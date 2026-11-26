module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChange
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem baseChange_loc {B A P P' Q Q' : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing P'] [CommRing Q]
    [CommRing Q'] [Algebra B A] [Algebra B P] [Algebra B P'] [Algebra B Q] [Algebra B Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower B A Q] [IsScalarTower B A Q']
    (i : P →+* P') (r : Q →+* Q') (t₁ : P →+* Q) (t : P' →+* Q') (c : P)
    (hi : ∀ b, i (algebraMap B P b) = algebraMap B P' b)
    (hr : ∀ a, r (algebraMap A Q a) = algebraMap A Q' a)
    (ht₁ : ∀ b, t₁ (algebraMap B P b) = algebraMap B Q b)
    (ht : ∀ b, t (algebraMap B P' b) = algebraMap B Q' b)
    (hcomm : ∀ x, t (i x) = r (t₁ x))
    (hP : letI := i.toAlgebra; IsLocalization.Away c P')
    (hQ : letI := r.toAlgebra; IsLocalization.Away (t₁ c) Q')
    (f₁ : P →ₗ[B] Q) (hf₁ : ∀ x, f₁ x = t₁ x) (f : P' →ₗ[B] Q') (hf : ∀ x, f x = t x)
    (h : IsBaseChange A f₁) : IsBaseChange A f := by
  letI a1 : Algebra P P' := i.toAlgebra
  letI a2 : Algebra Q Q' := r.toAlgebra
  letI a3 : Algebra P Q := t₁.toAlgebra
  letI a4 : Algebra P' Q' := t.toAlgebra
  letI a5 : Algebra P Q' := (t.comp i).toAlgebra
  haveI : IsScalarTower B P P' := .of_algebraMap_eq fun b => (hi b).symm
  haveI : IsScalarTower B P Q := .of_algebraMap_eq fun b => (ht₁ b).symm
  haveI : IsScalarTower B P' Q' := .of_algebraMap_eq fun b => (ht b).symm
  haveI : IsScalarTower B P Q' := .of_algebraMap_eq fun b => by
    change _ = t (i _)
    rw [hi, ht]
  haveI : IsScalarTower P P' Q' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower P Q Q' := .of_algebraMap_eq fun x => hcomm x
  haveI : IsScalarTower A Q Q' := .of_algebraMap_eq fun a => (hr a).symm
  haveI : IsScalarTower B Q Q' := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B A Q, IsScalarTower.algebraMap_apply B A Q']
    exact (hr _).symm
  have e1 : f₁ = (IsScalarTower.toAlgHom B P Q).toLinearMap := LinearMap.ext hf₁
  have p1 : Algebra.IsPushout B A P Q := ⟨by rw [← e1]; exact h⟩
  haveI p2 : Algebra.IsPushout B P A Q := p1.symm
  haveI : IsLocalization.Away c P' := hP
  have hQ' : IsLocalization (Algebra.algebraMapSubmonoid Q (Submonoid.powers c)) Q' := by
    have e : Algebra.algebraMapSubmonoid Q (Submonoid.powers c) = Submonoid.powers (t₁ c) := by
      simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      rfl
    rw [e]
    exact hQ
  have p3 : Algebra.IsPushout P Q P' Q' := (Algebra.isLocalization_iff_isPushout (Submonoid.powers c) P').1 hQ'
  have p4 : Algebra.IsPushout P P' Q Q' := p3.symm
  have p5 : Algebra.IsPushout B P' A Q' := (Algebra.IsPushout.comp_iff B P A Q).2 p4
  have e2 : f = (IsScalarTower.toAlgHom B P' Q').toLinearMap := LinearMap.ext hf
  rw [e2]
  exact p5.symm.out

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (e : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst e
  rfl

theorem mon_sum {ι : Type} {M : AddSubmonoid (Gam n d)} (s : Finset ι) (g : ι → Gam n d) (hg : ∀ j, g j ∈ M) :
    mon K (∑ j ∈ s, g j) (sum_mem fun j _ => hg j) = ∏ j ∈ s, mon K (g j) (hg j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact mon_congr (K := K) Finset.sum_empty _ M.zero_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha) _ _

def cE (S : Finset (Fin d)) (k : Fin d) : Gam n d := ∑ j ∈ S, ratE k j

theorem cE_mem (S : Finset (Fin d)) (k : Fin d) : cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  sum_mem fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cE_mem {S : Finset (Fin d)} (k : Fin d) : -cE S k ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have e : -cE S k = ∑ j ∈ S, (ratE j k : Gam n d) := by
    simp [cE, ratE, ← Finset.sum_neg_distrib]
  rw [e]
  exact sum_mem fun j hj => ratE_mem hj k

theorem one_le_cE {S : Finset (Fin d)} {k j : Fin d} (hj : j ∈ S) (hne : j ≠ k) :
    1 ≤ (cE S k : Gam n d) (Sum.inr j) := by
  have : (cE S k : Gam n d) (Sum.inr j) = 1 := by
    simp [cE, ratE, oneE, Finset.sum_apply, Pi.single_apply, hj, hne]
  exact this.ge

theorem exists_add_nsmul_mem {S : Finset (Fin d)} (k : Fin d) (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  have hc := cE_mem (n := n) S k
  have hN := (cone {k} : AddSubmonoid (Gam n d)).nsmul_mem hc
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · exact add_nonneg (hg.1 l) ((hN _).1 l)
  · have hne : j ≠ k := fun h => hj (h ▸ Finset.mem_singleton_self k)
    by_cases hjS : j ∈ S
    · have h1 := one_le_cE (n := n) hjS hne
      have h2 : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
        Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      show 0 ≤ g (Sum.inr j) + (∑ j, (g (Sum.inr j)).natAbs) • (cE S k : Gam n d) (Sum.inr j)
      rw [nsmul_eq_mul]
      have h3 : -g (Sum.inr j) ≤ ((g (Sum.inr j)).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h4 : ((g (Sum.inr j)).natAbs : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
      have h5 : (0 : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      nlinarith
    · exact add_nonneg (hg.2.1 j hjS) ((hN _).2.1 j hj)
  · rw [tdeg_add]
    exact add_nonneg hg.2.2 (hN _).2.2

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem theta_loc : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C S k hk θ₁ hθ₁ hu hbc
  have hsk : ({k} : Finset (Fin d)) ⊆ S := Finset.singleton_subset_iff.2 hk
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S := cone_mono hsk
  have hc := cE_mem (n := n) S k
  have hP := Away.isLocalization_away (K := K) hle (cE S k) hc (neg_cE_mem k)
    (fun g hg => exists_add_nsmul_mem k g hg)
  have hθc : θ₁ (mon K (cE S k) hc) = ∏ j ∈ S, C.u {k} k (Finset.mem_singleton_self k) j := by
    have e : mon K (cE S k) hc = ∏ j ∈ S, mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j) :=
      mon_sum S _ _
    rw [e, map_prod]
    exact Finset.prod_congr rfl fun j _ => hu j
  letI aP : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  letI aQ : Algebra (C.R {k}) (C.R S) := (C.res hsk).toRingHom.toAlgebra
  haveI hP' : IsLocalization.Away (mon K (cE S k) hc) (R0 K n d S) := hP
  have hQ : IsLocalization.Away (θ₁ (mon K (cE S k) hc)) (C.R S) := by
    rw [hθc]
    exact C.loc S k hk
  have hunit : IsUnit (((C.res hsk).toRingHom.comp θ₁.toRingHom) (mon K (cE S k) hc)) :=
    IsLocalization.Away.algebraMap_isUnit (S := C.R S) (θ₁ (mon K (cE S k) hc))
  let T : R0 K n d S →+* C.R S := IsLocalization.Away.lift (mon K (cE S k) hc) hunit
  have hT : ∀ x, T (incl hle x) = C.res hsk (θ₁ x) := fun x =>
    IsLocalization.Away.lift_eq (mon K (cE S k) hc) hunit x
  let θ : R0 K n d S →ₐ[K] C.R S :=
    { T with
      commutes' := fun r => by
        have e : algebraMap K (R0 K n d S) r = incl hle (algebraMap K (R0 K n d {k}) r) :=
          ((incl (K := K) hle).commutes r).symm
        change T _ = _
        rw [e, hT, θ₁.commutes, (C.res hsk).commutes] }
  have hθT : ∀ x, θ x = T x := fun _ => rfl
  have hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b) := fun b => by
    rw [hθT, ← incl_poly hsk, hT, hθ₁, res_toR]
  refine ⟨θ, hθ, ?_⟩
  exact baseChange_loc (A := Aa C) (Q := Rb C {k}) (Q' := Rb C S)
    (incl (K := K) hle).toRingHom (C.res hsk).toRingHom θ₁.toRingHom T (mon K (cE S k) hc)
    (fun b => incl_poly hsk b) (fun a => res_toR C hsk a) hθ₁ hθ hT hP hQ
    (thetaLin C θ₁ hθ₁) (fun _ => rfl) (thetaLin C θ hθ) (fun _ => rfl) hbc

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChangeStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_extend_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegOneEMul
set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis

def allE {n d : ℕ} : Gam n d := ∑ e, oneE e

theorem allE_mem {n d : ℕ} : (allE : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  unfold allE
  exact AddSubmonoid.sum_mem _ (fun e _ => oneE_mem ∅ e)

theorem allE_apply {n d : ℕ} (e : E n d) : (allE : Gam n d) e = 1 := by
  unfold allE
  rw [Finset.sum_apply]
  simp [oneE, Pi.single_apply]

theorem exists_add_mem {n d : ℕ} (g : Gam n d) :
    ∃ N : ℕ, g + N • allE ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ e, (g e).natAbs, ?_⟩
  have hnn : ∀ e, 0 ≤ (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e := by
    intro e
    have h1 : (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e
        = g e + ((∑ e, (g e).natAbs : ℕ) : ℤ) := by
      change g e + (∑ e, (g e).natAbs) • (allE : Gam n d) e = _
      rw [allE_apply, nsmul_one]
    have h2 : (g e).natAbs ≤ ∑ e, (g e).natAbs :=
      Finset.single_le_sum (f := fun e => (g e).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
    have h3 : ((g e).natAbs : ℤ) ≤ ((∑ e, (g e).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
    rw [h1]
    have h4 := Int.natCast_natAbs (g e)
    have h5 := neg_abs_le (g e)
    linarith
  have key := PolyBij.coe_mem_cone (n := n) (d := d)
    (Finsupp.equivFunOnFinite.symm fun e => ((g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e).toNat)
  convert key using 2
  rename_i e
  exact (Int.toNat_of_nonneg (hnn e)).symm

theorem monL_neg_oneE_mul {K : Type} [Field K] {n d : ℕ} (e : E n d) : monL K (-oneE e) * monL K (oneE e) = 1 := by
  rw [monL, monL, mon_mul]
  change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
  congr 1
  exact Subtype.ext (neg_add_cancel (oneE e))

theorem exists_basis_dl : ∀ {K : Type} [Field K] {n d : ℕ},
    ∃ b : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K], ∀ e, b e = dl e := by
  intro K _ n d
  have hle : (cone ∅ : AddSubmonoid (Gam n d)) ≤ ⊤ := le_top
  let φ : MvPolynomial (E n d) K →ₐ[K] Lr K n d := (incl (K := K) hle).comp (poly n K ∅)
  letI : Algebra (MvPolynomial (E n d) K) (Lr K n d) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (E n d) K) (Lr K n d) := IsScalarTower.of_algHom φ
  let s0 : MvPolynomial (E n d) K := (PolyBij.polyEquiv K).symm (mon K (allE : Gam n d) allE_mem)
  have hpe : ∀ a, poly n K ∅ ((PolyBij.polyEquiv (n := n) (d := d) K).symm a) = a := by
    intro a
    rw [PolyBij.poly_eq_polyEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  have e1 : φ s0 = incl (K := K) hle (mon K (allE : Gam n d) allE_mem) := by
    change incl (K := K) hle (poly n K ∅ s0) = _
    rw [hpe]
  have hmul : φ s0 * mon K (-(allE : Gam n d)) (AddSubmonoid.mem_top _) = 1 := by
    rw [e1, incl_mon, mon_mul]
    change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
    congr 1
    exact Subtype.ext (add_neg_cancel (allE : Gam n d))
  have hunit : IsUnit (φ s0) := ⟨⟨φ s0, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hinj : Function.Injective φ :=
    (Away.incl_injective (K := K) hle).comp (PolyBij.poly_bijective (K := K) (n := n) (d := d)).1
  haveI : IsLocalization (Submonoid.powers s0) (Lr K n d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [← hk]
      change IsUnit (φ (s0 ^ k))
      rw [map_pow]
      exact hunit.pow k
    · intro z
      obtain ⟨N, a, ha⟩ := Away.exists_mul_pow_eq_incl (K := K) hle (allE : Gam n d) allE_mem
        (fun g _ => exists_add_mem g) z
      refine ⟨((PolyBij.polyEquiv K).symm a, ⟨s0 ^ N, N, rfl⟩), ?_⟩
      change z * φ (s0 ^ N) = φ ((PolyBij.polyEquiv K).symm a)
      have e2 : φ ((PolyBij.polyEquiv K).symm a) = incl (K := K) hle a := by
        change incl (K := K) hle (poly n K ∅ _) = _
        rw [hpe]
      rw [map_pow, e1, e2, ← map_pow]
      exact ha
    · intro x y hxy
      have hxy' : φ x = φ y := hxy
      exact ⟨1, by rw [hinj hxy']⟩
  let b0 := (KaehlerDifferential.mvPolynomialBasis K (E n d)).ofIsLocalizedModule (Lr K n d)
    (Submonoid.powers s0) (KaehlerDifferential.map K K (MvPolynomial (E n d) K) (Lr K n d))
  let w : E n d → (Lr K n d)ˣ := fun e =>
    ⟨monL K (-oneE e), monL K (oneE e), monL_neg_oneE_mul e, by rw [mul_comm]; exact monL_neg_oneE_mul e⟩
  refine ⟨b0.unitsSMul w, fun e => ?_⟩
  have e4 : KaehlerDifferential.mvPolynomialBasis K (E n d) e
      = KaehlerDifferential.D K (MvPolynomial (E n d) K) (MvPolynomial.X e) :=
    Module.Basis.apply_eq_iff.mpr (by rw [KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.unitsSMul_apply, Module.Basis.ofIsLocalizedModule_apply, e4, KaehlerDifferential.map_D]
  have e3 : φ (MvPolynomial.X e) = monL K (oneE e) := by
    change incl (K := K) hle (poly n K ∅ (MvPolynomial.X e)) = _
    rw [poly_X, incl_mon]
    rfl
  change monL K (-oneE e) • KaehlerDifferential.D K (Lr K n d) (φ (MvPolynomial.X e)) = dl e
  rw [e3]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasis
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}

def topEquiv : (⊤ : AddSubmonoid (Gam n d)) ≃ Gam n d := Equiv.Set.univ _

def lrBasis : Module.Basis (Gam n d) K (Lr K n d) :=
  (Module.Basis.ofRepr (AddMonoidAlgebra.coeffLinearEquiv K)).reindex topEquiv

theorem lrBasis_apply (g : Gam n d) : lrBasis (K := K) g = monL K g := by
  rw [lrBasis, Module.Basis.reindex_apply, Module.Basis.coe_ofRepr]
  rfl

def setEquiv (a : ℕ) : {D : Finset (E n d) // D.card = a} ≃ Set.powersetCard (Fin (n + d)) a where
  toFun D := ⟨D.1.map finSumFinEquiv.toEmbedding, by simpa using D.2⟩
  invFun s := ⟨s.1.map finSumFinEquiv.symm.toEmbedding, by simp⟩
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

theorem wedge_basis (bΩ : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K]) (h : ∀ e, bΩ e = dl e) (a : ℕ) :
    ∃ c : Module.Basis {D : Finset (E n d) // D.card = a} (Lr K n d) (Om K (Lr K n d) a),
      ∀ D, c D = wedge (K := K) (enumD D) := by
  refine ⟨((bΩ.reindex finSumFinEquiv).exteriorPower a).reindex (setEquiv a).symm, fun D => ?_⟩
  rw [Module.Basis.reindex_apply, exteriorPower.basis_apply]
  simp only [Equiv.symm_symm]
  unfold exteriorPower.ιMulti_family wedge
  congr 1
  funext i
  simp [Module.Basis.reindex_apply, h, enumD, setEquiv, Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem monW_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  intro K _ n d a
  obtain ⟨bΩ, h⟩ := GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis.exists_basis_dl (K := K) (n := n) (d := d)
  obtain ⟨c, hc⟩ := wedge_basis bΩ h a
  refine ⟨lrBasis.smulTower c, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, lrBasis_apply, hc]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasisStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_forms_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRange
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTpow

open HomogeneousLocalization

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

theorem evV_awayMap (i : X ⟶ PSpace K N) {f g x : MvPolynomial (Fin (N + 1)) K} {n : ℕ}
    (hg : g ∈ grK K N n) (hx : x = f * g) (V : X.Opens)
    (hf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hxV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x)
    (a : Away (grK K N) f) :
    evV i x V hxV (awayMap (grK K N) hg hx a) = evV i f V hf a := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (grK K N) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (i.appLE _ V hxV).hom ((Proj.awayToSection (grK K N) x).hom (awayMap (grK K N) hg hx a)) = _
  rw [h]
  change ((_ ≫ i.appLE _ V hxV).hom) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem prod_pow_mem {n e p : ℕ} (y : Fin n → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (α : Fin n → ℕ) (hp : (∑ j, α j) * e = p) :
    ∏ j, y j ^ α j ∈ grK K N p := by
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun j => y j ^ α j) (fun j => e * α j)
    (fun j _ => (hy j).pow (α j))
  rw [MvPolynomial.mem_homogeneousSubmodule, ← hp, mul_comm, Finset.mul_sum]
  exact h

theorem prod_mk_pow {n e c : ℕ} {g : MvPolynomial (Fin (N + 1)) K} (hg : g ∈ grK K N e)
    (y : Fin n → MvPolynomial (Fin (N + 1)) K) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (α : Fin n → ℕ)
    (hc : ∑ j, α j = c) (hm : ∏ j, y j ^ α j ∈ grK K N (c • e)) :
    ∏ j, Away.mk (grK K N) hg 1 (y j) (h1 j) ^ α j = Away.mk (grK K N) hg c (∏ j, y j ^ α j) hm := by
  have hpow : ∀ k : ℕ, g ^ k ∈ Submonoid.powers g := fun k => ⟨k, rfl⟩
  let v : Localization (Submonoid.powers g) := Localization.mk 1 ⟨g, 1, pow_one g⟩
  have hv : ∀ k : ℕ, v ^ k = Localization.mk 1 ⟨g ^ k, hpow k⟩ := by
    intro k
    induction k with
    | zero => simpa using Localization.mk_one.symm
    | succ k ih =>
      rw [pow_succ, ih, Localization.mk_mul]
      simp [pow_succ]
  have key : ∀ (k : ℕ) (x) (hx : x ∈ grK K N (k • e)),
      (Away.mk (grK K N) hg k x hx).val = algebraMap _ _ x * v ^ k := by
    intro k x hx
    rw [Away.val_mk, hv, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    simp
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp_rw [map_pow, HomogeneousLocalization.algebraMap_apply, key, pow_one, mul_pow,
    Finset.prod_mul_distrib, map_prod, map_pow, Finset.prod_pow_eq_pow_sum, hc]

theorem exists_shift {n : ℕ} (S : Finset (Fin n)) (v : Fin n → ℤ) (h : ∀ j, j ∉ S → 0 ≤ v j) :
    ∃ (r : ℕ) (α : Fin n → ℕ), ∀ j, (α j : ℤ) = v j + if j ∈ S then (r : ℤ) else 0 := by
  refine ⟨∑ j, (v j).natAbs, fun j => (v j + if j ∈ S then ((∑ j, (v j).natAbs : ℕ) : ℤ) else 0).toNat, fun j => ?_⟩
  refine Int.toNat_of_nonneg ?_
  by_cases hj : j ∈ S
  · have h1 : (v j).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hj, if_true]
    omega
  · simpa [hj] using h j hj

theorem cross_mul {c r e₁ e₂ : ℕ} {f g a : MvPolynomial (Fin (N + 1)) K}
    (hf : f ∈ grK K N e₁) (hg : g ∈ grK K N e₂) (ha : a ∈ grK K N (r • e₁)) (ha' : a ∈ grK K N (c • e₂))
    (hF : f ^ r ∈ grK K N (c • e₂)) :
    awayMap (grK K N) hg (mul_comm g f) (Away.mk (grK K N) hf r a ha) *
      awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c (f ^ r) hF) =
    awayMap (grK K N) hf (rfl : g * f = g * f) (Away.mk (grK K N) hg c a ha') := by
  simp only [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  simp only [Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
  ring

theorem core {d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens) (h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (hy0 : y 0 ∈ grK K N e) (h1 : ∀ j, y j ∈ grK K N (1 • e)) (r : ℕ) (α : Fin (d + 1) → ℕ)
    (hα : ∑ j, α j = r * S.card)
    (ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e))) :
    evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
        ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ (if j ∈ S then r else 0) =
      ∏ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) ^ α j := by
  have hP : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * yS y S) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h0 hS
  have hβ : ∑ j, (if j ∈ S then r else 0) = r * S.card := by
    simp [Finset.sum_ite_mem, mul_comm]
  have ha' : ∏ j, y j ^ α j ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy α (by rw [hα, smul_eq_mul])
  have hF' : ∏ j, y j ^ (if j ∈ S then r else 0) ∈ grK K N ((r * S.card) • e) :=
    prod_pow_mem y hy _ (by rw [hβ, smul_eq_mul])
  have hFeq : ∏ j, y j ^ (if j ∈ S then r else 0) = yS y S ^ r := by
    simp [yS, pow_ite, Finset.prod_ite_mem, Finset.prod_pow]
  have hF : yS y S ^ r ∈ grK K N ((r * S.card) • e) := hFeq ▸ hF'
  simp_rw [← map_pow, ← map_prod]
  rw [prod_mk_pow hy0 y h1 α hα ha', prod_mk_pow hy0 y h1 _ hβ hF']
  simp only [hFeq]
  rw [← evV_awayMap i hy0 (mul_comm (y 0) (yS y S)) V hS hP,
    ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← evV_awayMap i (yS_mem y hy S) rfl V h0 hP, ← map_mul,
    cross_mul (yS_mem y hy S) hy0 ha ha' hF]

theorem tpow_mem_range {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) : 0 < e →
    ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
      (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S,
      tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  intro _ S hS ht m hm
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have h1 : ∀ j, y j ∈ grK K N (1 • e) := fun j => by
    simpa using (MvPolynomial.mem_homogeneousSubmodule e (y j)).2 (hy j)
  let n : Fin (d + 1) → ℤ := Fin.cons (-∑ k, m k) m
  have hn0 : n 0 = -∑ k, m k := rfl
  have hns : ∀ k : Fin d, n k.succ = m k := fun _ => rfl
  have hn : ∀ j, j ∉ S → 0 ≤ n j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj
      have := hm.2 hj
      rw [hn0]
      omega
    · intro hj
      rw [hns]
      exact hm.1 k hj
  obtain ⟨r, α, hα⟩ := exists_shift S n hn
  have hsum : ∑ j, n j = 0 := by
    rw [Fin.sum_univ_succ, hn0]
    simp only [hns]
    ring
  have hαs : ∑ j, α j = r * S.card := by
    have : ((∑ j, α j : ℕ) : ℤ) = ((r * S.card : ℕ) : ℤ) := by
      push_cast
      simp_rw [hα]
      rw [Finset.sum_add_distrib, hsum]
      simp [Finset.sum_ite_mem, mul_comm]
    exact_mod_cast this
  have ha : ∏ j, y j ^ α j ∈ grK K N (r • (S.card * e)) :=
    prod_pow_mem y hy α (by rw [hαs, smul_eq_mul, mul_assoc])
  refine ⟨Away.mk (grK K N) (yS_mem y hy S) r _ ha, ?_⟩
  have hc := core i y hy V h0 S hS hy0 h1 r α hαs ha
  let T : Fin (d + 1) → (Γ(X, V))ˣ := Fin.cons 1 (fun k => (ht k).unit)
  have hT0 : T 0 = 1 := rfl
  have hTs : ∀ k : Fin d, T k.succ = (ht k).unit := fun _ => rfl
  have hT : ∀ j, evV i (y 0) V h0 (Away.mk (grK K N) hy0 1 (y j) (h1 j)) = (T j : Γ(X, V)) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · have : Away.mk (grK K N) hy0 1 (y 0) (h1 0) = 1 := by
        apply HomogeneousLocalization.val_injective
        rw [Away.val_mk, HomogeneousLocalization.val_one]
        simpa using Localization.mk_self (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))
      rw [this, map_one, hT0, Units.val_one]
    · rw [hTs, IsUnit.unit_spec]
      rfl
  simp only [hT] at hc
  have hU : ∏ k, (ht k).unit ^ m k = ∏ j, T j ^ n j := by
    rw [Fin.prod_univ_succ, hT0, one_zpow, one_mul]
    simp only [hTs, hns]
  have hA : ∏ j, T j ^ α j = (∏ j, T j ^ n j) * ∏ j, T j ^ (if j ∈ S then r else 0) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, hα]
    split_ifs <;> simp
  have hc' : evV i (yS y S) V hS (Away.mk (grK K N) (yS_mem y hy S) r _ ha) *
      ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) =
      ((∏ j, T j ^ n j : (Γ(X, V))ˣ) : Γ(X, V)) * ((∏ j, T j ^ (if j ∈ S then r else 0) : (Γ(X, V))ˣ) : Γ(X, V)) := by
    rw [← Units.val_mul, ← hA]
    simpa [Units.coe_prod] using hc
  have := (Units.mul_left_inj _).1 hc'
  rw [this, tpow, hU]

end GlobalTheory.CompanionTheory.GeoTpow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRangeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_monomial_mem_range : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S, tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  first | exact @GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | exact GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | (intros; apply GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChange
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4


open TensorProduct in
theorem isBaseChange_of_presentation {B A P Q ι : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing Q]
    [Algebra B A] [Algebra B P] [Algebra A Q] [Algebra B Q] [IsScalarTower B A Q]
    (θ : P →ₐ[B] Q) (u : ι → Q) (v : ι → P) (k : ι) (b : ι → B)
    (hv : ∀ j, θ (v j) = u j)
    (hsurj : Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := Q) u))
    (hker : RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j)))
    (hvk : v k = 1) (hb : ∀ j, algebraMap B P (b j) = algebraMap B P (b k) * v j)
    (hadj : Algebra.adjoin B (Set.range v) = ⊤) :
    IsBaseChange A θ.toLinearMap := by
  let f : MvPolynomial ι A →ₐ[A] Q := MvPolynomial.aeval u
  let g : MvPolynomial ι A →ₐ[A] A ⊗[B] P := MvPolynomial.aeval fun j => (1 : A) ⊗ₜ[B] v j
  have key : ∀ c : B, (algebraMap B A c) ⊗ₜ[B] (1 : P) = (1 : A) ⊗ₜ[B] algebraMap B P c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom := by
    change RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom ≤ _
    rw [hker]
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨j, rfl⟩)
    · change g _ = 0
      simp [g, hvk, Algebra.TensorProduct.one_def]
    · change g _ = 0
      have e : g (MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j) =
          (algebraMap B A (b j)) ⊗ₜ[B] (1 : P) - ((algebraMap B A (b k)) ⊗ₜ[B] (1 : P)) * ((1 : A) ⊗ₜ[B] v j) := by
        simp [g, Algebra.TensorProduct.algebraMap_apply]
      rw [e, key, key, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb, sub_self]
  have hmem : ∀ p ∈ RingHom.ker f, g p = 0 := fun p hp => hle hp
  let h : Q →ₐ[A] A ⊗[B] P :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g hmem).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hh : ∀ p, h (f p) = g p := by
    intro p
    have e : (Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g hmem ((Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p)) = _
    rw [e]
    rfl
  let L : A ⊗[B] P →ₐ[A] Q := Algebra.TensorProduct.lift (Algebra.ofId A Q) θ fun _ _ => Commute.all _ _
  have hL1 : ∀ y, L ((1 : A) ⊗ₜ[B] y) = θ y := by
    intro y
    simp [L]
  have hLg : L.comp g = f := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [g, f, hL1, hv]
  have hLh : L.comp h = AlgHom.id A Q := by
    refine AlgHom.ext fun r => ?_
    obtain ⟨p, rfl⟩ := hsurj r
    change L (h (f p)) = f p
    rw [hh]
    exact DFunLike.congr_fun hLg p
  have hhL : h.comp L = AlgHom.id A (A ⊗[B] P) := by
    apply Algebra.TensorProduct.ext
    · refine AlgHom.ext fun a => ?_
      have := (h.comp L).commutes a
      simpa [Algebra.TensorProduct.algebraMap_apply] using this
    · refine AlgHom.ext_of_adjoin_eq_top hadj ?_
      rintro _ ⟨j, rfl⟩
      change h (L ((1 : A) ⊗ₜ[B] v j)) = (1 : A) ⊗ₜ[B] v j
      have e : u j = f (MvPolynomial.X j) := by simp [f]
      rw [hL1, hv, e, hh]
      simp [g]
  let eq : A ⊗[B] P ≃ₐ[A] Q := AlgEquiv.ofAlgHom L h hLh hhL
  exact IsBaseChange.of_equiv eq.toLinearEquiv fun x => hL1 x

theorem mon_eq_one {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g : Gam n d} (hg : g ∈ M) (h : g = 0) :
    mon K g hg = 1 := by
  subst h
  rfl

theorem mon_congr {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (hg : g ∈ M) (hg' : g' ∈ M)
    (h : g = g') : mon K g hg = mon K g' hg' := by
  subst h
  rfl

theorem theta_one {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d) :
    ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)),
      (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧
        IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  have hk : k ∈ ({k} : Finset (Fin d)) := Finset.mem_singleton_self k
  let u : Fin d → Rb C {k} := C.u {k} k hk
  have hphi : ∀ j, algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j)) = C.t j := by
    intro j
    change phi C _ = _
    simp [phi]
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) := C.chart_surj k
  have hker : RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j))) -
          MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr k))) * MvPolynomial.X j)) := by
    simp only [hphi]
    exact C.chart_ker k
  have huk : u k = 1 := by
    have hm : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) (Aa C)) ∈
        RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have h0 : (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) (MvPolynomial.X k - 1) = 0 := hm
    simpa [sub_eq_zero] using h0
  have htu : ∀ j, toR C {k} (C.t j) = toR C {k} (C.t k) * C.u {k} k hk j := fun j => C.t_eq {k} k hk j
  let w : E n d → C.R {k} := Sum.elim (fun l => toR C {k} (C.x l))
    (fun j => if j = k then toR C {k} (C.t k) else C.u {k} k hk j)
  let Ψ : Bp K n d ≃ₐ[K] R0 K n d {k} := AlgEquiv.ofBijective _ (ChartBij.chart_bijective (K := K) (n := n) k)
  let θ : R0 K n d {k} →ₐ[K] C.R {k} := (MvPolynomial.aeval w).comp Ψ.symm.toAlgHom
  have hθw : ∀ e, θ (mon K (wv k e) (wv_mem hk e)) = w e := by
    intro e
    have h1 : mon K (wv k e) (wv_mem hk e) = Ψ (MvPolynomial.X e) := by simp [Ψ]
    change MvPolynomial.aeval w (Ψ.symm _) = _
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
  have hθr : ∀ j, θ (mon K (ratE k j) (ratE_mem hk j)) = C.u {k} k hk j := by
    intro j
    by_cases h : j = k
    · subst h
      rw [mon_eq_one _ (by simp [ratE]), map_one]
      exact huk.symm
    · have h1 := hθw (Sum.inr j)
      have h2 : wv k (Sum.inr j) = (ratE k j : Gam n d) := by simp [wv, h]
      rw [mon_congr _ (ratE_mem hk j) h2] at h1
      simpa [w, h] using h1
  have hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b) := by
    have e : θ.comp (poly n K {k}) = (toR C {k}).comp (phi C) := by
      apply MvPolynomial.algHom_ext
      rintro (l | j)
      · have h1 := hθw (Sum.inl l)
        simpa [poly_X, phi, w, wv] using h1
      · have h1 := hθw (Sum.inr k)
        have h2 : wv k (Sum.inr k) = (oneE (Sum.inr k) : Gam n d) := by simp [wv]
        rw [mon_congr _ (oneE_mem {k} _) h2] at h1
        have h3 : mon K (oneE (Sum.inr j) : Gam n d) (oneE_mem {k} _) =
            mon K (oneE (Sum.inr k)) (oneE_mem {k} _) * mon K (ratE k j) (ratE_mem hk j) := by
          rw [mon_mul]
          exact mon_congr _ _ (by simp [ratE])
        simp only [AlgHom.comp_apply, poly_X, phi, MvPolynomial.aeval_X, Sum.elim_inr]
        rw [h3, map_mul, h1, hθr, htu j]
        simp [w]
    exact fun b => DFunLike.congr_fun e b
  refine ⟨θ, hθ, hθr, ?_⟩
  let θ' : R0 K n d {k} →ₐ[Bp K n d] Rb C {k} := { θ.toRingHom with commutes' := fun b => hθ b }
  have hadj : Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := (ChartBij.chart_bijective (K := K) (n := n) k).2 y
    induction p using MvPolynomial.induction_on with
    | C c =>
      have : MvPolynomial.aeval (fun e : E n d => mon K (wv k e) (wv_mem hk e)) (MvPolynomial.C c : Bp K n d) =
          algebraMap (Bp K n d) (R0 K n d {k}) (MvPolynomial.C c) := by
        rw [algebraMap_cone_ring]
        simp [poly]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hp hq
    | mul_X p e hp =>
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      rw [MvPolynomial.aeval_X]
      have hpoly : ∀ e' : E n d, mon K (oneE e') (oneE_mem {k} e') ∈
          Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) := by
        intro e'
        rw [← poly_X, ← algebraMap_cone_ring]
        exact Subalgebra.algebraMap_mem _ _
      rcases e with l | j
      · exact hpoly _
      · by_cases h : j = k
        · subst h
          rw [mon_congr _ (oneE_mem {j} _) (by simp [wv] : wv j (Sum.inr j) = (oneE (Sum.inr j) : Gam n d))]
          exact hpoly _
        · rw [mon_congr _ (ratE_mem hk j) (by simp [wv, h] : wv k (Sum.inr j) = (ratE k j : Gam n d))]
          exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hbase := isBaseChange_of_presentation (B := Bp K n d) (A := Aa C) (P := R0 K n d {k}) (Q := Rb C {k}) θ' u
    (fun j => mon K (ratE k j) (ratE_mem hk j)) k (fun j => MvPolynomial.X (Sum.inr j)) hθr hsurj hker
    (mon_eq_one _ (by simp [ratE]))
    (fun j => by
      simp only [algebraMap_cone_ring, poly_X]
      rw [mon_mul]
      exact mon_congr _ _ (by simp [ratE]))
    hadj
  exact hbase

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChangeStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_singleton_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d), ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧ IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one <;> assumption)
end
end
