module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

open scoped SchwartzMap Classical

set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat

open GroundTheory.Automorphic.Adele2 NumberField.mixedEmbedding

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def mulVecCLE (M : GL ι (mixedSpace k)) : (ι → mixedSpace k) ≃L[ℝ] (ι → mixedSpace k) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ (M : Matrix ι ι (mixedSpace k)) *ᵥ u
      invFun := fun u ↦ ((M⁻¹ : GL ι (mixedSpace k)) : Matrix ι ι (mixedSpace k)) *ᵥ u
      map_add' := fun u v ↦ mulVec_add _ u v
      map_smul' := fun c u ↦ mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun u ↦ by
        simp only [mulVec_mulVec, Units.mul_inv, one_mulVec] }

theorem mulVecCLE_apply (M : GL ι (mixedSpace k)) (u : ι → mixedSpace k) :
    mulVecCLE M u = (M : Matrix ι ι (mixedSpace k)) *ᵥ u := rfl

def mulVecHomeo (M : GL ι 𝔸ᶠ[k]) : (ι → 𝔸ᶠ[k]) ≃ₜ (ι → 𝔸ᶠ[k]) where
  toFun u := (M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  invFun u := ((M⁻¹ : GL ι 𝔸ᶠ[k]) : Matrix ι ι 𝔸ᶠ[k]) *ᵥ u
  left_inv u := by simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv u := by simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem comp_mulVec_mem_finiteSchwartzBruhatPi (M : GL ι 𝔸ᶠ[k]) {g : (ι → 𝔸ᶠ[k]) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi k) :
    (fun z ↦ g ((M : Matrix ι ι 𝔸ᶠ[k]) *ᵥ z)) ∈ finiteSchwartzBruhatPi k := by
  obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi k).1 hg
  exact (mem_finiteSchwartzBruhatPi k).2
    ⟨h1.comp_continuous (mulVecHomeo M).continuous,
      h2.comp_isClosedEmbedding (mulVecHomeo M).isClosedEmbedding⟩

theorem infPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    infPartPi (A *ᵥ x) = A.map infRingHom *ᵥ infPartPi x := by
  funext i
  exact RingHom.map_mulVec infRingHom A x i

theorem finPartPi_mulVec (A : Matrix ι ι 𝔸[k]) (x : ι → 𝔸[k]) :
    finPartPi (A *ᵥ x) = A.map finRingHom *ᵥ finPartPi x := by
  funext i
  exact RingHom.map_mulVec finRingHom A x i

theorem ltr_schwartzBruhatTensorPi (A : GL ι 𝔸[k]) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (g : (ι → 𝔸ᶠ[k]) → ℂ) :
    ltr A (schwartzBruhatTensorPi φ g) =
      schwartzBruhatTensorPi
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mulVecCLE (Matrix.GeneralLinearGroup.map infRingHom A)) φ)
        (fun z ↦ g ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) *ᵥ z)) := by
  funext x
  have h1 : ((Matrix.GeneralLinearGroup.map infRingHom A : GL ι (mixedSpace k)) :
      Matrix ι ι (mixedSpace k)) = (A : Matrix ι ι 𝔸[k]).map infRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : ((Matrix.GeneralLinearGroup.map finRingHom A : GL ι 𝔸ᶠ[k]) :
      Matrix ι ι 𝔸ᶠ[k]) = (A : Matrix ι ι 𝔸[k]).map finRingHom := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  simp only [ltr, schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, mulVecCLE_apply, h1, h2, infPartPi_mulVec, finPartPi_mulVec]

theorem ltr_mem {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) :
    ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [ltr_schwartzBruhatTensorPi]
    exact schwartzBruhatTensorPi_mem _ (comp_mulVec_mem_finiteSchwartzBruhatPi _ hg)
  | zero => exact zero_mem _
  | add G H _ _ ihG ihH => exact add_mem ihG ihH
  | smul a G _ ih => exact Submodule.smul_mem _ a ih

end GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrime
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.TensOne

open TensorProduct

section Generic

variable {R S W C : Type} [CommRing R] [CommRing S] [CommRing W] [CommRing C]
  [Algebra R S] [Algebra R W] [Algebra R C]

theorem tmul_mul_natCast_mem (p : ℕ) (e : S) (x : W) :
    (e * (p : S)) ⊗ₜ[R] x ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm
  have : (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem tmul_natCast_mul_mem (p : ℕ) (e : S) (x : W) :
    e ⊗ₜ[R] (x * (p : W)) ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W) :=
    (map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm
  have : e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gsum (d : ℕ → S) (w : ℕ →₀ W) : S ⊗[R] W := w.sum fun k x => d k ⊗ₜ[R] x

theorem gsum_add (d : ℕ → S) (w w' : ℕ →₀ W) :
    (gsum d (w + w') : S ⊗[R] W) = gsum d w + gsum d w' :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _

theorem exists_gsum (p : ℕ) (d : ℕ → S)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (z : S ⊗[R] W) : ∃ w : ℕ →₀ W, z - gsum d w ∈ Ideal.span {(p : S ⊗[R] W)} := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨s, c, hc⟩ := hsurj a
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩
    have h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) =
        (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x := by
      rw [gsum, ← Finsupp.sum_finsetSum_index (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.sub_tmul, ← he]
    exact tmul_mul_natCast_mem p e x
  | add x y hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    refine ⟨w + w', ?_⟩
    have : x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w') := by
      rw [gsum_add]; ring
    rw [this]
    exact add_mem hw hw'

theorem generic (p : ℕ) (d : ℕ → S) (r0 : R) (f : S →ₐ[R] C) (g : W →ₐ[R] C)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (hv : ∀ k, algebraMap R S r0 * d k ∈ Ideal.span {(p : S)})
    (hK : ∀ (s : Finset ℕ) (w : ℕ → W), ∑ k ∈ s, f (d k) * g (w k) = 0 →
      ∀ k ∈ s, w k ∈ Ideal.span {algebraMap R W r0, (p : W)})
    (hC : (p : C) = 0) (z : S ⊗[R] W)
    (hz : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = 0) :
    z ∈ Ideal.span {(p : S ⊗[R] W)} := by
  obtain ⟨w, hw⟩ := exists_gsum p d hsurj z
  have hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hw
    rw [← hy, map_mul, map_natCast, hC, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum] at hL
  have hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0 := by
    rw [← hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  have hk := hK _ _ hsum
  have hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)} := by
    refine Ideal.sum_mem _ fun k hks => ?_
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hk k hks)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hv k)
    have h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u := by
      rw [he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    change d k ⊗ₜ[R] (w k) ∈ _
    rw [← huv, TensorProduct.tmul_add, h1]
    exact add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)
  have := add_mem hw hG
  rwa [sub_add_cancel] at this

end Generic

section Specific

variable {l : ℕ} [Fact l.Prime]

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.1
  tf := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.2

theorem isBase_base : IsBase l (base (l := l)) := Function.bijective_id

def d (k : ℕ) : Acris l := AdicCompletion.of _ _ (ACris.dpowZero (xi0_mem (l := l)) k)

theorem cris_d (A : PAlg l) (n k : ℕ) : A.cris n (d k) = A.dxi n k := by
  rw [d, cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)

theorem sW_base (x : Ainf l) : (base (l := l)).sW x = x := wmap_id x

theorem cris_teich (a : Ob l) :
    (base (l := l)).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l a)) =
      (base (l := l)).aTo1 a := by
  have h1 := (base (l := l)).aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h1
  have h2 := (base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)
  rw [sW_base] at h2
  rw [h1]
  exact h2

theorem mem_of_cris (a : Acris l) (h : (base (l := l)).cris 1 a = 0) : a ∈ Ideal.span {(l : Acris l)} := by
  have := (RingHom.mem_ker).2 h
  rwa [((GlobalTheory.T.period_ring_comparison_of_base base isBase_base).2 1).2, pow_one] at this

theorem hsurj (a : Acris l) : ∃ (s : Finset ℕ) (c : ℕ → Ainf l),
    a - ∑ k ∈ s, algebraMap (Ainf l) (Acris l) (c k) * d (l * k) ∈ Ideal.span {(l : Acris l)} := by
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).1 ((base (l := l)).cris 1 a)
  refine ⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩
  have e : (base (l := l)).expand c =
      ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, ← hc, e, sub_eq_zero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cris_teich, cris_d]

def r0 : Ainf l := WittVector.teichmuller l (pFlat l ^ l)

theorem hv (k : ℕ) : algebraMap (Ainf l) (Acris l) (r0 (l := l)) * d k ∈ Ideal.span {(l : Acris l)} := by
  refine mem_of_cris _ ?_
  rw [map_mul, r0, cris_teich, cris_d]
  exact (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).2.2.2 k

theorem hK (A : PAlg l) (s : Finset ℕ) (w : ℕ → A.W)
    (h : ∑ k ∈ s, A.cris 1 (d (l * k)) * A.toAcr 1 (w k) = 0) (k : ℕ) (hks : k ∈ s) :
    w k ∈ Ideal.span {algebraMap (Ainf l) A.W r0, (l : A.W)} := by
  have hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0 := by
    rw [expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]
  have hk := (GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A _).1 hexp k
  rw [Finsupp.indicator_of_mem hks] at hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hk
  have hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l) := by
    change A.sW _ = _
    rw [r0, sW, WittVector.map_teichmuller, map_pow]
    rfl
  have hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hr]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [hb, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)
  exact Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩

theorem natCast_acr (A : PAlg l) : (l : A.Acr 1) = 0 := by
  have := A.pow_l_acr 1
  rwa [pow_one] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W),
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 →
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  intro l _ A z hz
  exact generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0
    (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1))
    hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz

end Specific

end GlobalTheory.CompanionTheory.TensOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrimeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_lift_kernel_mod_prime : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W), Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 → z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  first | exact @GlobalTheory.CompanionTheory.TensOne.main | exact GlobalTheory.CompanionTheory.TensOne.main | (intros; apply GlobalTheory.CompanionTheory.TensOne.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntSmul
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.He2M1

theorem thetaC_smul {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (c • F) h = c * thetaC F h := by
  unfold thetaC
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem thetaCInt_smul : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}), thetaCInt w (c • F) ω t = c * thetaCInt w F ω t := by
  intro k _ _ ι _ _ w c F ω t
  unfold thetaCInt
  simp only [thetaC_smul, mul_assoc]
  exact integral_const_mul c _

end GlobalTheory.CompanionTheory.He2M1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntNeg
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

theorem thetaC_neg {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (fun x ↦ F (-x)) h = thetaC F h := by
  unfold thetaC
  rw [← (Equiv.neg (ι → k)).tsum_eq (fun ξ => F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))]
  refine tsum_congr fun ξ => ?_
  have hr : ratV (-ξ) = -ratV ξ := by
    funext i
    simp [ratV]
  simp only [Equiv.neg_apply, hr, Matrix.mulVec_neg]

theorem thetaCInt_neg : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k),
    thetaCInt w (fun x ↦ F (-x)) ω = thetaCInt w F ω := by
  intro k _ _ ι _ _ w F ω
  funext t
  unfold thetaCInt
  simp only [thetaC_neg]

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolCharOneEq
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfForallInM
noncomputable section
open NumberField IsDedekindDomain Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.RgEis.InMTopPf

variable {k : Type} [Field k] [NumberField k]

theorem natCast_isUnit (M : ℕ) (hM : M ≠ 0) : IsUnit (M : FiniteAdeleRing (𝓞 k) k) := by
  have : (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k) := by simp
  rw [this]
  exact (IsUnit.mk0 _ (by exact_mod_cast hM)).map _

theorem inM_iff (M : ℕ) (hM : M ≠ 0) (x : FiniteAdeleRing (𝓞 k) k) :
    InM M x ↔ (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
      FiniteAdeleRing (𝓞 k) k) * x ∈ OH k := by
  set u := (natCast_isUnit (k := k) M hM).unit
  have hu : (u : FiniteAdeleRing (𝓞 k) k) = M := rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

theorem isOpen_isClosed (M : ℕ) (hM : M ≠ 0) :
    IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x} := by
  have hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} =
      (fun x => (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
        FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by
    ext x; exact inM_iff M hM x
  have hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k =>
      (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) :=
    continuous_const.mul continuous_id
  have ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := GroundTheory.Global.isOpen_integralFiniteAdeles
  rw [hS]
  exact ⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩

theorem exists_pow_lt' {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ n : ℕ, c ^ n < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

theorem natCast_apply' (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    (M : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) := by
  rw [← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap k (v.adicCompletion k)) M

theorem valued_natCast (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (n : v.adicCompletion k) = v.intValuation (n : 𝓞 k) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  rw [← this]
  congr 1
  simp

theorem eq_zero_of_forall_inM (x : FiniteAdeleRing (𝓞 k) k) (hx : ∀ M : ℕ, M ≠ 0 → InM M x) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change x v = 0
  by_contra hxv
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hNmem : (N : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt : v.intValuation (N : 𝓞 k) < 1 := (v.intValuation_lt_one_iff_mem _).mpr hNmem
  have hxv0 : Valued.v (x v) ≠ 0 := by simpa using hxv
  obtain ⟨n, hn⟩ := exists_pow_lt' hxv0 hlt
  obtain ⟨y, hy, hxy⟩ := hx (N ^ n) (pow_ne_zero _ hN0)
  have hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v := by
    rw [hxy]
    have h1 := natCast_apply' v (N ^ n)
    change ((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _
    rw [h1]
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n := by
    rw [hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]
    exact mul_le_of_le_one_right' hyv
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

theorem inMTop : InMTop := fun k _ _ =>
  ⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩

end GlobalTheory.CompanionTheory.RgEis.InMTopPf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
noncomputable section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMir

theorem avg_one_apply {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (ρ : K →* (W →L[ℂ] W)) (hρ : Continuous ρ) (w : W)
    (hw : ∀ r : K, ρ r w = w) : avg μ ρ (fun _ => (1 : ℂ)) w = w := by
  have hint : Integrable (fun κ : K => (1 : ℂ) • ρ κ) μ := by
    simp only [one_smul]
    exact hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [avg]
  rw [ContinuousLinearMap.integral_apply hint]
  simp [hw]

theorem isPar_top {G : Type} [Group G] [TopologicalSpace G] (Γ K : Subgroup G) :
    IsPar Γ K ⊤ (1 : G → ℂ) := by
  refine ⟨?_, fun g => ⟨g, Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩, ?_⟩
  · simp only [Subgroup.coe_top]
    exact isClosed_univ
  · exact ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp,
      continuous_const.continuousOn⟩

theorem sec_top_apply {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) (g : G) (w : W)
    (hw : ∀ r : K, ρ r w = w) : sec K ⊤ (1 : G → ℂ) ρ g w = w := by
  unfold sec
  rw [dite_eq_left ⟨1, Subgroup.mem_top _⟩]
  simp [hw]

theorem mirGen_of_core : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  intro _hSec hSph hMem hInv hSide hTK hCore G _ _ _ _ _ W _ _ _ K ρ hK hρ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hSC hMD
  haveI := hSC
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  have hHaar : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hProb : IsProbabilityMeasure μ := ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using h⟩
  haveI := hProb
  have hN1 : (1 : ℝ) < Fintype.card ι := by
    have h2 := hMD.two
    exact_mod_cast (show 1 < Fintype.card ι by omega)
  obtain ⟨hS0, -, -, -⟩ := hSide G K hK k ι π Γ i₀ i₁ ω d c η η' l hMD
  obtain ⟨V, hV, hJV⟩ := hInv G W K ρ hK hρ μ hHaar hProb Γ _ c hMD.par
  obtain ⟨Ψ, Ψ₁, φ, hΨ, hΨ₁, hφc, hφ1, hφL, hφN, hzt, hz, hω1⟩ :=
    hTK G K hK k ι π Γ _ i₀ ω d c η hS0 V hV
  obtain ⟨J, hJ⟩ := hJV φ hφc hφ1 hφL hφN
  obtain ⟨R, D, Op, H, hW, ⟨dd, hdd, hD, hddN⟩, -, hH⟩ :=
    hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ ω d c η η' l hMD Ψ Ψ₁ φ _ J hΨ hΨ₁ hzt hz le_rfl hJ
  refine ⟨⟨R, D, Op, H, hW⟩, fun hω hc => ?_⟩
  subst hω
  subst hc
  have hinv : ∀ w ∈ secSp K ⊤ (1 : G → ℂ) ρ, ∀ r : K, ρ r w = w := fun w hw r => by
    simpa using hw r (Subgroup.mem_top _)
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψs, Ψ₁s, hΨs, hΨ₁s, hΨ0, hsph, hnz⟩ := hSph k ι i₀
    have hzt' : ∀ s (κ : K), zt π d i₀ Ψs 1 s κ = tate Ψ₁s 1 s * (fun _ => (1 : ℂ)) κ := by
      intro s κ
      simp only [mul_one]
      unfold zt tate lineZeta
      congr 1
      funext t
      exact hsph t ⟨kap π d κ, hS0.piK κ κ.2⟩
    have hnz' : ∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁s 1 z ≠ 0 :=
      ⟨(((Fintype.card ι : ℝ) + 1 : ℝ) : ℂ), by simp, hnz _ (by linarith)⟩
    have hle : secSp K ⊤ (1 : G → ℂ) ρ ≤ secSp K ((stab _ {i₀}).comap π) 1 ρ :=
      fun w hw r _ => hw r (Subgroup.mem_top _)
    have havg : ∀ w : secSp K ⊤ (1 : G → ℂ) ρ,
        avg μ ρ (fun _ => (1 : ℂ)) ((secSp K ⊤ (1 : G → ℂ) ρ).subtypeL w) = w := fun w => by
      simpa using avg_one_apply μ ρ hρ (w : W) (hinv w w.2)
    obtain ⟨R', D', Op', H', hW', -, ⟨O', hO', hOp'⟩, hH'⟩ :=
      hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ 1 d 1 η η' l hMD Ψs Ψ₁s (fun _ => 1)
        (secSp K ⊤ (1 : G → ℂ) ρ) (secSp K ⊤ (1 : G → ℂ) ρ).subtypeL hΨs hΨ₁s hzt' hnz' hle havg
    obtain ⟨⟨a, ha, hH0⟩, -⟩ := hH' rfl
    refine ⟨R', D', Op', H', hW', ⟨a, ha, fun g w => ?_⟩, O', hO', hOp'⟩
    rw [hH0, hΨ0, mul_one, havg w, sec_top_apply K ρ g (w : W) (hinv w w.2)]
  · obtain ⟨-, b, hb⟩ := hH rfl
    have hmem : ∀ v, avg μ ρ (fun _ => (1 : ℂ)) v ∈ secSp K ⊤ (1 : G → ℂ) ρ :=
      hMem G W K ρ hK hρ μ hHaar hProb Γ ⊤ 1 (isPar_top Γ K) (fun _ => 1) continuous_const
        (fun _ _ _ => by simp)
    let T : secSp K ((stab _ {i₀}).comap π) 1 ρ →L[ℂ] secSp K ⊤ (1 : G → ℂ) ρ :=
      b • ((avg μ ρ (fun _ => (1 : ℂ))).comp J).codRestrict _ (fun w => hmem (J w))
    refine ⟨R, D, Op, H, hW, ⟨dd, hdd, hddN (hω1 rfl _ hN1), hD⟩, T, fun g w => ?_⟩
    rw [hb g w, sec_top_apply K ρ g _ (hinv _ (T w).2), mul_smul]
    rfl

end GlobalTheory.CompanionTheory.EisMir
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGenerationStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_generation : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  first | exact @GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | exact GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | (intros; apply GlobalTheory.CompanionTheory.EisMir.mirGen_of_core <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInfiniteIdeleInclusion
noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTestFun

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF

variable {k : Type} [Field k] [NumberField k]

theorem continuous_infinite_idele_inclusion :
    Continuous (ofInfinite : (InfiniteAdeleRing k)ˣ → IdeleGroup k) :=
  (ContinuousMulEquiv.symm (prodEquiv k)).continuous.comp (Continuous.prodMk_left 1)

theorem ideleModule_ofInfinite_eq (a : (InfiniteAdeleRing k)ˣ) :
    (ideleModule k (ofInfinite a) : ℝ) = ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ w.mult := by
  have h1 : ∀ w, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).1 w = (a : InfiniteAdeleRing k) w := fun w => by
    have := congrArg (fun u : (InfiniteAdeleRing k)ˣ => (u : InfiniteAdeleRing k) w) (toInfinite_ofInfinite a)
    exact this
  have h2 : ∀ v, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).2 v = 1 := fun v => by
    have := congrArg (fun u : (FiniteAdeleRing (𝓞 k) k)ˣ => (u : FiniteAdeleRing (𝓞 k) k) v) (toFinite_ofInfinite a)
    exact this
  rw [ideleModule_eq]
  simp only [h1, h2, norm_one, finprod_one, mul_one]

theorem exists_norm_rd_le (φ : 𝓢(Unit → mixedSpace k, ℂ)) (K : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing k,
      ‖rd φ (fun _ => x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ K)⁻¹ := by
  let e : mixedSpace k ≃L[ℝ] (Unit → mixedSpace k) :=
    (ContinuousLinearEquiv.funUnique Unit ℝ (mixedSpace k)).symm
  obtain ⟨C, hC, h⟩ := exists_norm_schwartz_le_prod (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) K
  refine ⟨C, hC, fun x => ?_⟩
  have hx := h x
  have he : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) (homeomorphMixedSpace k x) =
      rd φ (fun _ => x) := by
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, rd]
    congr 1
  rwa [he] at hx

theorem module_rpow_eq (a : (InfiniteAdeleRing k)ˣ) (x : ℝ) :
    (ideleModule k (ofInfinite a) : ℝ) ^ x =
      ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ ((w.mult : ℝ) * x) := by
  rw [ideleModule_ofInfinite_eq, ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]

theorem integrable_norm_rd_mul (φ : 𝓢(Unit → mixedSpace k, ℂ)) {x : ℝ} (hx : 1 < x)
    (hc : Continuous fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x) :
    Integrable (fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x)
      (infiniteIdeleMeasure k) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * x + 2)
  obtain ⟨C, hC, h⟩ := exists_norm_rd_le φ K
  refine Integrable.mono' ((integrable_infiniteZetaBound (K := k) hx.le hK).const_mul C)
    hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  have hm : 0 ≤ (ideleModule k (ofInfinite a) : ℝ) ^ x := Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hm)]
  calc ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x
      ≤ (C * ∏ w, ((1 + ‖(a : InfiniteAdeleRing k) w‖) ^ K)⁻¹) * (ideleModule k (ofInfinite a) : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right (h a) hm
    _ = C * infiniteZetaBound x K a := by
        rw [module_rpow_eq, infiniteZetaBound, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_eq_mul_inv, mul_comm]

theorem zInf_ne_zero : ZInf := by
  intro k _ _ φ ω h h1 x hx
  have hc0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => rd φ (fun _ => (a : InfiniteAdeleRing k)) :=
    φ.continuous.comp (continuous_pi fun _ =>
      (homeomorphMixedSpace k).continuous.comp Units.continuous_val)
  have hm0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => (ideleModule k (ofInfinite a) : ℝ) :=
    continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp continuous_infinite_idele_inclusion)
  set f : (InfiniteAdeleRing k)ˣ → ℝ := fun a =>
    ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x with hf
  have hcf : Continuous f :=
    hc0.norm.mul (hm0.rpow_const fun _ => Or.inr (by linarith))
  have hint : Integrable f (infiniteIdeleMeasure k) := integrable_norm_rd_mul φ hx hcf
  have hnn : 0 ≤ f := fun a => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _)
  have hpt : ∀ a : (InfiniteAdeleRing k)ˣ,
      rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
        ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ (x : ℂ) = ((f a : ℝ) : ℂ) := fun a => by
    obtain ⟨r, hr, e⟩ := h a
    have hn : r = ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ := by
      have := congrArg norm e
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr] at this
      exact this.symm
    rw [e, hn, hf]
    push_cast
    rw [Complex.ofReal_cpow (ideleModule k (ofInfinite a)).2.le]
  have hz : zInf φ ω x = ((∫ a, f a ∂infiniteIdeleMeasure k : ℝ) : ℂ) := by
    rw [zInf, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hpos : 0 < ∫ a, f a ∂infiniteIdeleMeasure k := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hop : IsOpen (Function.support f) := isOpen_compl_singleton.preimage hcf
    refine hop.measure_pos _ ⟨1, ?_⟩
    have hm1 : 0 < (ideleModule k (ofInfinite (1 : (InfiniteAdeleRing k)ˣ)) : ℝ) ^ x :=
      Real.rpow_pos_of_pos (ideleModule k (ofInfinite _)).2 _
    have : f 1 ≠ 0 := by
      simp only [hf, Units.val_one]
      exact mul_ne_zero (norm_ne_zero_iff.2 h1) hm1.ne'
    exact this
  rw [hz]
  exact_mod_cast hpos.ne'

end GlobalTheory.CompanionTheory.EisTestFun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inv_mulVec_smul_vec (m γ : GL ι 𝔸[k]) (x : 𝔸[k]) (i : ι) :
    ((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ (x • MG.vec γ i) = x • MG.vec (γ * m) i := by
  unfold MG.vec
  rw [Matrix.mulVec_smul, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]


omit [Fintype ι] [DecidableEq ι] in
theorem norm_lineZeta_le (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (v : ι → 𝔸[k]) :
    ‖lineZeta Ψ ω s v‖ ≤ ∫ t : IdeleGroup k, ‖Ψ ((t : 𝔸[k]) • v)‖ *
      (IdeleGroup.ideleModule k t : ℝ) ^ s.re ∂ideleMeasure k := by
  unfold lineZeta globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k t : ℝ) := (IdeleGroup.ideleModule k t).2
  simp only [norm_mul, Circle.norm_coe, mul_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]

section Eis

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (φ : K → ℂ) :
    avg μ ρ (fun κ => a * φ κ) = a • avg μ ρ φ := by
  unfold avg
  rw [← integral_smul]
  simp only [smul_smul]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => by rw [map_smul, smul_comm]

end Eis

theorem sideUnfold : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  intro hE hU hL hT hZ G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ s hs g w
  have hcard : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    have := hS.two
    exact_mod_cast (by omega : 1 < Fintype.card ι)
  have hs1 : 1 < s.re := hcard.trans hs
  obtain ⟨e, he⟩ := hL G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hT1, hT2⟩ := hT G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hTp, hTl, hTx⟩ := hT2 Ψ s
  obtain ⟨-, hZc, -⟩ := hZ G K hK k ι π Γ P i ω d c η hS Ψ hΨ
  set a : ℂ := (ω.toIdele (d i) : ℂ) * modPow (d i) s with ha
  let T : G → ℂ := fun y => lineZeta Ψ ω s (MG.vec (π y * dgl d) i)
  let φ : K → ℂ := fun κ => a * zt π d i Ψ ω s κ
  let Λ : G → ℂ := fun x => s * η x
  have key : ∀ (y : G) (q : Cos P Γ), lineZeta Ψ ω s
      (((π y * dgl d)⁻¹ : GL ι 𝔸[k]).1 *ᵥ ratV (e q).rep) = T (rep q * y) := by
    intro y q
    obtain ⟨x, hx⟩ := he q
    rw [hx, inv_mulVec_smul_vec, hTx]
    simp only [T, map_mul, mul_assoc]
  have hφc : Continuous φ := by
    have h1 : Continuous fun κ : K => zt π d i Ψ ω s κ := by
      have h2 : ContinuousOn (fun y : ℂ × K => zt π d i Ψ ω y.1 y.2) (Set.univ.image fun κ : K => (s, κ)) :=
        hZc.mono (by rintro _ ⟨κ, -, rfl⟩; exact ⟨hs1, Set.mem_univ _⟩)
      have h3 := h2.comp_continuous (f := fun κ : K => (s, κ)) (by fun_prop) (fun κ => ⟨κ, Set.mem_univ _, rfl⟩)
      exact h3
    exact continuous_const.mul h1
  have hφl : Law K P c φ := fun r κ hr => by
    have h : zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ := hTl r κ hr
    simp only [φ]
    rw [h]
    ring
  have hΛ : ∀ x, ∀ κ ∈ K, Λ (x * κ) = Λ x := fun x κ hκ => by
    simp only [Λ, hS.ht.right x κ hκ]
  have hTP : ∀ p ∈ P, ∀ κ : K, T (p * κ) = c p * Complex.exp (Λ p) * φ κ := fun p hp κ =>
    hTp p hp κ κ.2
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hCc : IsCompact (Set.range fun κ : K => ((π (g * κ) * dgl d)⁻¹ : GL ι 𝔸[k])) := by
    refine isCompact_range ?_
    have hπ := hS.cont
    exact ((hπ.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const).inv
  obtain ⟨u, hu, hub⟩ := (hE k ι Ψ hΨ).2 s.re _ (max_lt hs1 hs |>.trans_le le_rfl) hCc
  have hbound : ∀ (q : Cos P Γ) (κ : K), ‖T (rep q * (g * κ))‖ ≤ (u ∘ e) q := fun q κ => by
    rw [← key]
    exact (norm_lineZeta_le Ψ ω s _).trans (hub _ ⟨κ, rfl⟩ (e q))
  have hfun : (fun κ : K => epstein Ψ ω s (π (g * κ) * dgl d)) = fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ)) := by
    funext κ
    unfold epstein
    rw [← e.tsum_eq]
    exact tsum_congr fun q => key _ q
  have hmain := hU G W K ρ hK hρ μ hμ hP Γ P c hS.par φ Λ T hφc hφl hΛ hTP g (u ∘ e) (e.summable_iff.2 hu) hbound w
  rw [hfun, hmain]
  simp only [φ]
  rw [avg_const_mul, _root_.smul_apply, eis_smul]

end GlobalTheory.CompanionTheory.RgEisSide
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfoldingStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_unfolding : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideUnfold | exact GlobalTheory.CompanionTheory.RgEisSide.sideUnfold | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideUnfold <;> assumption)
end
end
