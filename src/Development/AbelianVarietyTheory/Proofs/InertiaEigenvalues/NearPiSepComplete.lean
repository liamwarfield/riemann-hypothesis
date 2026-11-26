module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

theorem sep_complete_of_coord {R A B I : Type} [AddCommGroup R] [CommRing A] [CommRing B]
    (φ : I → R →+ B) (j : A →+* B) (hj : Function.Injective j) (t : A)
    (hs : ∀ c : I → A, ∃ x : R, ∀ i, φ i x = j (c i))
    (h1 : ∀ x : A, (∀ m : ℕ, t ^ m ∣ x) → x = 0)
    (h2 : ∀ a : ℕ → A, ∃ x : A, ∀ m : ℕ, t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i) :
    (∀ x : R, (∀ (m : ℕ) i, ∃ c, φ i x = j (t ^ m * c)) → ∀ i, φ i x = 0) ∧
    ∀ (k : ℕ) (f : ℕ → R), (∀ n i, ∃ c, φ i (f n) = j (t ^ (n + k) * c)) →
      ∃ x, ∀ (m : ℕ) i, ∃ c, φ i (x - ∑ n ∈ Finset.range m, f n) = j (t ^ (m + k) * c) := by
  refine ⟨fun x hx i => ?_, fun k f hf => ?_⟩
  · obtain ⟨y, hy⟩ := hx 0 i
    rw [pow_zero, one_mul] at hy
    have hdiv : ∀ m : ℕ, t ^ m ∣ y := by
      intro m
      obtain ⟨c, hc⟩ := hx m i
      exact ⟨c, hj (hy.symm.trans hc)⟩
    rw [hy, h1 y hdiv, map_zero]
  · choose c hc using hf
    choose y hy using fun i => h2 (fun n => c n i)
    obtain ⟨x, hx⟩ := hs (fun i => t ^ k * y i)
    refine ⟨x, fun m i => ?_⟩
    obtain ⟨d, hd⟩ := hy i m
    refine ⟨d, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hx i, Finset.sum_congr rfl (fun n _ => hc n i), ← map_sum j, ← map_sub j]
    congr 1
    have e : t ^ k * y i - ∑ n ∈ Finset.range m, t ^ (n + k) * c n i =
        t ^ k * (y i - ∑ n ∈ Finset.range m, t ^ n * c n i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hd]
    ring

def crdZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    RW LL →+ Cb l :=
  (WittVector.constantCoeff : WCb l →+* Cb l).toAddMonoidHom.comp
    (crd (W := WCb l) (basisO LL) i).toAddMonoidHom

theorem crdZero_apply {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i) (x : RW LL) :
    crdZero LL i x = (crd (basisO LL) i x).coeff 0 := rfl

private theorem crd_tmul_lemma {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (o : ↥(OL LL)) (w : WCb l) :
    crd (W := WCb l) (basisO LL) i (o ⊗ₜ[ℤ_[l]] w) = (basisO LL).coord i o • w := by
  unfold crd
  rfl

set_option maxHeartbeats 1000000 in
private theorem crd_mul_lemma_2 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (q : WCb l) (y : RW LL) :
    crd (W := WCb l) (basisO LL) i (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] q) * y) =
      q * crd (W := WCb l) (basisO LL) i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma, mul_smul_comm]
  | add y z hy hz =>
    rw [mul_add, LinearMap.map_add (f := _), LinearMap.map_add (f := _), hy, hz]
    exact (mul_add q _ _).symm

private theorem expand_lemma_3 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (y : RW LL) :
    ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] crd (W := WCb l) (basisO LL) k y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [crd_tmul_lemma, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    simp_rw [Module.Basis.coord_apply]
    rw [Module.Basis.sum_repr]
  | add y z hy hz => simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WCb l) :
    crd (W := WCb l) (basisO LL) i (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] w k) = w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, crd_tmul_lemma, Finsupp.single_apply]

private theorem wdiv_lemma_5 {l : ℕ} [Fact l.Prime] (w : WCb l) (hw : w.coeff 0 = 0) :
    ∃ v : WCb l, w = (l : WCb l) * v := by
  have e : w = WittVector.verschiebung^[1] (w.shift 1) :=
    WittVector.eq_iterate_verschiebung (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hw)
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective (p := l) (R := Cb l)).2 (w.shift 1)
  refine ⟨z, ?_⟩
  rw [e, Function.iterate_one, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private theorem rwdiv_lemma_6 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (z : RW LL)
    (hz : ∀ i, (crd (W := WCb l) (basisO LL) i z).coeff 0 = 0) : ∃ r : RW LL, z = (l : RW LL) * r := by
  choose v hv using fun i => wdiv_lemma_5 _ (hz i)
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] v k, ?_⟩
  rw [← expand_lemma_3 LL z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hv k, ← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

private theorem cc_inclW_lemma_7 {l : ℕ} [Fact l.Prime] (w : Ainf l) :
    (inclW l w).coeff 0 = algebraMap (OCb l) (Cb l) (w.coeff 0) := by
  unfold inclW
  exact WittVector.map_coeff _ _ 0

private theorem cc_pi_lemma_8 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ) :
    (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 =
      algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [cc_inclW_lemma_7]
  congr 1
  change WittVector.constantCoeff (WittVector.teichmuller l (AI.εroot s) - 1) = _
  rw [map_sub, map_one]
  rfl

private theorem inclR_piR_lemma_9 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    piR AI LL s =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (AI.εroot s) - 1) := rfl

private theorem inclR_tmul_lemma_10 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (o : ↥(OL LL)) (w : Ainf l) :
    (inclR LL) (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] inclW l w := rfl

private theorem cc_inclR_lemma_11 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l) :
    ∃ c : OCb l, (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 = algebraMap (OCb l) (Cb l) c := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o w =>
    refine ⟨((basisO LL).coord i o • w).coeff 0, ?_⟩
    rw [inclR_tmul_lemma_10, crd_tmul_lemma, ← cc_inclW_lemma_7]
    congr 1
    exact (map_smul (inclWA l) _ _).symm
  | add a b ha hb =>
    obtain ⟨c1, h1⟩ := ha
    obtain ⟨c2, h2⟩ := hb
    refine ⟨c1 + c2, ?_⟩
    have e : (inclR LL) (a + b) = (inclR LL) a + (inclR LL) b := (inclR LL).toRingHom.map_add a b
    rw [e, LinearMap.map_add (f := _), map_add (algebraMap (OCb l) (Cb l)), ← h1, ← h2]
    exact WittVector.add_coeff_zero _ _

private theorem coord_of_near_lemma_12 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL) (h : NearPi AI LL s n y)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c) := by
  unfold NearPi Near at h
  obtain ⟨a, r, rfl⟩ := h
  obtain ⟨c, hc⟩ := cc_inclR_lemma_11 LL i a
  refine ⟨c, ?_⟩
  rw [map_add (f := _), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, crdZero_apply, inclR_piR_lemma_9,
    Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2]
  change WittVector.constantCoeff (p := l) (R := Cb l) (_ * _) + _ = _
  rw [map_mul, map_pow]
  change (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
    (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 + _ = _
  rw [cc_pi_lemma_8, hc, map_mul, map_pow]
  simp

set_option maxHeartbeats 2000000 in
private theorem near_of_coord_lemma_13 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL)
    (h : ∀ i, ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c)) :
    NearPi AI LL s n y := by
  choose c hc using h
  let a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l := ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)
  obtain ⟨r, hr⟩ := rwdiv_lemma_6 LL (y - piR AI LL s ^ n * (inclR LL) a) (fun i => by
    have ha : (inclR LL) a = ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (c k)) := by
      change (inclR LL : RA LL →+* RW LL) (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [LinearMap.map_sub, inclR_piR_lemma_9, Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2, ha,
      crd_sum_lemma_4]
    change WittVector.constantCoeff (p := l) (R := Cb l) (_ - _) = 0
    rw [map_sub, map_mul, map_pow]
    change (crd (W := WCb l) (basisO LL) i y).coeff 0 -
      (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
        (inclW l (WittVector.teichmuller l (c i))).coeff 0 = 0
    rw [← crdZero_apply, hc, cc_pi_lemma_8, cc_inclW_lemma_7, WittVector.teichmuller_coeff_zero, map_mul,
      map_pow, sub_self])
  unfold NearPi Near
  exact ⟨a, r, sub_eq_iff_eq_add'.mp hr⟩

private theorem surj_lemma_14 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (c : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l) :
    ∃ x : RW LL, ∀ i, crdZero LL i x = algebraMap (OCb l) (Cb l) (c i) := by
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (c k)),
    fun i => ?_⟩
  rw [crdZero_apply, crd_sum_lemma_4, WittVector.teichmuller_coeff_zero]

theorem nearPi_sep_complete (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧
    ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) →
      ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  have key := sep_complete_of_coord (fun i => crdZero LL i) (algebraMap (OCb l) (Cb l))
    (IsFractionRing.injective (OCb l) (Cb l)) (AI.εroot s - 1) (surj_lemma_14 LL)
    (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).1 (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).2
  refine ⟨fun x hx => ?_, fun k f hf => ?_⟩
  · refine rwdiv_lemma_6 LL x fun i => ?_
    rw [← crdZero_apply]
    exact key.1 x (fun m i => coord_of_near_lemma_12 P AI LL s m x (hx m) i) i
  · obtain ⟨x, hx⟩ := key.2 k f (fun n i => coord_of_near_lemma_12 P AI LL s (n + k) (f n) (hf n) i)
    exact ⟨x, fun m => near_of_coord_lemma_13 P AI LL s (m + k) _ (hx m)⟩

end GlobalTheory.Decompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepCompleteStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearPi_sep_complete_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧ ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.nearPi_sep_complete | exact GlobalTheory.Decompl.nearPi_sep_complete | (intros; apply GlobalTheory.Decompl.nearPi_sep_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivial
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem resΓ_eq_one_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) (h1 : P.χQ g = 1) : W.resΓ g = 1 := by
  apply W.χΓ_inj
  rw [map_one W.χΓ]
  apply Units.ext
  apply Subtype.ext
  have h3 := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at h3
  exact h3

theorem hinf_fixes_εroot_and_resΓ_eq_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l),
    (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧
    ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K,
      ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  intro l _ P AI K
  have hχ : ∀ g ∈ Hinf K, P.χQ g = 1 := fun g hg =>
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g
      (IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Kinf K from le_sup_left) hg)).2.1 hg
  refine ⟨fun g hg j => ?_, fun s LL hG W g hg => ?_⟩
  · have := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by simp [hχ g hg]) j
    rwa [pow_one] at this
  · have h1 : Ks K s ≤ Kinf K := by
      apply sup_le_sup_left _ _
      apply IntermediateField.adjoin.mono
      intro x hx
      exact ⟨s, hx⟩
    have h2 : K.1 ≤ Ks K s := hG.2.2.1
    have hgK : g ∈ GK K := IntermediateField.fixingSubgroup_antitone (h2.trans h1) hg
    exact ⟨hgK, resΓ_eq_one_of_chi P W ⟨g, hgK⟩ (hχ g hg)⟩

end GlobalTheory.Decompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivialStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l), (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧ ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K, ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  first | exact @GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | exact GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | (intros; apply GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRingStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  first | exact @GlobalTheory.ExpImage.nearZ_of_forall_Lat | exact GlobalTheory.ExpImage.nearZ_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.nearZ_of_forall_Lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDuality
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem exists_fundamental_cocycle_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧
      ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]),
        Continuous (fun g => (χ g : ℤ_[l])) ∧
        (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧
        (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧
        ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep
          ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  intro l _ P K
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  refine ⟨Φ.symm.surjective.compactSpace hΦ1, χZ.comp Φ.toMonoidHom, _, hχc.comp hΦ2,
    fun g => ?_, fun r => (hc r).transport Φ hΦ2 hΦ1, fun r hr => ?_⟩
  · have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    exact h1
  · have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hfin := (GlobalTheory.T.finite_H1_H2_local hT l K.1 K.2 r (ZMod (l ^ r))
      (ReciprocityTheory.Gal.charRep (redChar χZ r)) hr
      (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
    obtain ⟨e⟩ := (GlobalTheory.contCohomology_transport_mulEquiv (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1)
      ↥(GK K) (ZMod (l ^ r)) Φ hΦ2 hΦ1 (ReciprocityTheory.Gal.charRep (redChar χZ r))
      (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
        (χZ.comp Φ.toMonoidHom))) (fun g m => rfl)).1
    exact Finite.of_equiv _ e

end GlobalTheory.TateTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalTwoCocycleOfLocalTateDualityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), CompactSpace ↥(GK K) ∧ ∃ (χ : ↥(GK K) →* ℤ_[l]ˣ) (c : ↥(GK K) × ↥(GK K) → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) ∧ (∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) ∧ (∀ r, GlobalTheory.TateTop.Gen χ r c) ∧ ∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ))) := by
  first | exact @GlobalTheory.TateTop.exists_fundamental_cocycle_loc | exact GlobalTheory.TateTop.exists_fundamental_cocycle_loc | (intros; apply GlobalTheory.TateTop.exists_fundamental_cocycle_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpen
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isOpen_ker_map_of_isOpen_ker {Γ A B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ} (f : A →+* B) (hf : IsOpen ((RingHom.ker f : Ideal A) : Set A))
    (ρ : Γ →* GL (Fin n) A) (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A))) :
    IsOpen (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) := by
  classical

  let U : Set (Matrix (Fin n) (Fin n) A) :=
    {M | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ RingHom.ker f}
  have hU : IsOpen U := by
    have : U = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) A =>
        M i j - (1 : Matrix (Fin n) (Fin n) A) i j) ⁻¹' ((RingHom.ker f : Ideal A) : Set A) := by
      ext M; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hf.preimage ((continuous_id.matrix_elem i j).sub continuous_const)

  have hker : (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) =
      (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A)) ⁻¹' U := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Set.mem_preimage, U,
      Set.mem_ofPred_eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    rw [Units.ext_iff]
    change f.mapMatrix ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A) =
      ((1 : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) ↔ _
    rw [Units.val_one, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hker]
  exact hU.preimage hρ

theorem redF_ker_isOpen (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) :
    IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by

  have hk : ((RingHom.ker ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) : Ideal (D.nd.O i)) :
      Set (D.nd.O i)) = (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext x
    simp [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]
  have hm : IsOpen (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic i)).1 1
  exact isOpen_ker_map_of_isOpen_ker _ (hk ▸ hm) ρ hρ

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpenStatement
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRep_ker_isOpen : ∀ (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by
  first | exact @GlobalTheory.TypeLeaf.redF_ker_isOpen | exact GlobalTheory.TypeLeaf.redF_ker_isOpen | (intros; apply GlobalTheory.TypeLeaf.redF_ker_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isDR_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  intro l _ P n _ _ K V _ _ b ρ Q hQ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK
  haveI : Nontrivial P.R.BdR := by
    refine ⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] P.R.BdR V n b
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x :=
    fun g x => P.PD_actdR K g x
  have key := GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K)
    (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR))
    (fun x => ⟨fun h => (P.PD K).invdR x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actdR g).commutes c⟩) Q
    (fun g => by
      have h := hQ g
      have : (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l) :=
        funext (hact g)
      rw [this]
      exact h)
    ((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔
          y ∈ DdR (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y
      have h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b] at key
  exact key

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_invertible_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.PMon.isDR_of_periodMatrix | exact GlobalTheory.PMon.isDR_of_periodMatrix | (intros; apply GlobalTheory.PMon.isDR_of_periodMatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOfGood
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.Cyc.CrysDeRham

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_Ks_of_good {K LL : FinExt l} {s : ℕ} (h : Good K s LL) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hle : Ks K s ≤ LL.1 := fun x hx => h.2.2.2 (Ks K s).val ⟨x, hx⟩
  have := LL.2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem apply_mem_Ks (K : FinExt l) (s : ℕ) :
    ∀ g ∈ GK K, ∀ x ∈ Ks K s, g x ∈ Ks K s := by
  intro g hg
  have key : Ks K s ≤ (Ks K s).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro x hx
      have h1 : g x = x := hg ⟨x, hx.1⟩
      change g x ∈ Ks K s
      rw [h1]
      exact (le_sup_left : K0 K ≤ Ks K s) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K s
      apply (le_sup_right : _ ≤ Ks K s)
      apply IntermediateField.subset_adjoin
      have hx' : x ^ (l ^ s) = 1 := hx
      change (g x) ^ (l ^ s) = 1
      rw [← map_pow, hx', map_one]
  intro x hx
  exact key hx

noncomputable def restrictRep {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  modO := T.modO
  towO := T.towO
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_inclusion (GK_le hle))

theorem isDR_of_restrict (P : LocPrime l) {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (hs : ∀ g ∈ GK K, ∀ x ∈ E.1, g x ∈ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (h : IsDR (P.PD E) (restrictRep hle T).ρ) : IsDR (P.PD K) T.ρ :=
  GlobalTheory.T.isDeRham_of_restrict_galois_descent l P K E LL (GK_le hle) hle hs T.V T.ρ h


set_option maxHeartbeats 1600000 in
theorem isDR_of_isCrysOn : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → IsDR S.PD T.ρ := by
  intro D HW hF l _ K s LL h S T hT
  let E : FinExt l := ⟨Ks K s, finiteDimensional_Ks_of_good h⟩
  have hle : K.1 ≤ E.1 := h.2.2.1
  have h1 := isCrys_Ks_of_finrank l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h)
    E rfl hle T hT
  have h2 := (hF l E ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.goodO_integers l LL)
    (restrictRep hle T)).2.2 h1
  exact isDR_of_restrict (D.loc l) hle (apply_mem_Ks K s) T h2

end GlobalTheory.Cyc.CrysDeRham
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZeta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZeta
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.LevExp

theorem eq_exp {F : Type} [Field F] [CharZero F] [Algebra ℚ F] (E : PowerSeries F)
    (h0 : PowerSeries.constantCoeff E = 1) (h1 : PowerSeries.derivative (R := F) E = E) :
    E = PowerSeries.exp F := by
  exact PowerSeries.exp_unique_of_derivative_eq_self h1 h0

theorem map_poly {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {n : ℕ} (f : LetA O n →ₐ[O] A)
    (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) = Polynomial.aeval (f letπ) (p i) := by
  have hfam : f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      f (fun _ => ((p i : Polynomial O) : PowerSeries O)) := by
    have h := hf ((fun j => ((p j : Polynomial O) : PowerSeries O)) -
      (fun _ => ((p i : Polynomial O) : PowerSeries O))) (by simp)
    rwa [map_sub, sub_eq_zero] at h
  rw [hfam]
  have hg : f.comp ((Pi.constAlgHom O (ZMod n) (PowerSeries O)).comp
      (Polynomial.coeToPowerSeries.algHom O)) = Polynomial.aeval (f letπ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.coeToPowerSeries.algHom_apply,
      Polynomial.coe_X, Algebra.algebraMap_self, PowerSeries.map_id]
    rfl
  have h2 := congrArg (fun φ => φ (p i)) hg
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self,
    PowerSeries.map_id] at h2
  exact h2

theorem map_poly_series {O L : Type} [CommRing O] [CommRing L] [Algebra O L] {n : ℕ}
    (f : LetA O n →ₐ[O] PowerSeries L) (i : ZMod n) (hf : ∀ a, a i = 0 → f a = 0) (p : ZMod n → Polynomial O) :
    f (fun j => ((p j : Polynomial O) : PowerSeries O)) =
      Polynomial.aeval (f letπ) ((p i).map (algebraMap O L)) := by
  rw [map_poly f i hf p, Polynomial.aeval_map_algebraMap]

theorem lev_isExp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  intro l _ P K s LL Γ R i ζ hζ a
  have hπ : R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 := by
    obtain ⟨E, hE0, hE1, hE⟩ := R.lev_π i ζ (by rw [P.PD_p K]; exact hζ)
    rw [eq_exp E hE0 hE1] at hE
    rw [← hE]
    ring
  have htr : ∀ m : ℕ, Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1)
      (PowerSeries.trunc m (toLL a i)) =
      R.lev i ζ (fun j => ((PowerSeries.trunc m (a j) : Polynomial ↥(OL LL)) : PowerSeries ↥(OL LL))) := by
    intro m
    rw [map_poly_series (R.lev i ζ) i (R.lev_letter i ζ) (fun j => PowerSeries.trunc m (a j)), hπ]
    simp only [toLL, PowerSeries.trunc_map]
  intro k
  simp only [htr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (l : ℝ) ^ (-(r : ℝ)) < ε := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
    refine ⟨r, ?_⟩
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
    exact hr
  obtain ⟨m₀, hm₀⟩ := R.lev_cont i ζ a k r
  refine ⟨m₀, fun m hm => ?_⟩
  have hv := hm₀ m hm
  rw [← WithTop.coe_natCast] at hv
  have hn := ((NormVal.locPrime_v_normalised l P LL).2.1 _ (r : ℚ)).1 hv
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc _ = _ := by push_cast; rfl
    _ ≤ _ := hn
    _ = (l : ℝ) ^ (-(r : ℝ)) := by push_cast; rfl
    _ < ε := hr

end GlobalTheory.HWL.LevExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  first | exact @GlobalTheory.HWL.LevExp.lev_isExp | exact GlobalTheory.HWL.LevExp.lev_isExp | (intros; apply GlobalTheory.HWL.LevExp.lev_isExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.RankDeRham

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)


include PD in
theorem one_ne_zero_BdR : (1 : BdR) ≠ 0 := by
  intro h
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by rw [← mul_one (PD.ι PD.t), h, mul_zero]
  rw [this]
  exact Submodule.zero_mem _


include PD in
theorem eq_zero_of_tmul_one (v : V) (hv : v ⊗ₜ[Qp] (1 : BdR) = 0) : v = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero_BdR PD)
  have h := congrArg (fun x => TensorProduct.rid Qp V (LinearMap.lTensor V f x)) hv
  simpa [hf] using h

theorem finrank_H0V_le [FiniteDimensional LL ↥(DdR PD ρ)] :
    finrank LL ↥(H0V ρ) ≤ finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) := by
  haveI : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let j : V →ₗ[LL] V ⊗[Qp] BdR := (AlgebraTensorModule.mk Qp LL V BdR).flip 1
  have hj : ∀ v, j v = v ⊗ₜ[Qp] (1 : BdR) := fun v => rfl
  have hm : ∀ v ∈ H0V ρ, j v ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0 := by
    intro v hv
    refine ⟨?_, ?_⟩
    · simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hv
      have : j v ∈ DdR PD ρ := by
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero]
        intro g
        rw [hj]
        simp [actVdR, hv g]
      exact this
    · exact ⟨v ⊗ₜ[Qp] ⟨1, PD.one_mem⟩, by simp [hj]⟩
  refine LinearMap.finrank_le_finrank_of_injective (f := j.restrict hm) ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  have h0 : j v.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
  have := eq_zero_of_tmul_one PD v.1 (by rw [← hj]; exact h0)
  exact (Submodule.mem_bot _).2 (Subtype.ext this)

theorem h0_add_le [FiniteDimensional LL V] (hK : finrank Qp K = 1) (h : IsDR PD ρ) :
    (finrank LL ↥(H0V ρ) : ℤ) + ((finrank LL ↥(DdR PD ρ) : ℤ) -
      finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) ≤ finrank LL V := by
  have h' : finrank LL ↥(DdR PD ρ) = finrank LL V := by rw [h, hK, one_mul]
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · have := Submodule.finrank_le (H0V ρ)
    omega
  · haveI : FiniteDimensional LL ↥(DdR PD ρ) := Module.finite_of_finrank_pos (by omega)
    have := finrank_H0V_le PD ρ
    omega

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_H1f_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), finrank ℚ_[l] ↥K.1 = 1 → LocalSituation.bkAll (P.PD K) → ∀ A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsDR (P.PD K) A.ρ → finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) ≤ finrank ↥LL.1 A.V := by
  intro l _ P K LL hK hBK A hA
  have hd := hBK.2.1 _ _ (goodO_ringOfIntegers l LL) A hA
  have h := h0_add_le (P.PD K) A.ρ hK hA
  rw [← hd] at h
  exact_mod_cast h

end GlobalTheory.Pass.RankDeRham
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitFor_of_tie (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W RA RW inclR φR gR πA)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E := by
  intro e₀ h₀
  obtain ⟨e₁, f₀, hf₀, hj, hN⟩ := E.one_e
  obtain ⟨u, hu, hT⟩ := W.one_line
  have huT : u ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf₀ ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h₀ ▸ Submodule.mem_top : f₀ ∈ Submodule.span O {e₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] e₀ := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hde : d • (c • e₁) = e₁ := by
    apply E.jD_inj
    rw [map_smul, hje, hj, ← hd, TensorProduct.tmul_smul]
  refine ⟨c • e₁, hje, ⟨fun x y hxy => ?_, ?_⟩, ?_, fun g => ?_, ?_⟩
  · have h1 := congrArg (E.jD W.one) hxy
    simp only at h1
    rw [E.jD_smul, E.jD_smul, hje, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact GlobalTheory.EtaleExact.ioE_injective E
      (GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one u hu huT e₀ h₀ _ _ h1)
  · have htop : Submodule.span W.EE {c • e₁} = ⊤ := by
      refine GlobalTheory.EtaleExact.eq_top_DD E hm W.one _ ?_
      rw [eq_top_iff]
      rintro z -
      have h1 : ((1 : RW) ⊗ₜ[O] e₀ : TW RW W.one) ∈ Submodule.span RW
          (E.jD W.one '' (Submodule.span W.EE {c • e₁} : Submodule W.EE (W.DD W.one))) :=
        Submodule.subset_span ⟨c • e₁, Submodule.mem_span_singleton_self _, hje⟩
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => exact Submodule.add_mem _ ha hb
      | tmul r t =>
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
          (h₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {e₀})
        have h2 : (r ⊗ₜ[O] (a • e₀) : TW RW W.one) = (a • r) • ((1 : RW) ⊗ₜ[O] e₀) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
        rw [h2]
        exact Submodule.smul_mem _ _ h1
    intro z
    exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : z ∈ Submodule.span W.EE {c • e₁})
  · apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  · obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  · rw [hN]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) d, by rw [algebraMap_smul, hde]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) c, by rw [algebraMap_smul]⟩

end Generic

theorem unitPart : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H), GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitPart l P AI H F := by
  intro l _ P AI H F K s LL h
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  refine unitFor_of_tie Subtype.val_injective _
    (GlobalTheory.EtaleExact.map_ne_top_of_tie (F.E K s LL h).tie ?_ ?_)
  · rw [hp]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL
  · rw [hp]
    exact GlobalTheory.EtaleExact.sep_RW LL

end GlobalTheory.WachUnit
end
end
