module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
noncomputable section

namespace GlobalTheory.VolRatioCompare

open NumberField Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def reLat (V : HSpace E) (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : HSpace E :=
  { V with L0 := L, standardTuple_isLattice := h1, baseLattice_isUnimodular := h2 }

end GlobalTheory.VolRatioCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F mo) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : AddMonoidAlgebra.coeff F mo = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * AddMonoidAlgebra.coeff F mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := by
      have h1 := congrArg (AddMonoidAlgebra.coeff · mo) hQ
      rw [coeff_smul] at h1
      have h2 : AddMonoidAlgebra.coeff (toK K _ Q) mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (AddMonoidAlgebra.coeff Q mo)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.NabStab

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem int_of_mem_colLat_one {x : Fin n → K} (hx : x ∈ colLat (1 : GL (Fin n) K)) (a : Fin n) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, rfl⟩ := h
    by_cases h : a = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [Matrix.one_apply, h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; rfl⟩
  | smul r x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨r * u, by rw [map_mul, hu, Pi.smul_apply, Algebra.smul_def]⟩

theorem exists_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K) := by
  classical
  have h1 : ∀ j : Fin n, (fun a : Fin n => (g : Matrix (Fin n) (Fin n) K) a j) ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat (1 : GL (Fin n) K)) := by
    intro j
    unfold IsBasisAt at h
    rw [h]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  choose s hs hs' using h1
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * (g : Matrix (Fin n) (Fin n) K) a j := by
    intro a j
    obtain ⟨y, hy⟩ := int_of_mem_colLat_one (hs' j) a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, Pi.smul_apply, Algebra.smul_def,
      mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

theorem isBasisAt_inv (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    IsBasisAt w (colLat 1) g⁻¹ := by
  rw [← isBasisAt_gLat w g, ← colLat_mul, mul_one, mul_inv_cancel]
  exact h.symm

theorem det_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

theorem detPow_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) (e : ℤ) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * detPow K n g e := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := det_int w g h
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_natCast, Units.val_pow_eq_pow_val]
  · obtain ⟨t, ht, y, hy⟩ := det_int w g⁻¹ (isBasisAt_inv w g h)
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, map_inv]

theorem degree_of_weight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_weight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct]

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

theorem sqAct_mem (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g)
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • sqAct K n lam g f ∈ (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  obtain ⟨u, hu, y, hy⟩ := detPow_int w g h lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul]
  rw [map_smul, toK_apply, toK_apply, map_rowAct, hT, rowAct_smul _ _ _ hK.1, sqAct,
    ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, map_mul, map_pow]
  congr 1
  ring

theorem polyAction_mem_locP_nabStd (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (h : ∀ τ, IsBasisAt w (colLat 1) (g τ)) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_mem w (g τ) (h τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod]
      simp only [map_smul]
      exact (Finset.prod_smul _ _ _).symm
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul]
  exact h2

end GlobalTheory.NabStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAtStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualETwo
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Model

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

theorem _root_.GlobalTheory.TestLat.Model.mem_sumLat (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam))
    (u : Fin N → K) : u ∈ _root_.GlobalTheory.TestLat.sumLat lam e T ↔
      ∀ c, _root_.GlobalTheory.TestLat.valAt lam e c u ∈ T c := by
  simp only [_root_.GlobalTheory.TestLat.sumLat, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.Model.valAt_bijective (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) :
    Function.Bijective fun (u : Fin N → K) (c : C) => _root_.GlobalTheory.TestLat.valAt lam e c u := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun f a => (_root_.Formalism.L2.DIV.bVV K lam).equivFun (f (e a).1) (e a).2, fun u => ?_, fun f => ?_⟩
  · ext a
    simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
  · ext c
    simp [_root_.GlobalTheory.TestLat.valAt, LinearMap.funLeft_apply]

omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.Model.sumGram_form [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by
  classical
  simp only [dotProduct, Matrix.mulVec, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply, Pi.star_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
    LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos rfl]
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

end GlobalTheory.TestLat.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.SumLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

def valEquiv (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) : (Fin N → K) ≃ₗ[K] (C → VV K lam) :=
  LinearEquiv.ofBijective (LinearMap.pi fun c => valAt lam e c) (Model.valAt_bijective lam e)

theorem _root_.GlobalTheory.TestLat.SumLat.idx_nonempty (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have hne : (_root_.Formalism.L2.Col.extV ℚ lam : _root_.Formalism.L2.DIV.VV ℚ lam) ≠ 0 := by
    intro h
    apply _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (fun _ => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ) lam
      (Rat.castHom ℂ)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})
    rw [h]
    exact map_zero _
  haveI : Nontrivial (_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

theorem _root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat [Finite C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)) (hT : ∀ c, Submodule.IsLattice K (T c)) :
    Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) := by
  classical
  haveI := Fintype.ofFinite C
  set f := _root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e with hf
  let g : C → _root_.Formalism.L2.DIV.VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => _root_.Formalism.L2.DIV.VV K lam) c
  have hval : ∀ c c' t, _root_.GlobalTheory.TestLat.valAt lam e c' (g c t) = (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
    intro c c' t
    have h := congrFun (f.apply_symm_apply (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam)) c'
    exact h
  have hsum : ∀ u, ∑ c, g c (_root_.GlobalTheory.TestLat.valAt lam e c u) = u := by
    intro u
    apply f.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have h : ∀ c, f (g c (_root_.GlobalTheory.TestLat.valAt lam e c u)) =
        Pi.single c (_root_.GlobalTheory.TestLat.valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => _root_.GlobalTheory.TestLat.valAt lam e c u)
  set L : Submodule (𝓞 K) (Fin N → K) := ⨆ c, (T c).map ((g c).restrictScalars (𝓞 K)) with hL
  have hP : _root_.GlobalTheory.TestLat.sumLat lam e T = L := by
    apply le_antisymm
    · intro u hu
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hu
      rw [← hsum u]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem (hu c))
    · rw [hL, iSup_le_iff]
      intro c
      rw [Submodule.map_le_iff_le_comap]
      intro t ht
      rw [Submodule.mem_comap, _root_.GlobalTheory.TestLat.Model.mem_sumLat]
      intro c'
      rw [LinearMap.restrictScalars_apply, hval]
      by_cases hc : c' = c
      · subst hc
        rw [Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hc]
        exact zero_mem _
  have key : ∀ c, ∀ t ∈ Submodule.span K (T c : Set (_root_.Formalism.L2.DIV.VV K lam)),
      g c t ∈ Submodule.span K (L : Set (Fin N → K)) := by
    intro c t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem hx))
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  rw [hP]
  refine ⟨Submodule.fg_iSup _ fun c => ((hT c).fg).map _, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem _root_.GlobalTheory.TestLat.SumLat.sumLat_lattice_dual : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (C : Type) [Nonempty C]
    (N : ℕ) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)),
    (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) ∧
      0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) →
        _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) (_root_.GlobalTheory.TestLat.sumLat lam e T) =
          _root_.GlobalTheory.TestLat.sumLat lam e fun c => _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) := by
  intro K _ _ _ ι _ n lam C _ N e T hT
  classical
  obtain ⟨i₀⟩ := _root_.GlobalTheory.TestLat.SumLat.idx_nonempty lam
  haveI : Finite (C × _root_.Formalism.L2.DIV.VVIdx lam) := Finite.of_equiv _ e
  haveI : Finite C :=
    Finite.of_surjective (fun p : C × _root_.Formalism.L2.DIV.VVIdx lam => p.1) (fun c => ⟨(c, i₀), rfl⟩)
  haveI : Fintype C := Fintype.ofFinite C
  refine ⟨_root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat lam e T hT, ?_, ?_⟩
  · obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
    refine Nat.pos_of_ne_zero fun h => ?_
    subst h
    exact (e.symm (c₀, i₀)).elim0
  · intro G _
    ext x
    rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
    have hmemD : ∀ L : Submodule (𝓞 K) (Fin N → K), x ∈ _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) L ↔
        ∀ y ∈ L, star y ⬝ᵥ _root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ x ∈ (1 : Submodule (𝓞 K) K) :=
      fun _ => Iff.rfl
    have hmemV : ∀ (c : C) (v : _root_.Formalism.L2.DIV.VV K lam), v ∈ _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) ↔
        ∀ z ∈ T c, _root_.Formalism.L2.DIV.pairK lam G z v ∈ (1 : Submodule (𝓞 K) K) := by
      intro c v
      unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
      simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    rw [hmemD]
    simp_rw [_root_.GlobalTheory.TestLat.Model.sumGram_form, hmemV]
    constructor
    · intro h c z hz
      set y := (_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).symm (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) with hydef
      have hy : ∀ c', _root_.GlobalTheory.TestLat.valAt lam e c' y = (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
        intro c'
        have h' := congrFun
          ((_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).apply_symm_apply (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam)) c'
        exact h'
      have hyL : y ∈ _root_.GlobalTheory.TestLat.sumLat lam e T := by
        rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        rw [hy]
        by_cases hc : c' = c
        · subst hc
          rw [Pi.single_eq_same]
          exact hz
        · rw [Pi.single_eq_of_ne hc]
          exact zero_mem _
      have hsum := h y hyL
      rwa [Finset.sum_eq_single c
        (fun c' _ hc => by rw [hy, Pi.single_eq_of_ne hc, map_zero, LinearMap.zero_apply])
        (by simp), hy, Pi.single_eq_same] at hsum
    · intro h y hy
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hy
      exact Submodule.sum_mem _ fun c _ => h c _ (hy c)

end GlobalTheory.TestLat.SumLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (C : Type) [Nonempty C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (T : C → Submodule (𝓞 K) (VV K lam)), (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (sumLat lam e T) ∧ 0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) → hdualFr (sumGram lam e G) (sumLat lam e T) = sumLat lam e fun c => Formalism.HermitianLatticesTheory.dual (pairK lam G) (T c) := by
  first | exact @GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | exact GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | (intros; apply GlobalTheory.TestLat.SumLat.sumLat_lattice_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylRowActMemOfIsUnitDet
namespace GlobalTheory.TestLat

theorem weyl_rowAct_mem_of_isUnit_det :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by
  intro R _ _ n ν _ g hg f hf
  exact Formalism.UG.P.wlocal_main (le_refl n) ν n 0 (by omega) g g⁻¹ (Matrix.nonsing_inv_mul g hg)
    (fun _ _ hj => absurd hj (Nat.not_lt_zero _)) f hf

end GlobalTheory.TestLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAt
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.WeylLocal

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ w.asIdeal.primeCompl),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

theorem isLocalRing_locRing (w : HeightOneSpectrum (𝓞 K)) : IsLocalRing (locRing w) :=
  IsLocalization.AtPrime.isLocalRing (locRing w) w.asIdeal

theorem ne_zero_of_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∈ w.asIdeal.primeCompl) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have h0 : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact hs (by rw [h0]; exact w.asIdeal.zero_mem)

theorem smul_mem_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a ∈ locRing w) {y : Z}
    (hy : y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  obtain ⟨s, hs, hsy⟩ := hy
  obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp ha
  refine ⟨t * s, mul_mem ht hs, ?_⟩
  have ht0 := ne_zero_of_mem w ht
  have he : (t * s) • (a • y) = r • (s • y) := by
    rw [hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
      ← algebraMap_smul K s, smul_smul, smul_smul]
    congr 1
    rw [map_mul]
    field_simp
  rw [he]
  exact M.smul_mem r hsy

theorem le_locP {Z : Type} [AddCommGroup Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {y : Z} (hy : y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
  ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hy⟩

theorem coord_of_mem_colLat {n : ℕ} (B : GL (Fin n) K) {x : Fin n → K} (hx : x ∈ colLat B) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have h : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        fun a => (B : Matrix (Fin n) (Fin n) K) a j) i =
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) i j := rfl
    rw [h, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hy

theorem coord_of_mem_locP {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) {x : Fin n → K}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ locRing w := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨a, ha⟩ := coord_of_mem_colLat B hsx i
  rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at ha
  refine (mem_locRing w _).mpr ⟨a, s, hs, ?_⟩
  have hs0 := ne_zero_of_mem w hs
  rw [ha]
  field_simp

theorem entries_mem {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B')) (i j : Fin n) :
    ((B⁻¹ * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ locRing w := by
  have hx : (fun a => (B' : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by
    rw [h]
    exact le_locP w _ (Submodule.subset_span ⟨j, rfl⟩)
  exact coord_of_mem_locP w B hx i

theorem exists_lift {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ g₀ : Matrix (Fin n) (Fin n) (locRing w), IsUnit g₀.det ∧
      g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := by
  have h1 := entries_mem w 1 g h
  have h2 := entries_mem w g 1 h.symm
  rw [inv_one, one_mul] at h1
  rw [mul_one] at h2
  let g₀ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let g₁ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have e0 : g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := rfl
  have e1 : g₁.map (algebraMap (locRing w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨g₀, ?_, e0⟩
  have hm : g₀ * g₁ = 1 := by
    apply Matrix.map_injective (f := algebraMap (locRing w) K) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e0, e1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S n n le_rfl ν := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

theorem map_weyl_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) (locRing w)} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl (locRing w) n n le_rfl ν) :
    map (algebraMap (locRing w) K) f ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K _)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine le_locP w _ ⟨_, Submodule.subset_span ⟨v, rfl⟩, ?_⟩
    simp only
    rw [toK_apply, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact smul_mem_locP w _ a.2 hy

theorem sqAct_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) K)
    (h : IsBasisAt w (colLat 1) g) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ (delSq (𝓞 K) n lam).map (toK K _)) :
    sqAct K n lam g f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  obtain ⟨g₀, hu, e0⟩ := exists_lift w g h
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  haveI := isLocalRing_locRing w
  have h1 := map_mem_weyl (algebraMap (𝓞 K) (locRing w)) lam.natW hf₀
  have h2 := GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det (locRing w) n lam.natW (natW_antitone lam) g₀ᵀ (by rwa [Matrix.det_transpose]) _ h1
  have h3 := map_weyl_mem_locP w lam.natW h2
  rw [Formalism.GradedWeylDivisibility.ldtwist_map_rowAct, map_map, ← IsScalarTower.algebraMap_eq, Matrix.transpose_map, e0] at h3
  refine smul_mem_locP w _ ?_ h3
  have hd : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap (locRing w) K).toMonoidHom hu.unit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← e0, Units.coe_map, IsUnit.unit_spec]
    exact ((algebraMap (locRing w) K).map_det g₀).symm
  rw [detPow, hd, ← map_zpow, Units.coe_map]
  exact Subtype.property _

theorem ten_mem_locP (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ}
    (M : ι → Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K)) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (M τ)) :
    ten f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K M) := by
  choose s hs hsf using hf
  refine ⟨∏ τ, s τ, prod_mem fun τ _ => hs τ, Submodule.subset_span ⟨fun τ => s τ • f τ, hsf, ?_⟩⟩
  rw [ten, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact ((Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap.map_smul_of_tower (s τ) (f τ)).symm

theorem polyAction_mem_locP_delStd : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ ι _ n lam w g hg F hF
  have key : ∀ P ∈ delStd K lam, actP lam g P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      have h := actTen K ι n lam g f
      rw [ten] at h
      rw [h]
      exact ten_mem_locP w _ _ fun τ => sqAct_mem_locP w (lam τ) (g τ) (hg τ) (hf τ)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hsF⟩ := hF
  obtain ⟨t, ht, h⟩ := key _ hsF
  rw [LinearMap.map_smul_of_tower] at h
  exact ⟨t * s, mul_mem ht hs, (mul_smul t s (actP lam g F)).symm ▸ h⟩

end GlobalTheory.TestLat.WeylLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAtStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  first | exact @GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | exact GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd | (intros; apply GlobalTheory.TestLat.WeylLocal.polyAction_mem_locP_delStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSelfDualEColLatOne
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat.Inhabitant

theorem colLat_one_eq {K : Type} [Field K] [NumberField K] {n : ℕ} :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (algebraMap (𝓞 K) K).range := by
  rw [colLat_one_eq, Module.Basis.mem_span_iff_repr_mem]
  simp

end GlobalTheory.TestLat.Inhabitant
end
