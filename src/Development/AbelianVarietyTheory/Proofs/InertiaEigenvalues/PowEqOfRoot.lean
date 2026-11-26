module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal IsLocalRing Polynomial Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AinfK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem l_res : ((l : ℕ) : ResidueField ↥(OL K)) = 0 := by
  rw [← map_natCast (residue ↥(OL K))]
  exact (residue_eq_zero_iff _).mpr (l_mem_max K)

theorem exists_card : ∃ a : ℕ, a ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ a := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  exact ⟨n, n.ne_zero, by rw [Nat.card_eq_fintype_card, hn]⟩

variable {K} {a : ℕ} [NeZero a]


omit [NeZero a] in
theorem res_pow (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ResidueField ↥(OL K)) : x ^ l ^ a = x := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  rw [← h, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_teich (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ↥(OL K)) :
    ∃ w : ↥(OL K), w ^ l ^ a = w ∧ residue _ w = residue _ x := by
  obtain ⟨_, hc, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete K
  have h1 := one_lt_pow_l l a
  have hm : (X ^ l ^ a - X : (↥(OL K))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨w, hw, hx⟩ := HenselianRing.is_henselian (I := maximalIdeal ↥(OL K)) _ hm x (by
      rw [← residue_eq_zero_iff]; simp [res_pow h]) (by
      change IsUnit (residue _ _)
      have : ((l : ResidueField ↥(OL K))) ^ a = 0 := by rw [l_res, zero_pow (NeZero.ne a)]
      simp [derivative_X_pow, this])
  refine ⟨w, by simpa [sub_eq_zero] using hw, ?_⟩
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

theorem exists_toOm (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : Om l) (hx : x ^ l ^ a = x) :
    ∃ w : ↥(OL K), toOm K w = x := by
  classical
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have h1 := one_lt_pow_l l a
  choose r hr using residue_surjective (R := ↥(OL K))
  choose s hs hs' using fun y => exists_teich h (r y)
  have hinj : Function.Injective fun y => toOm K (s y) := fun y z e => by
    rw [← hr y, ← hr z, ← hs', ← hs', toOm_injective K e]
  have hm : (X ^ l ^ a - X : (Om l)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hmem : ∀ y : Om l, y ∈ (X ^ l ^ a - X : (Om l)[X]).roots.toFinset ↔ y ^ l ^ a = y := fun y => by
    simp [mem_roots hm.ne_zero, sub_eq_zero]
  have hsub : Finset.univ.image (fun y => toOm K (s y)) = (X ^ l ^ a - X : (Om l)[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hmem, ← map_pow, hs]
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, h]
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      rw [Polynomial.natDegree_X_pow_sub_X h1]
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (hsub ▸ (hmem x).2 hx)
  exact ⟨_, hz⟩

theorem hasUnr (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : HasUnr a K :=
  ⟨IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨w, rfl⟩ := exists_toOm h x hx
    exact (w : ↥K.1).2⟩

theorem pow_eq_of_root (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) {x : Om l} (hx : x ∈ K.1) {m : ℕ}
    (h0 : 0 < m) (hm : ¬ l ∣ m) (h1 : x ^ m = 1) : x ^ l ^ a = x := by
  have h2 : (⟨x, hx⟩ : ↥K.1) ∈ OL K := IsIntegral.of_pow h0 (by
    rw [show (⟨x, hx⟩ : ↥K.1) ^ m = 1 from Subtype.ext h1]; exact isIntegral_one)
  set y : ↥(OL K) := ⟨_, h2⟩
  have hy : y ^ m = 1 := Subtype.ext (Subtype.ext h1)
  obtain ⟨k, hk⟩ : ∃ k, l ^ a = k + 1 := ⟨l ^ a - 1, by have := one_lt_pow_l l a; omega⟩
  have hr0 : residue _ y ≠ 0 := ((IsUnit.of_pow_eq_one hy h0.ne').map _).ne_zero
  have hr : residue _ (y ^ k) = 1 := by
    have := res_pow h (residue _ y)
    rw [hk, pow_succ] at this
    rw [map_pow]
    exact mul_right_cancel₀ hr0 (by rw [this, one_mul])
  have hg := mul_geom_sum (y ^ k) m
  rw [← pow_mul, mul_comm k, pow_mul, hy, one_pow, sub_self] at hg
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  have hs : ∑ i ∈ Finset.range m, (y ^ k) ^ i ≠ 0 := fun e => hm (by
    have := congrArg (residue _) e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow (residue _) (y ^ k), hr, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at this
    exact (CharP.cast_eq_zero_iff _ l m).1 this)
  have h3 : y ^ k = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hg).resolve_right hs)
  have h4 : x ^ k = 1 := congrArg (toOm K) h3
  rw [hk, pow_succ, h4, one_mul]

theorem Kunr_eq (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : Kunr l a = K0 K := by
  refine le_antisymm (le_inf (hasUnr h).le (Kunr_le_Kur l a)) ?_
  have key : ∀ c ∈ K0 K, ‖c‖ ≤ 1 → c ∈ Kunr l a := fun c hc h1 => by
    obtain ⟨n, z, ω, hω, rfl⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c hc h1
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    obtain ⟨h2, m, h0, hm, h3⟩ := hω i
    exact IntermediateField.subset_adjoin _ _ (pow_eq_of_root h h2.1 h0 hm h3)
  intro c hc
  rcases le_total ‖c‖ 1 with h1 | h1
  · exact key c hc h1
  · exact inv_mem_iff.1 (key _ (inv_mem hc) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1))


variable (l a) in
theorem free_Wq : Module.Free ℤ_[l] (Wq l a) := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : FaithfulSMul ℤ_[l] (Wq l a) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun u v h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l a) h
    simp only [GlobalTheory.TameFrob.iotaO_algebraMap] at this
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective this)
  infer_instance


variable (l a) in
theorem finrank_Wq : Module.finrank ℤ_[l] (Wq l a) = a := by
  have := free_Wq l a
  have h := (splitEquiv (AlgHom.id ℤ_[l] (Wq l a))).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  simpa using h


attribute [local instance] GlobalTheory.TameFrob.algK GlobalTheory.TameFrob.isFractionRing in
variable (l a) in
theorem finrank_Kunr : Module.finrank ℚ_[l] ↥(Kunr l a) = a := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : IsScalarTower ℤ_[l] (Wq l a) ↥(Kunr l a) := IsScalarTower.of_algebraMap_eq fun u =>
    Subtype.ext (GlobalTheory.TameFrob.iotaO_algebraMap l a u).symm
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing ℤ_[l] ℚ_[l] (Wq l a) ↥(Kunr l a), finrank_Wq]

variable (K)

def fK : ℕ := Module.finrank ℚ_[l] ↥(K0 K)

theorem card_res' : fK K ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ fK K := by
  obtain ⟨a, ha, h⟩ := exists_card K
  have : NeZero a := ⟨ha⟩
  have e : fK K = a := by rw [fK, ← Kunr_eq h, finrank_Kunr]
  rw [e]
  exact ⟨ha, h⟩

instance : NeZero (fK K) := ⟨(card_res' K).1⟩

theorem card_res : Nat.card (ResidueField ↥(OL K)) = l ^ fK K := (card_res' K).2

theorem Kunr_fK : Kunr l (fK K) = K0 K := Kunr_eq (card_res K)

end GlobalTheory.AinfK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVector
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntO

theorem frobenius_integrality_vec_O : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ ι _ _ Y w z h i
  classical
  have key := GlobalTheory.FrobIntegralCoeff.integrality_baseChange (R := ℤ_[l]) (O := O) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) ι Unit
    (Matrix.of fun j (_ : Unit) => z j) Y 1 (Matrix.of fun j (_ : Unit) => w j) (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      refine Matrix.ext fun j u => ?_
      have := congrFun h j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fintype.sum_unique, Pi.add_apply] at this ⊢
      exact this) i ()
  exact key

end GlobalTheory.FrobIntO
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVectorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  first | exact @GlobalTheory.FrobIntO.frobenius_integrality_vec_O | exact GlobalTheory.FrobIntO.frobenius_integrality_vec_O | (intros; apply GlobalTheory.FrobIntO.frobenius_integrality_vec_O <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.LiftStep

theorem ev_eis_mul_mu {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : PiSys l e)
    {ε δ : OCb l} (hε : IsEps ε) (hδ : δ ^ l = ε) :
    ∃ u : Ainf l, IsUnit u ∧ ϖ.ev a (eis l a e) * muOf δ = u * muOf ε := by
  obtain ⟨⟨ξ, hξ, hμ⟩, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  have h : Associated (ϖ.ev a (eis l a e)) ξ := by
    rw [← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]
  obtain ⟨v, hv⟩ := h
  refine ⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩
  rw [hμ, ← hv]
  linear_combination (-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul

section Integral

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)

theorem E_pow_mul_iW (n : ℕ) (f : ZMod a → invE l e (A O K)) (hf : ∀ τ, E K l e ^ n * (f τ : K⟦X⟧) ∈ A O K) :
    inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K f = inclO l O (ϖ.iTot t K fun τ => ⟨_, hf τ⟩) := by
  have h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) := by
    rw [← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  rw [h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]
  congr 1

theorem integral (α β : ℕ) (hL : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) (hM : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) :
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobMat t ϖ P i j) ∧
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ β * frobMatInv t ϖ P i j) ∧
    ∀ y : ME P, y.1 ∈ P.EM α → ∀ i, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * toW t ϖ P y i := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩
  · have hm : (fun τ k => P.mx τ k j) ∈ P.L := mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩
    have h := mem_tot.1 (hL _ hm)
    exact ⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩
  · have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M :=
      mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]
    have h := fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i
    refine ⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩
    simpa [Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm] using h τ
  · have h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K := fun τ => by simpa using mem_tot.1 hy τ i
    refine ⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩
    rw [toW_apply]
    exact (E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm

end Integral

end GlobalTheory.BKGal.LiftStep

theorem GlobalTheory.BKGal.LiftStep.alg_step {S ι : Type} [CommRing S] [Fintype ι] (Ui Ew N Mh : S) (α β : ℕ)
    (hMN : Mh = Ui * Ew ^ (β + α) * N) (Xi : Matrix ι ι S) (m y : ι → S) (Yc : ι → ι → S) (yc : ι → S)
    (hY : ∀ i j, Yc i j = Ew ^ β * Xi i j) (hy : ∀ j, yc j = Ew ^ α * y j) :
    Mh • (Xi *ᵥ (m + y)) = (Matrix.of fun i j => Ui * Ew ^ α * Yc i j) *ᵥ (N • m) +
      fun i => Ui * ∑ j, Yc i j * (N * yc j) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


open GlobalTheory.BKGal.LiftStep in
theorem GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀
  classical
  obtain ⟨u, hu, hEu⟩ := ev_eis_mul_mu a ϖ hε hδ
  have hfr : WittVector.frobenius (muOf δ) = muOf ε := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.1
  obtain ⟨-, hXi, hyI⟩ := integral t ϖ P α β hL hM
  choose cXi hcXi using hXi
  choose cy hcy using hyI y hy
  set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui
  have hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ := by
    rw [mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]
  set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw
  set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN
  set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh
  set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi
  have hMN : Mh = Ui * Ew ^ (β + α) * N := by
    rw [hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]
  have hFN : frobOW l O N = Mh := by
    rw [hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]
  set y' := toW t ϖ P y with hy'
  have hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y') := by
    have h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y' := by
      rw [← phiW_apply]; exact sub_eq_iff_eq_add'.1 hm₀
    rw [← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  set z : ι → OW l O := N • m₀ with hz
  have hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i)) := by
    funext i
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]
  set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j
  set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)
  have heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) := by
    rw [hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j))
      (fun j => inclO l O (cy j)) hcXi hcy]
    congr 2
    · ext i j
      change _ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)
      rw [map_mul, map_mul, map_pow]
      rfl
    · funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, map_mul, map_sum]
      rfl
  have hint := GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector l O ι Y w z heq
  choose c hc using hint
  refine ⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩
  rw [inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]
  congr 1
  funext i
  rw [← frobOW_inclO]
  exact congrArg _ (hc i)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  first | exact @GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | exact GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun i j => ?_⟩
  choose y hy e using ha.2
  choose z hz e' using hb.2
  have hbU : ∀ k l, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hb.1
  refine ⟨∑ k, y i k * (b.1 : Matrix (Fin n) (Fin n) (AL L)) k j + z i j,
    Subring.add_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hbU k j)) (hz i j), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hB : (b.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of z := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e']; ring
  have : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) = (a.1 : Matrix _ _ _) * (b.1 : Matrix _ _ _) := rfl
  rw [this]
  conv_lhs => rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hB]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  refine ⟨Subgroup.inv_mem _ ha.1, fun i j => ?_⟩
  choose y hy e using ha.2
  have hiU : ∀ k l, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := Subgroup.inv_mem _ ha.1
  refine ⟨-(∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j),
    Subring.neg_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hiU i k) (hy k j)), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hinv : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix _ _ _) = 1 := by
    have : (a⁻¹ * a).1 = 1 := by simp
    exact congrArg (fun u : GL (Fin n) (AL L) => (u : Matrix (Fin n) (Fin n) (AL L))) this
  have key : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      -((N : AL L) • (((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * Matrix.of y)) := by
    calc ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1
        = ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - ((a⁻¹).1 : Matrix _ _ _) * (a.1 : Matrix _ _ _) := by rw [hinv]
      _ = _ := by rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]; abel
  have := congrFun (congrFun key i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul] at this
  rw [this]; ring


variable (L n) in
def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitCount

theorem locDeg_mul_ncard (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite ∧
      ∀ w ∈ placesOver E l, locDeg E w * (placesOver E l).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have him : HeightOneSpectrum.asIdeal '' placesOver E l = (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, GlobalTheory.HubLoc.liesOver_of_mem hl hv⟩
    · rintro ⟨hP, hlo⟩
      have hm : ((l : ℕ) : 𝓞 E) ∈ P := by
        have : (l : ℤ) ∈ P.under ℤ := by
          rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
        simpa [Ideal.under, Ideal.mem_comap] using this
      refine ⟨⟨P, hP, ?_⟩, hm, rfl⟩
      rintro rfl
      exact hl.ne_zero (by simpa using hm)
  refine ⟨Set.Finite.of_finite_image (him ▸ Algebra.QuasiFinite.finite_primesOver _) hinj.injOn, fun w hw => ?_⟩
  have := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have := w.isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ), ← him,
    Set.ncard_image_of_injective _ hinj, IsGalois.card_aut_eq_finrank] at h
  rw [← h, mul_comm]
  rfl

section Host
variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  obtain ⟨φ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  apply φ.injective
  rw [GlobalTheory.SplitRowProbe.conj_sqrt, GlobalTheory.SplitRowProbe.conj_sqrt, starRingEnd_self_apply]

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem cInt_coe (x : 𝓞 H.E) : (cInt H x : H.E) = H.conj (x : H.E) := rfl

theorem cInt_cInt (x : 𝓞 H.E) : cInt H (cInt H x) = x :=
  RingOfIntegers.ext (by rw [cInt_coe, cInt_coe, conj_conj])

def cPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap (cInt H).toRingHom (cInt H).surjective w

theorem mem_cPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (cPl H w).asIdeal ↔ cInt H x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : cPl H (cPl H w) = w :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cPl, mem_cPl, cInt_cInt])

theorem isConjPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (cPl H w) := by
  intro x y h
  have : y = cInt H x := RingOfIntegers.ext h
  rw [this, mem_cPl, cInt_cInt]

theorem mem_placesOver_of_conj {l : ℕ} {w w' : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E l)
    (h : IsConjPl H w w') : w' ∈ placesOver H.E l :=
  (h (l : 𝓞 H.E) (l : 𝓞 H.E) (by simp)).1 hw

end Host

theorem columns_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have hgal := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  set C := columns (N := D.nd) D.nbr i s with hC
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun w ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  have h2 : 2 * (locDeg D.host.E w * C.ncard) = 2 * D.R.f := by rw [← h]; ring
  omega

end GlobalTheory.SplitCount

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCountStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitCount in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  exact @_root_.GlobalTheory.SplitCount.columns_count
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOE
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOE
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem invariant_phi_solution_approx (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (c : κ → κ → WCb l) (hc : ∀ i j, c i j ∈ bk.OE) (n : ℕ) :
    ∀ (x b : κ → WCb l), (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) →
      (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) →
      ∀ j, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ x j - v := by
  induction n with
  | zero => exact fun x b _ _ _ j => ⟨0, bk.OE.zero_mem, by simp⟩
  | succ n ih =>
    intro x b hb hx hg j
    obtain ⟨v, x', b', hv, hb', hxv, hx', hg'⟩ := GlobalTheory.T.ladic_descent_step_to_OE l K bk κ x b c hc hb hx hg
    obtain ⟨v', hv', y, hy⟩ := ih x' b' hb' hx' hg' j
    refine ⟨v j + ((l : ℕ) : WCb l) * v', bk.OE.add_mem (hv j) (bk.OE.mul_mem (natCast_mem bk.OE l) hv'), y, ?_⟩
    rw [hxv j]
    linear_combination ((l : ℕ) : WCb l) * hy

theorem invariant_phi_solution_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j) →
    (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∀ j, x j ∈ bk.OE := by
  intro l _ K bk κ _ x c hc hx hg j
  refine (GlobalTheory.T.breuilKisin_OE_stability_properties l K bk).2.1 (x j) fun n => ?_
  exact invariant_phi_solution_approx l K bk κ c hc n x (fun _ => 0) (fun _ => bk.OE.zero_mem)
    (fun j => by rw [add_zero]; exact hx j) hg j

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOEStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_OE_of_invariant_frobenius_solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∀ j, x j ∈ bk.OE := by
  first | exact @GlobalTheory.BSP.invariant_phi_solution_mem_OE | exact GlobalTheory.BSP.invariant_phi_solution_mem_OE | (intros; apply GlobalTheory.BSP.invariant_phi_solution_mem_OE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubring
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_mul_coeff_mem_S : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF τ i
  obtain ⟨w, hw, hF⟩ := hF
  have key : ∀ n, ‖coeff n ((i.factorial : K⟦X⟧) * coeff i (F τ))‖ * wS K e n =
      ‖algebraMap O K (emb t τ (w (i, n)))‖ := fun n => by
    rw [← hF τ i n, wS, ← norm_mul, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1; ring
  rw [mem_S]
  simp only [key]
  refine ⟨fun n => norm_algebraMap_le _, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt_one (K := K) l)
  have h : ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w (i, n) := by
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (f := fun n : ℕ => (i, n)) (fun _ _ _ _ h => by simpa using h)
  rw [Nat.cofinite_eq_atTop] at h
  filter_upwards [h] with n hn
  obtain ⟨c, hc⟩ := hn
  rw [Real.dist_eq, sub_zero, abs_norm, hc, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)) hr

end GlobalTheory.CrysPrism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubringStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ (τ : ZMod a) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (F τ) ∈ S O K e := by
  first | exact @GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | exact GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S | (intros; apply GlobalTheory.CrysPrism.factorial_mul_coeff_mem_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGe
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem pow_dvd_factorial_mul (l r : ℕ) (hl : 1 ≤ l) : l ^ r ∣ (l * r).factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : l * (r + 1) = (l * (r + 1) - 1) + 1 := by
      have : 1 ≤ l * (r + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [h1, Nat.factorial_succ, ← h1, pow_succ, mul_comm (l ^ r) l]
    refine Nat.mul_dvd_mul (Dvd.intro (r + 1) rfl) (ih.trans (Nat.factorial_dvd_factorial ?_))
    rw [Nat.mul_succ]; omega

theorem inclS_mem_SdSet (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (x : (Wq l a)⟦X⟧) :
    inclS t K x ∈ SdSet t K e := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  refine ⟨fun n => ((n / e).factorial : Wq l a) * coeff n x, fun r => ?_, fun τ n => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat (e * (l * r))).subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hlt
    apply hn
    have hle : l * r ≤ n / e := (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; omega)
    obtain ⟨k, hk⟩ := (pow_dvd_factorial_mul l r hl1).trans (Nat.factorial_dvd_factorial hle)
    refine Dvd.dvd.mul_right ⟨(k : Wq l a), ?_⟩ _
    rw [hk]; push_cast; rfl
  · rw [inclS_apply, coeff_toAc, map_mul, map_natCast, map_mul, map_natCast]

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x : (Wq l a)⟦X⟧, inclS t K x ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.inclS_mem_SdSet | exact GlobalTheory.CrysPrism.inclS_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.inclS_mem_SdSet <;> assumption)
end
end
