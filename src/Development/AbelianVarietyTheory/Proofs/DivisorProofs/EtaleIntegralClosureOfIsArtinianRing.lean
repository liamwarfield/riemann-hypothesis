module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegularStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePuncturedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLocaStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocal
open IsLocalRing

namespace GlobalTheory.AnnRegSeq

theorem free_of_free_quotient_map (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) (hf : f ∈ maximalIdeal R)
    (reg : IsSMulRegular A f)
    (hfree : Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) :
    Module.Free R A := by
  set I : Ideal R := Ideal.span {f}
  have hsub : I • (⊤ : Submodule R A) = (I.map (algebraMap R A)).restrictScalars R :=
    Ideal.smul_top_eq_map I
  let e0 : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] (A ⧸ I.map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A)))
  let e : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R ⧸ I] (A ⧸ I.map (algebraMap R A)) :=
    { e0.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show e0 (Ideal.Quotient.mk I c • Submodule.Quotient.mk x) = Ideal.Quotient.mk I c • e0 (Submodule.Quotient.mk x)
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  haveI := hfree
  haveI : Module.Free (R ⧸ I) (A ⧸ I • (⊤ : Submodule R A)) := Module.Free.of_equiv e.symm
  exact free_of_free_quotient hf reg

end GlobalTheory.AnnRegSeq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocalStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → IsSMulRegular A f → Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) → Module.Free R A := by
  first | exact @GlobalTheory.AnnRegSeq.free_of_free_quotient_map | exact GlobalTheory.AnnRegSeq.free_of_free_quotient_map | (intros; apply GlobalTheory.AnnRegSeq.free_of_free_quotient_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
open IsLocalRing TensorProduct

namespace GlobalTheory.PurityComplete

variable (R : Type) [CommRing R] [IsRegularLocalRing R]

theorem algebraMap_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hr

theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem modDepthGE_two_baseChange (A : Type) [CommRing A] [Algebra R A]
    (h : ReciprocityTheory.CA.ModDepthGE R A 2) :
    ReciprocityTheory.CA.ModDepthGE (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[R] A) 2 := by
  obtain ⟨rs, hl, hm, hreg⟩ := h
  refine ⟨rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)), by simp [hl], ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact algebraMap_mem_maximalIdeal R (hm s hs)
  · haveI := faithfullyFlat_adicCompletion R
    exact hreg.of_faithfullyFlat_of_isBaseChange (S := AdicCompletion (maximalIdeal R) R)
      (TensorProduct.isBaseChange R A (AdicCompletion (maximalIdeal R) R))

theorem etale_baseChange (A : Type) [CommRing A] [Algebra R A]
    (he : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A))
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : P ≠ maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    Algebra.Etale (Localization.AtPrime P)
      (TensorProduct (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime P)
        (AdicCompletion (maximalIdeal R) R ⊗[R] A)) := by
  set C := AdicCompletion (maximalIdeal R) R
  set p : Ideal R := P.comap (algebraMap R C) with hpdef
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, ← hpdef, h]
  haveI := he p hp
  haveI : P.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] A) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime P ⊗[C] (C ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R C (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  exact Algebra.Etale.of_equiv e

theorem free_of_free_baseChange (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : Module.Free (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) R ⊗[R] A)) :
    Module.Free R A := by
  haveI := faithfullyFlat_adicCompletion R
  haveI : Module.Flat R A := Module.Flat.of_flat_tensorProduct R A (AdicCompletion (maximalIdeal R) R)
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.PurityComplete

namespace GlobalTheory.PurityStep

theorem purityFree_of_complete :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S →
        ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  intro R _ _ H A _ _ _ hd he
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  have hC := H (AdicCompletion (maximalIdeal R) R) inferInstance (UpperTheory.V.CA.g_dimcpl R)
  refine GlobalTheory.PurityComplete.free_of_free_baseChange R A ?_
  exact hC _ (GlobalTheory.PurityComplete.modDepthGE_two_baseChange R A hd)
    (fun P _ hP => GlobalTheory.PurityComplete.etale_baseChange R A he P hP)

end GlobalTheory.PurityStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocalStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.purityFree_of_complete_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S → ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  first | exact @GlobalTheory.PurityStep.purityFree_of_complete | exact GlobalTheory.PurityStep.purityFree_of_complete | (intros; apply GlobalTheory.PurityStep.purityFree_of_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePunctured
open IsLocalRing

namespace GlobalTheory.PurityStep

theorem finite_quot (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem lowDim (R : Type) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    PurityFree R := by
  intro A _ _ _ hA _
  refine GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_
  have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [h1]; exact_mod_cast h
  exact_mod_cast this

theorem hyperplane (R : Type) [CommRing R] [IsRegularLocalRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (hd : 3 ≤ ringKrullDim R) (f : R)
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span {f})]
    (hP : PurityFree (R ⧸ Ideal.span {f})) : PurityFree R := by
  intro A _ _ _ hA het
  have h3 := GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular R hc hd f hf hf2 hP A hA het
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  have hreg := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0
  haveI := finite_quot R A f
  exact GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular R A f hf hreg 2 h3) (GlobalTheory.T.etale_quotient_of_etale_punctured' R A f het))

theorem purityFree_of_ringKrullDim (n : ℕ) : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
    ringKrullDim S = n → PurityFree S := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact lowDim S (by rw [hS]; norm_num)
  | succ n ih =>
    intro S _ _ hS
    by_cases h2 : n + 1 ≤ 2
    · exact lowDim S (by rw [hS]; exact_mod_cast h2)
    refine GlobalTheory.T.purityFree_of_complete_regularLocal S fun S' _ _ hc hd' => ?_
    rw [hS] at hd'
    have hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2 := by
      intro h
      have h0 := GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h
      have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)
      rw [this] at hd'
      exact absurd hd' (by norm_cast)
    obtain ⟨f, hf, hf2⟩ := Set.not_subset.mp hsq
    haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf
    haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
    have hdim := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2
    have hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (S' ⧸ Ideal.span {f}) := IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hsp, hd'] at hdim
    have hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n := by
      have : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 := by
        exact_mod_cast hdim
      omega
    refine hyperplane S' hc ?_ f hf hf2 (ih _ ?_)
    · rw [hd']; exact_mod_cast (by omega : 3 ≤ n + 1)
    · rw [← hsp, hk]

theorem free_of_etale_punctured : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hd het
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  refine purityFree_of_ringKrullDim _ R hreg.symm A (GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' R A (le_trans (by norm_num) hd)) het

end GlobalTheory.PurityStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_of_etale_on_punctured_spectrum : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  first | exact @GlobalTheory.PurityStep.free_of_etale_punctured | exact GlobalTheory.PurityStep.free_of_etale_punctured | (intros; apply GlobalTheory.PurityStep.free_of_etale_punctured <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfIsIntegrallyClosed
open IsLocalRing

namespace GlobalTheory.PurFree

theorem span_succAbove_eq_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}
    (e : Fin (k + 1) → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin (k + 1) → R)
    (ha : ∑ i, a i • e i = 0) (j : Fin (k + 1)) (hj : IsUnit (a j)) :
    Submodule.span R (Set.range (e ∘ j.succAbove)) = ⊤ := by
  set N := Submodule.span R (Set.range (e ∘ j.succAbove))
  have hsa : ∀ i : Fin k, e (j.succAbove i) ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hej : e j ∈ N := by
    rw [Fin.sum_univ_succAbove _ j] at ha
    obtain ⟨u, hu⟩ := hj
    have h1 := eq_neg_of_add_eq_zero_left ha
    have : e j = -(↑u⁻¹ : R) • ∑ i : Fin k, a (j.succAbove i) • e (j.succAbove i) := by
      calc e j = ((↑u⁻¹ : R) * a j) • e j := by rw [← hu, Units.inv_mul, one_smul]
        _ = (↑u⁻¹ : R) • (a j • e j) := mul_smul _ _ _
        _ = _ := by rw [h1, smul_neg, neg_smul]
    rw [this]
    exact N.smul_mem _ (N.sum_mem fun i _ => N.smul_mem _ (hsa i))
  rw [eq_top_iff, ← he, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨i', rfl⟩
  · rw [h]; exact hej
  · exact hsa i'

theorem exists_span_fin_pred {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)
    (e : Fin n → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin n → R)
    (ha : ∑ i, a i • e i = 0) (j : Fin n) (hj : IsUnit (a j)) :
    ∃ e' : Fin (n - 1) → M, Submodule.span R (Set.range e') = ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := j.pos; omega⟩
  exact ⟨e ∘ j.succAbove, span_succAbove_eq_top e he a ha j hj⟩

theorem free_of_relations {R M : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (x y : R)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hrel : ∀ (n : ℕ) (e : Fin n → M), Submodule.span R (Set.range e) = ⊤ →
      ∀ a : Fin n → R, ∑ i, a i • e i = 0 → (∀ i, a i ∈ maximalIdeal R) →
      ∃ b c : Fin n → R, ∑ i, b i • e i = 0 ∧ ∑ i, c i • e i = 0 ∧ a = x • b + y • c) :
    Module.Free R M := by
  classical
  have hex : ∃ n, ∃ e : Fin n → M, Submodule.span R (Set.range e) = ⊤ := Module.Finite.exists_fin
  obtain ⟨e, he⟩ := Nat.find_spec hex
  have hmin : ∀ a : Fin (Nat.find hex) → R, ∑ i, a i • e i = 0 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha j
    by_contra hj
    have hu : IsUnit (a j) := by
      by_contra h'
      exact hj ((IsLocalRing.mem_maximalIdeal _).mpr h')
    have hle := Nat.find_min' hex (exists_span_fin_pred _ e he a ha j hu)
    have := j.pos
    omega
  let f := Fintype.linearCombination R e
  have hK : LinearMap.ker f ≤ maximalIdeal R • LinearMap.ker f := by
    intro a ha
    have ha' : ∑ i, a i • e i = 0 := by
      rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha; exact ha
    obtain ⟨b, c, hb, hc, rfl⟩ := hrel _ e he a ha' (hmin a ha')
    refine Submodule.add_mem _ (Submodule.smul_mem_smul hx ?_) (Submodule.smul_mem_smul hy ?_)
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]; exact hb
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]; exact hc
  have hbot : LinearMap.ker f = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
      (IsNoetherian.noetherian _) hK
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, he]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hbot, hsurj⟩)

theorem relations_of_koszul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (x y : R)
    (hK : ∀ B C : M, x • B + y • C = 0 → ∃ w : M, B = y • w ∧ C = -(x • w))
    (n : ℕ) (e : Fin n → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin n → R)
    (ha : ∑ i, a i • e i = 0) (hai : ∀ i, a i ∈ Ideal.span {x, y}) :
    ∃ b c : Fin n → R, ∑ i, b i • e i = 0 ∧ ∑ i, c i • e i = 0 ∧ a = x • b + y • c := by
  have hbc : ∀ i, ∃ p q : R, p * x + q * y = a i := fun i => Ideal.mem_span_pair.mp (hai i)
  choose b c hbc using hbc
  have hsum : x • (∑ i, b i • e i) + y • (∑ i, c i • e i) = 0 := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul, ← hbc i, mul_comm x, mul_comm y]
  obtain ⟨w, hB, hC⟩ := hK _ _ hsum
  have hw : w ∈ Submodule.span R (Set.range e) := he ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := Submodule.mem_span_range_iff_exists_fun R |>.mp hw
  refine ⟨b - y • d, c + x • d, ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib]
    rw [hB, ← hd, Finset.smul_sum]
    simp [mul_smul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
    rw [hC, ← hd, Finset.smul_sum]
    simp [mul_smul]
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hbc i]
    ring

theorem two_le_height_of_comap (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] [FaithfulSMul R A] (h2 : ringKrullDim R = 2)
    (P : Ideal A) (hPp : P.IsPrime) (hP : P.comap (algebraMap R A) = maximalIdeal R) :
    2 ≤ P.height := by
  have hm : (maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [h2] at this
    exact WithBot.coe_injective (this.trans rfl)
  have hmbot : maximalIdeal R ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hm
    exact absurd hm (by decide)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  have hqp : q.IsPrime := hq.1.1
  have hq1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  have hqne : q ≠ maximalIdeal R := by
    rintro rfl
    rw [hm] at hq1
    exact absurd hq1 (by decide)
  have hqbot : q ≠ ⊥ := by
    intro h
    have := hq.1.2
    rw [h, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at this
    exact hx0 this
  haveI : P.LiesOver (maximalIdeal R) := ⟨hP.symm⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := maximalIdeal R) P hqm
  have hQq : Q.comap (algebraMap R A) = q := hQo.over.symm
  have hQlt : Q < P := by
    refine lt_of_le_of_ne hQP ?_
    rintro rfl
    exact hqne (hQq.symm.trans hP)
  have hQbot : Q ≠ ⊥ := by
    rintro rfl
    apply hqbot
    rw [← hQq]
    ext z
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R A))
  have h1 : 1 ≤ Q.height := by
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hQbot
  have h3 : Q.height + 1 ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Q.height + 1 := by gcongr
    _ ≤ P.height := h3

theorem koszul_of_height (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [Algebra R A] [FaithfulSMul R A]
    (x y : R) (hm : maximalIdeal R = Ideal.span {x, y}) (hx : x ≠ 0)
    (hP : ∀ P : Ideal A, P.IsPrime → P.comap (algebraMap R A) = maximalIdeal R → 2 ≤ P.height)
    (B C : A) (h : x • B + y • C = 0) : ∃ w : A, B = y • w ∧ C = -(x • w) := by
  have hX : algebraMap R A x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hx
  rw [Algebra.smul_def, Algebra.smul_def] at h
  have hdvd : algebraMap R A x ∣ C := by
    refine GlobalTheory.dvd_of_forall_height_eq_one hX fun p _ hp1 hXp => ?_
    by_cases hYp : algebraMap R A y ∈ p
    · exfalso
      have hcomap : p.comap (algebraMap R A) = maximalIdeal R := by
        apply le_antisymm
        · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance))
        · rw [hm, Ideal.span_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hXp
          · exact hYp
      have h2 := hP p inferInstance hcomap
      rw [hp1] at h2
      exact absurd h2 (by decide)
    · exact ⟨algebraMap R A y, hYp, ⟨-B, by linear_combination h⟩⟩
  obtain ⟨w', hw'⟩ := hdvd
  refine ⟨-w', ?_, ?_⟩
  · have h0 : algebraMap R A x * (B + algebraMap R A y * w') = 0 := by
      rw [hw'] at h
      linear_combination h
    have h1 := (mul_eq_zero.mp h0).resolve_left hX
    rw [Algebra.smul_def]
    linear_combination h1
  · rw [Algebra.smul_def, hw']
    ring

theorem free_of_isIntegrallyClosed : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ringKrullDim R ≤ 2 → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hdim
  classical
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have hinj := FaithfulSMul.algebraMap_injective R A
  have hreg' : ∀ r : R, r ≠ 0 → ∀ v : A, r • v = 0 → v = 0 := by
    intro r hr v hv
    rw [Algebra.smul_def] at hv
    exact (mul_eq_zero.mp hv).resolve_left ((map_ne_zero_iff _ hinj).mpr hr)
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  have hn : s.card ≤ 2 := by
    have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 2 := hreg ▸ hdim
    rw [← hs] at h1
    exact_mod_cast h1
  have one : ∀ y : R, maximalIdeal R = Ideal.span {y} → Module.Free R A := by
    intro y hy
    have hym : y ∈ maximalIdeal R := hy ▸ Ideal.mem_span_singleton_self y
    refine free_of_relations (0 : R) y (zero_mem _) hym ?_
    intro n e _ a ha hai
    by_cases hy0 : y = 0
    · refine ⟨0, 0, by simp, by simp, ?_⟩
      funext i
      have := hai i
      rw [hy, hy0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
      simp [this]
    · have hc : ∀ i, ∃ c, a i = c * y := fun i => by
        have := hai i
        rw [hy, Ideal.mem_span_singleton'] at this
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hc.symm⟩
      choose c hc using hc
      refine ⟨0, c, by simp, ?_, ?_⟩
      · apply hreg' y hy0
        rw [Finset.smul_sum, ← ha]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc i, smul_smul, mul_comm]
      · funext i
        simp [hc i, mul_comm]
  obtain h0 | h1 | h2 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  · refine one 0 ?_
    rw [← hspan, Finset.card_eq_zero.mp h0]
    simp
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp h1
    refine one y ?_
    rw [← hspan]
    simp [Ideal.span]
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    have hm : maximalIdeal R = Ideal.span {x, y} := by
      rw [← hspan]
      simp [Ideal.span]
    have h2dim : ringKrullDim R = 2 := by
      rw [← hreg, ← hs, h2]
      rfl
    have hx0 : x ≠ 0 := by
      rintro rfl
      have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton y)
      rw [Set.ncard_singleton] at hle
      have : Submodule.span R {y} = maximalIdeal R := by
        rw [hm]; simp [Ideal.span]
      rw [this, ← hs, h2] at hle
      omega
    have hxm : x ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
    have hym : y ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
    refine free_of_relations x y hxm hym ?_
    intro n e he a ha hai
    exact relations_of_koszul x y
      (koszul_of_height R A x y hm hx0 fun P hP hc => two_le_height_of_comap R A h2dim P hP hc)
      n e he a ha (fun i => hm ▸ hai i)

end GlobalTheory.PurFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeOfHeightOne
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_under p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPrimeTensorIsDomainIsIntegrallyClosedFaithfulS
open IsLocalRing

namespace GlobalTheory

theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFractionFieldOfEtaleHeightOne
open IsLocalRing

namespace GlobalTheory

theorem etale_fractionField_of_etale_height_one :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A]
      [Algebra R A], ¬ IsField R →
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
        (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) A) := by
  intro R A _ _ _ _ _ _ hR h

  have hm : maximalIdeal R ≠ ⊥ := fun hm => hR ((isField_iff_maximalIdeal_eq).mpr hm)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  haveI hP : P.IsPrime := hPmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  have hPne : P ≠ ⊥ := fun e => hx0 (by simpa [e] using hxP)
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin)
    (Order.one_le_iff_ne_zero.mpr (fun e => hPne (Ideal.height_eq_zero_iff_eq_bot.mp e)))
  haveI := h P h1
  set K := Localization.AtPrime (⊥ : Ideal R)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
      intro hb
      have hb' : (y : R) = 0 := Ideal.mem_bot.mp hb
      exact y.2 (by rw [hb']; exact P.zero_mem)
    exact IsLocalization.map_units K (⟨y, hy⟩ : (⊥ : Ideal R).primeCompl)
  letI : Algebra (Localization.AtPrime P) K :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) K :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change _ = IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit _
      rw [IsLocalization.lift_eq])
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) K K A)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing
open IsLocalRing

namespace GlobalTheory.BranchPurity

theorem dim_lt (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ maximalIdeal R) : ringKrullDim (Localization.AtPrime p) < ringKrullDim R := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, ← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_lt_coe.mpr (Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp))

theorem regular_localization (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) (p : Ideal R) [p.IsPrime] :
    ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  haveI : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  exact (IsRegularRing.isRegularLocalRing_localization p).spanFinrank_maximalIdeal

theorem integrallyClosed (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) : IsIntegrallyClosed R := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2

theorem not_isField_localization (R : Type) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) : ¬ IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  intro h
  apply hp
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  exact (Ideal.map_eq_bot_iff_of_injective hinj).mp h

theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ (n : ℕ) (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (maximalIdeal R).spanFinrank = n → (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R A _ _ _ _ _ _ _ _ _ _ hn hR hF hA
  haveI : IsIntegrallyClosed R := integrallyClosed R hR
  have hfree : Module.Free R A := by
    by_cases h2 : ringKrullDim R ≤ 2
    · exact GlobalTheory.PurFree.free_of_isIntegrallyClosed R A hR h2
    · refine GlobalTheory.T.free_of_etale_on_punctured_spectrum R A hR ?_ ?_
      · rw [not_le] at h2
        have h2' : ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim R := by exact_mod_cast h2
        rw [← hR] at h2' ⊢
        have : 2 < (maximalIdeal R).spanFinrank := by exact_mod_cast h2'
        exact_mod_cast this
      · intro p _ hp
        by_cases hb : p = ⊥
        · subst hb
          exact GlobalTheory.etale_fractionField_of_etale_height_one R A hF hA
        obtain ⟨hdom, hic, hfs⟩ := GlobalTheory.atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul R A p
        have hlt := dim_lt R p hp
        have hreg := regular_localization R hR p
        refine IH (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_ (Localization.AtPrime p)
          (TensorProduct R (Localization.AtPrime p) A) rfl hreg (not_isField_localization R p hb)
          (GlobalTheory.etale_localization_atPrime_of_height_one R A p hA)
        rw [← hreg, ← hR, hn] at hlt
        exact_mod_cast hlt
  exact GlobalTheory.PurityDisc.etale_of_etale_height_one R A hF hA

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hR _ hF hA
  exact finiteRing_sq_sub_mul_sq_eq_of_card _ R A rfl hR hF hA

end GlobalTheory.BranchPurity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRingStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.BranchPurity.etale_of_etale_height_one | exact GlobalTheory.BranchPurity.etale_of_etale_height_one | (intros; apply GlobalTheory.BranchPurity.etale_of_etale_height_one <;> assumption)
end
end

open IsLocalRing

namespace GlobalTheory.PurityProd

theorem etale_of_etale_atMaximal {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale (Localization.AtPrime (maximalIdeal A))
      (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B)) :
    Algebra.Etale A B := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by
      simpa [IsUnit.mem_submonoid_iff] using IsLocalRing.notMem_maximalIdeal.mp hx)
  haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e
  haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) :=
    Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _
  let f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)
  exact Algebra.Etale.of_equiv f

theorem isIntegral_of_forall_apply {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem etale_of_etale_pi {R : Type} [CommRing R] [IsNoetherianRing R] {ι : Type} [Finite ι]
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] [∀ i, Module.Finite R (C i)]
    (h : Algebra.Etale R (∀ i, C i)) (i : ι) : Algebra.Etale R (C i) :=
  ⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end GlobalTheory.PurityProd

namespace GlobalTheory.PurityProd

theorem etale_integralClosure_of_isArtinianRing : ∀ (A E : Type) [CommRing A] [IsRegularLocalRing A]
    [CommRing E] [Algebra A E], IsReduced E → IsArtinianRing E → NoZeroSMulDivisors A E →
    Module.Finite A (integralClosure A E) →
    (∀ (q : Ideal A) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q)
      (TensorProduct A (Localization.AtPrime q) (integralClosure A E))) →
    Algebra.Etale A (integralClosure A E) := by
  intro A E _ _ _ _ hred hart hnz hfin hq
  classical
  by_cases hm : (maximalIdeal A).height ≤ 1
  · exact etale_of_etale_atMaximal (hq (maximalIdeal A) hm)
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  haveI := hdom
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let F : MaximalSpectrum E → Type := fun I => E ⧸ I.asIdeal
  let ψ : E ≃ₐ[A] (∀ I, F I) := (IsArtinianRing.equivPi E).restrictScalars A
  let C : MaximalSpectrum E → Type := fun I => integralClosure A (F I)
  let Ψ : integralClosure A E →ₐ[A] ∀ I, C I := AlgHom.pi fun I =>
    ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict
      (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ψ.injective
      funext I
      exact congrArg Subtype.val (congrFun hxy I)
    · intro l
      refine ⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩
      · exact (isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map
          ψ.symm.toAlgHom
      · funext I
        apply Subtype.ext
        change ψ (ψ.symm fun I => (l I).1) I = (l I).1
        rw [AlgEquiv.apply_symm_apply]
  let Φ : integralClosure A E ≃ₐ[A] ∀ I, C I := AlgEquiv.ofBijective Ψ hΨ
  have hinjF : ∀ I, Function.Injective (algebraMap A (F I)) := by
    intro I
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hne : ψ.symm (Pi.single I 1) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)
    have h0 : a • ψ.symm (Pi.single I 1) = 0 := by
      apply ψ.injective
      rw [map_smul, AlgEquiv.apply_symm_apply, map_zero]
      funext J
      by_cases hJ : J = I
      · subst hJ; simp [Algebra.smul_def, ha]
      · simp [hJ]
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hne
  haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply hinjF I
    exact congrArg Subtype.val hab
  haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I =>
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I =>
    IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)
  haveI hfinC : ∀ I, Module.Finite A (C I) := fun I =>
    Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by
      intro c
      obtain ⟨x, hx⟩ := Φ.surjective (Pi.single I c)
      exact ⟨x, by simp [hx]⟩)
  haveI : ∀ I, Algebra.Etale A (C I) := by
    intro I
    have key := GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing A (C I)
    refine key ?_ ?_ ?_ ?_
    · exact IsRegularLocalRing.spanFinrank_maximalIdeal
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast (le_of_lt (not_le.mp hm))
    · intro hf
      apply hm
      rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]
      exact zero_le_one
    · intro p _ hp
      have h1 := hq p (le_of_eq hp)
      let G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p]
          ∀ J, TensorProduct A (Localization.AtPrime p) (C J) :=
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
          (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)
      haveI : Algebra.Etale (Localization.AtPrime p)
          (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G
      exact etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityProd
