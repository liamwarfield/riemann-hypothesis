module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalOneSubOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExportAllOfSixInputs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotValuationNatCastLtOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarev

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualityDimOfLocalTheorem
namespace GlobalTheory.BlochKato₂

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem localTheorem_iff (D : D7) : LocalSituation.Conclusion5 D ↔ BlochKatoReduction.adm3 D ∧
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
      LocalSituation.bkARightExact ((D.loc l).PD K) ∧ LocalSituation.bkC ((D.loc l).PD K) :=
  ⟨fun h => ⟨fun l _ K => ⟨(h l K).1, (h l K).2.1, (h l K).2.2.2.1⟩,
      fun l _ K => ⟨(h l K).2.2.1, (h l K).2.2.2.2⟩⟩,
    fun h l _ K => ⟨(h.1 l K).1, (h.1 l K).2.1, (h.2 l K).1, (h.1 l K).2.2, (h.2 l K).2⟩⟩

theorem duality_dim_of_localTheorem : ∀ D : D7, LocalSituation.Conclusion5 D → BlochKatoReduction.Gen.adm3 D ∧ BlochKatoReduction.adm3 D :=
  fun D h => ⟨((localTheorem_iff D).1 h).1, ((localTheorem_iff D).1 h).1⟩

end GlobalTheory.BlochKato₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTheoremAllPowersOfSelmerSupLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleIndexBoundAllPowersOfConditions
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.TwistChoice
open scoped TensorProduct

namespace GlobalTheory.TwistChoiceAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem root_pow_prim (i : X.Tw) {k e : ℕ} {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k))
    (he : e < k) : IsPrimitiveRoot ((ζ ^ (X.l i ^ e) : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ (k - e)) := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  rw [Units.val_pow_eq_pow_val]
  refine hζ.pow (pow_pos hl.pos _) ?_
  rw [← pow_add]
  congr 1
  omega

theorem side_root (i : X.Tw) (k : ℕ) {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (b : Bool) :
    IsPrimitiveRoot (((if b then ζ else ζ⁻¹ : (X.Ok i k)ˣ)) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff] at hζ ⊢
  cases b
  · exact hζ.inv
  · exact hζ

theorem zpow_prim (i : X.Tw) (k : ℕ) {a : ℤ} (ha : IsCoprime a (X.l i : ℤ)) :
    IsPrimitiveRoot ((X.zk i k ^ a : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff]
  refine (IsPrimitiveRoot.coe_units_iff.1 (X.zk_prim i k)).zpow_of_gcd_eq_one a ?_
  rw [← Int.isCoprime_iff_gcd_eq_one, Nat.cast_pow]
  exact ha.pow_right

theorem psiOk_partD_root (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k)
    {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Q : Finset (PlE D.host)} (hQ : IsQ P Q) (e : ι → ℕ) {ε : ℝ}
    (he : ∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε)
    (ζ : (X.Ok i k)ˣ) (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (hζm : ζ ∈ Subgroup.zpowers (X.zk i k))
    (ψ' : X.RCG i Q →* (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (hχ : ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M))
    (hψ : ∀ g, ψ' (X.art i Q g) = ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d q g)).val) :
    PsiOk i A0 Q k ψ' ∧ ∑ v ∈ Q, tameVal (X.l i) (ψ'.comp (X.art i Q)) (N.plOm.1 v) ≤ Q.card * ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  have hF : ∀ q, ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1 ≠ 0 ∧
      nval (X.Ok i k) (X.l i) (((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) ≤ ε := by
    intro q
    have := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one (X.Ok i k) (X.l i) (k - e q) hl (by have := (he q).1; omega) (l_ne_zero_Ok i k).1
      (l_not_unit i k).1 _ (root_pow_prim i hζ (he q).1)
    refine ⟨this.1, ?_⟩
    rw [this.2, totient_bound hl (he q).1]
    exact (he q).2
  have hne : ∀ q, ζ ^ (X.l i ^ e q) ≠ 1 := fun q h => (hF q).1 (by rw [h]; simp)
  refine ⟨⟨fun v hv => ?_, ?_, hk, ?_, ?_, fun g => ?_, fun v A hA => ⟨?_, fun hv => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨a, b, c, -⟩ := h.1 q v hq
    exact ⟨a, b, c⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨-, -, -, a, b, -⟩ := h.1 q v hq
    rcases Finset.mem_union.1 hv' with h | h
    · exact a h
    · exact b h
  · refine Subgroup.isOpen_mono (H₁ := (X.art i Q).ker) (fun g hg => ?_) (X.art_cont i Q)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  · intro g g' hg
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv]
  · rw [MonoidHom.comp_apply, hψ]
    exact prod_mem fun q _ => pow_mem (pow_mem hζm _) _
  · rintro ⟨σ, hσ, h1⟩
    by_contra hv
    exact h1 (by rw [MonoidHom.comp_apply, X.art_unr i Q v hv A hA σ hσ, map_one])
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq A hA
    exact ⟨σ, hσ, h1 ▸ hne q⟩
  · intro v hv A hA σ hσ
    rw [hχ, MonoidHom.comp_apply, Y.delU_l i Q M v hv A hA σ hσ, map_one]
  · rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq (N.plOm.1 v) (N.plOm.2 v)
    refine (tameVal_le _ _ _ hσ (h1 ▸ hne q)).trans ?_
    rw [h1]
    exact (hF q).2

theorem admissibleIndexBoundAllPowers_of_conditions (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (N0 : X.Tw → ℕ) (hU : DelUTie bkP.ex) (hAB : PropABCD bkP.ex) (hX : GaloisSideTwistedSelmerAuxiliaryPrimes bkP) (hadm : AdmACD bkP N0) :
    admissibleIndexBoundAllPowers bkP.ex bkP N0 := by
  classical
  intro i hi hS eps' heps F hF A0
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨h1, h2, h3, -, h9, h10⟩ := hadm
  obtain ⟨sNC, sSD, sNJ, sth, sS, sr, -⟩ := hS
  obtain ⟨z, hz⟩ := GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime D N X i
  obtain ⟨R, Dd, M₀, hM₀, hR⟩ := hX i {s | goodS bkP i s}
    (fun s hs => ⟨h1 i hi s, h2 i hi s, sSD s hs, sNJ s hs, sNC, h3, sr⟩)
  choose HE vE hHEo hHEn hvE hE using fun lam => GlobalTheory.ToricFactor.propE D N X N0 h9 h10 i lam z hi (sS lam) (sth lam) hz
  choose HB AB vB nB hHBo hHBn hB using fun y : ↥(Finset.Icc 1 D.R.m) × Bool =>
    hAB i F y.1 y.2 z hi y.1.2 (hF _ y.1.2 _) hz
  have hopen : IsOpen (((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)) : Set (GE N)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite hHEo).inter (isOpen_iInter_of_finite hHBo)
  have hnorm : ((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)).Normal := by
    haveI := Subgroup.normal_iInf_normal hHEn
    haveI := Subgroup.normal_iInf_normal hHBn
    infer_instance
  choose H0 S0 d hd hco using fun M (h : M₀ ≤ M) => hU i M hi (hM₀.trans h)
  choose P hPa hPs hPF using fun M (h : M₀ ≤ M) =>
    hR M h _ _ _ (hd M h) z hz _ hopen hnorm (A0 ∪ Finset.univ.biUnion AB)
  choose Q hQ hQc using fun M (h : M₀ ≤ M) => exists_isQ (P M h)
  choose Fs hFs hFc using fun M (h : M₀ ≤ M) (s : {s // goodS bkP i s}) => hPF M h s.1 s.2 (Q M h) (hQ M h)
  choose fE hfE hfE' using fun M (h : M₀ ≤ M) lam => hE lam M R (P M h) _ (Q M h) (hM₀.trans h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) (Finset.empty_subset _)) (steps_mono (hPs M h) (inf_le_left.trans (iInf_le _ lam))) (hQ M h)
  choose fB hfB hfB' using fun M (h : M₀ ≤ M) y => hB y M R (P M h) (d M h) (Q M h) (hM₀.trans h) (hco M h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) ((Finset.subset_biUnion_of_mem AB (Finset.mem_univ y)).trans Finset.subset_union_right))
    (steps_mono (hPs M h) (inf_le_right.trans (iInf_le _ y))) (hQ M h)
  set C : ℝ := (SigG bkP i).card + 2 * D.R.m + D.R.t * (4 * R) + 1 with hC
  have hCpos : 0 < C := by positivity
  have hεC : C * (eps' / C) = eps' := by field_simp
  have hε : 0 < eps' / C := div_pos heps hCpos
  generalize eps' / C = ε at hε hεC
  have hle : ∀ c : ℝ, c ≤ C → c * ε ≤ eps' := fun c hc => hεC ▸ mul_le_mul_of_nonneg_right hc hε.le
  have c1 : (0 : ℝ) ≤ (SigG bkP i).card := Nat.cast_nonneg _
  have c2 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have c3 : (0 : ℝ) ≤ D.R.t * (4 * R) := by positivity
  have he0 := e_pos (l_ne_zero_Ok i 0).2.2 (l_not_unit i 0).2.2
  obtain ⟨M, hM, k, e, hk, hkM, he, Hev⟩ := exists_level i R Dd (2 + ∑ y, nB y) M₀ {s // goodS bkP i s}
    (X.abelian₂ i ⊕ (↥(Finset.Icc 1 D.R.m) × Bool))
    (nu X i * (IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat) (Sum.elim vE vB) Fs
    (fun M h => Sum.elim (fE M h) (fB M h))
    (fun M h x => by
      obtain ⟨m, hm, hv⟩ := hFc M h x
      exact ⟨m, hm, hv.trans (addVal_l_pow (l_ne_zero_Ok i 0).2.2 _).le⟩)
    (fun M h y => by
      rcases y with lam | y
      · exact ordHyp_mono (hfE M h lam) (Nat.le_add_right _ _)
      · exact ordHyp_mono (hfB M h y)
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)).trans (Nat.le_add_left _ _))) hε
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hu0 : ∀ ζ : (X.Ok i k)ˣ, IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k) →
      ∀ q, (ζ ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 := by
    intro ζ hζ q
    rw [← pow_mul]
    exact ((IsPrimitiveRoot.coe_units_iff.1 hζ).pow_eq_one_iff_dvd _).2
      (Dvd.dvd.mul_left (pow_dvd_pow _ hkM) _)
  have hmem : ∀ q, P M hM q ∈ Q M hM := fun q => (hQ M hM _).2 ⟨q, Or.inl rfl⟩
  let χ₀ : Multiplicative (DelQM D.host (X.l i) (Q M hM) M) →* (X.Ok i k)ˣ :=
    prodChar (X.l i ^ M) (fun q => (⟨P M hM q, hmem q⟩ : ↥(Q M hM))) (fun q => X.zk i k ^ (X.l i ^ e q))
      (hu0 _ (X.zk_prim i k))
  have hχ₀ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, χ₀ (Multiplicative.ofAdd x) =
      ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := fun _ => rfl
  obtain ⟨φ, hφ⟩ := exists_factor bkP.ex i M (Q := Q M hM) (fun v hv => by
    obtain ⟨q, hq⟩ := (hQ M hM v).1 hv
    exact ((hPa M hM).1 q v hq).2.2.2.1)
  refine ⟨Q M hM, k, χ₀.comp φ, fun a ha => ?_⟩
  have hζ := zpow_prim i k ha
  have hζm : X.zk i k ^ a ∈ Subgroup.zpowers (X.zk i k) := Subgroup.zpow_mem_zpowers _ _
  have hχ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, (χ₀ ^ a) (Multiplicative.ofAdd x) =
      ∏ q, ((X.zk i k ^ a) ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := by
    intro x
    rw [MonoidHom.zpow_apply, hχ₀, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun q _ => ?_
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hψχ : ((χ₀.comp φ) ^ a).comp (X.art i (Q M hM)) = (χ₀ ^ a).comp (bkP.ex.delU i (Q M hM) M) := by
    rw [← hφ]
    rfl
  generalize X.zk i k ^ a = ζ at hζ hζm hχ
  generalize χ₀ ^ a = χ at hχ hψχ
  generalize (χ₀.comp φ) ^ a = ψ' at hψχ ⊢
  have hu : ∀ (b : Bool) q, ((if b then ζ else ζ⁻¹) ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 :=
    fun b => hu0 _ (side_root i k hζ b)
  have hψ : ∀ g, ψ' (X.art i (Q M hM) g) =
      ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d M hM (P M hM q) g)).val := by
    intro g
    refine (DFunLike.congr_fun hψχ g).trans ((hχ (Multiplicative.toAdd (bkP.ex.delU i (Q M hM) M g))).trans ?_)
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hco M hM _ (conjCl_of_isQ (hQ M hM))]
  obtain ⟨hok, hD⟩ := psiOk_partD_root bkP.ex (hM₀.trans hM) hk (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M hM) Finset.subset_union_left) (hQ M hM) e he
    ζ hζ hζm ψ' χ hψχ hψ
  refine ⟨hok, ⟨fun _ => ε, fun _ => hε.le, ?_, fun s hs => ?_⟩, fun lam => ?_, ?_,
    M, χ, hψχ, fun _ _ => ε, fun _ _ => hε.le, ?_, fun j hj b Tψ hT hmemT => ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact hle _ (by linarith)
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.side i s))).1 ⟨s, hs⟩
    rw [hFs M hM ⟨s, hs⟩ k _ _ (hu (X.side i s)) (fun g => psiAt_prod _ _ _ _ _ g (hψ g)),
      valE_eq (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne]
    refine ENNReal.ofReal_le_ofReal (hv.trans (le_of_eq ?_))
    congr 1
    rw [Nat.cast_mul, mul_div_assoc, div_self (by exact_mod_cast he0.ne'), mul_one]
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.sideL i lam))).2 (.inl lam)
    have := hfE' M hM lam k _ (psiAt (X.sideL i lam) ψ') (hu (X.sideL i lam)) (fun g => psiAt_prod _ _ _ _ _ _ (hψ g))
    obtain ⟨hx, hvK⟩ := vK_bounds (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne this
    simp only [Sum.elim_inl] at hv hvK
    rw [hvE] at hv
    have h0 := hle 1 (by linarith)
    refine ⟨hx, ?_, ?_⟩
    · rw [hvK]
      exact le_sub_iff_add_le.2 (by rw [neg_add_cancel]; exact nval_nonneg _)
    · rw [hvK]
      linarith
  · have hc : ((Q M hM).card : ℝ) ≤ 4 * R := by
      have := hQc M hM
      rw [Fintype.card_sum, Fintype.card_fin] at this
      exact_mod_cast (by omega : (Q M hM).card ≤ 4 * R)
    refine (mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_right hc hε.le)) (Nat.cast_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact hle _ (by linarith)
  · have := hle (D.R.m * 2) (by linarith)
    simpa [mul_assoc] using this
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ b)).2 (.inr (⟨j, hj⟩, b))
    have := hfB' M hM (⟨j, hj⟩, b) k _ (psiAt b χ) (hu b) (fun x => psiAt_prod _ _ _ _ _ _ (hχ x)) hne Tψ hT hmemT
    simp only [Sum.elim_inr] at hv
    refine this.trans (add_le_add_right ?_ _)
    linarith

end GlobalTheory.TwistChoiceAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSelmerLengthsEqDeterminantValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthKerMatActKmodEqAddValDet
namespace GlobalTheory

open Formalism.MainNotions.BlochKatoReduction Formalism.BasicNotions

theorem matAct_comp_linear {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (f : M →ₗ[R] N)
    (v : Fin n → M) : matAct (M := N) A (fun i => f (v i)) = fun i => f (matAct (M := M) A v i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [matAct, map_sum, map_smul]

theorem matAct_self_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : matAct (M := R) A v = A.mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

private theorem matAct_fractionRing {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (v : Fin n → FractionRing O) :
    matAct (M := FractionRing O) A v = (A.map (algebraMap O (FractionRing O))).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem matAct_fraction_bijective {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Function.Bijective (matAct (M := FractionRing O) A) := by
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = algebraMap O (FractionRing O) A.det := by
    rw [hB, RingHom.map_det]; rfl
  have hU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h
  have hf : ⇑(matAct (M := FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)
  rw [hf]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

theorem nonempty_coker_equiv_ker_matAct {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Nonempty (((Fin n → O) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[O]
      LinearMap.ker (matAct (M := KmodO O) A)) := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O) :=
    LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)
  have he : ∀ x, e x = matAct (M := FractionRing O) A x := fun x => rfl
  have hAι : ∀ y, matAct (M := FractionRing O) A (ι y) = ι (A.mulVec y) := by
    intro y
    have key := matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y
    rw [matAct_self_apply] at key
    exact key
  have hAπ : ∀ x, matAct (M := KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) :=
    fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x
  have hπι : ∀ y, π (ι y) = 0 := by
    intro y
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun hab i)
  have hlift : ∀ x, π x = 0 → ∃ y, ι y = x := by
    intro x hx
    have hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i := by
      intro i
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)
      exact ⟨a, ha⟩
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  let φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O) := π ∘ₗ e.symm.toLinearMap ∘ₗ ι
  have hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro y
    rw [LinearMap.mem_ker]
    show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0
    rw [hAπ, ← he, e.apply_symm_apply, hπι]
  let φ := φ0.codRestrict _ hφ0
  have hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y)) := fun y => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i :=
      fun i => Submodule.Quotient.mk_surjective _ (x i)
    choose k hk using hpre
    have hπk : π k = x := funext hk
    obtain ⟨y, hy⟩ := hlift (matAct (M := FractionRing O) A k) (by
      rw [← hAπ, hπk]
      exact hx)
    refine ⟨y, Subtype.ext ?_⟩
    rw [hφ, hy, ← he, e.symm_apply_apply, hπk]
  have hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      rw [hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]
      rfl
    · intro hy
      have h0 : π (e.symm (ι y)) = 0 := by
        rw [← hφ, hy]
        rfl
      obtain ⟨z, hz⟩ := hlift _ h0
      refine ⟨z, hιinj ?_⟩
      rw [Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩

theorem length_ker_matAct_eq_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (h : A.det = 0) :
    Module.length O (LinearMap.ker (matAct (M := KmodO O) A)) = ⊤ := by
  classical
  by_contra hne
  have hfl := Module.length_ne_top_iff.mp hne
  have : IsNoetherian O (LinearMap.ker (matAct (M := KmodO O) A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hh
    exact hv0 (funext fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let g0 : FractionRing O →ₗ[O] (Fin n → KmodO O) :=
    π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))
  have hg0 : ∀ t, g0 t = π (t • v) := fun t => rfl
  have hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro t
    rw [LinearMap.mem_ker, hg0]
    refine (matAct_comp_linear A
      (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_
    rw [matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]
    funext i
    simp
  let g := g0.codRestrict _ hg0mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g := by
    rintro _ ⟨t, rfl⟩
    have ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ) := by
      rw [Algebra.smul_def]
      field_simp
    rw [ht, map_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O)
    (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht
  have hgt : g t = 0 := by
    have hm : g t ∈ LinearMap.range g := ⟨t, rfl⟩
    rw [hbot] at hm
    exact (Submodule.mem_bot O).mp hm
  have hcomp : π (t • v) i0 = 0 := by
    rw [← hg0]
    exact congrFun (congrArg Subtype.val hgt) i0
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hcomp
  have ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1 := by
    have h1 : algebraMap O (FractionRing O) a = t * v i0 := ha
    rw [h1, ht]
    field_simp
  rw [← map_mul, ← map_one (algebraMap O (FractionRing O))] at ha'
  have hmul : a * ϖ = 1 := IsFractionRing.injective O (FractionRing O) ha'
  have hunit : IsUnit ϖ := ⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  exact hϖ.not_isUnit hunit

theorem length_ker_matAct_kmod_eq_addVal_det :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : ℕ)
      (Φ : Matrix (Fin a) (Fin a) O),
      Module.length O (LinearMap.ker (Formalism.MainNotions.BlochKatoReduction.matAct (M := Formalism.BasicNotions.KmodO O) Φ)) =
        IsDiscreteValuationRing.addVal O Φ.det := by
  intro O _ _ _ a Φ
  by_cases h : Φ.det = 0
  · rw [length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨e⟩ := nonempty_coker_equiv_ker_matAct Φ h
    rw [← e.length_eq]
    exact RelativeLengthSpanDet.length_coker Φ

end GlobalTheory
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.SelDetLength

section Transport

variable {Λ O G M : Type} [CommRing Λ] [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module Λ M]
  [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M] [ContinuousConstSMul O M]
  (ρ : Representation Λ G M) (ρ' : Representation O G M) (h : ∀ g m, ρ g m = ρ' g m)

def trZ : ↥(Z1 ρ) ≃+ ↥(Z1 ρ') where
  toFun z := ⟨z.1, z.2.1, fun g g' => by rw [← h]; exact z.2.2 g g'⟩
  invFun z := ⟨z.1, z.2.1, fun g g' => by rw [h]; exact z.2.2 g g'⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def trH : H1 ρ ≃+ H1 ρ' :=
  QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup
    (trZ ρ ρ' h) (by
      ext z
      refine (AddSubgroup.mem_map_equiv (f := trZ ρ ρ' h)).trans ?_
      change z.1 ∈ B1 ρ ↔ z.1 ∈ B1 ρ'
      simp only [mem_coboundaries1, h])

theorem trH_mk (z : Z1 ρ) : trH ρ ρ' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (trZ ρ ρ' h z) := rfl

theorem exists_mk (x : H1 ρ) : ∃ z : Z1 ρ, x = Submodule.Quotient.mk z :=
  (Submodule.Quotient.mk_surjective _ x).imp fun _ hz => hz.symm

theorem trH_symm_smul (t : O) (z : Z1 ρ') : (trH ρ ρ' h).symm (t • Submodule.Quotient.mk z) =
    Submodule.Quotient.mk ((trZ ρ ρ' h).symm (t • z)) := rfl

theorem trZ_symm_smul (t : O) (z : Z1 ρ') (g : G) : ((trZ ρ ρ' h).symm (t • z)).1 g = t • z.1 g := rfl

theorem trH_eq_smul (t : O) (w w' : H1 ρ) (z z' : Z1 ρ) (hz : ∀ g, z'.1 g = t • z.1 g)
    (hw : w = Submodule.Quotient.mk z) (hw' : w' = Submodule.Quotient.mk z') : trH ρ ρ' h w' = t • trH ρ ρ' h w := by
  rw [hw, hw', trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext hz)

include h in
theorem exists_smul_cocycle (t : O) (z : Z1 ρ) : ∃ z' : Z1 ρ, ∀ g, z'.1 g = t • z.1 g :=
  ⟨(trZ ρ ρ' h).symm (t • trZ ρ ρ' h z), fun _ => rfl⟩

theorem trH_smul (a : Λ) (t : O) (hat : ∀ m : M, a • m = t • m) (x : H1 ρ) :
    trH ρ ρ' h (a • x) = t • trH ρ ρ' h x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, trH_mk, trH_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext fun g => hat _)

theorem trH_res {J : Type} [Group J] [TopologicalSpace J] (φ : J →* G) (hφ : Continuous φ) (x : H1 ρ) :
    trH (ρ.comp φ) (ρ'.comp φ) (fun g m => h (φ g) m) (resH1 ρ φ hφ x) = resH1 ρ' φ hφ (trH ρ ρ' h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem mem_H1ur_iff (J : Subgroup G) (x : H1 ρ) : x ∈ H1ur ρ J ↔ trH ρ ρ' h x ∈ H1ur ρ' J := by
  have hJ : Continuous J.subtype := continuous_subtype_val
  change resH1 ρ J.subtype hJ x = 0 ↔ resH1 ρ' J.subtype hJ (trH ρ ρ' h x) = 0
  rw [← trH_res, AddEquiv.map_eq_zero_iff]

end Transport

theorem mem_selAll_iff {F Ω Λ O M : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CommRing Λ] [CommRing O]
    [AddCommGroup M] [Module Λ M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul Λ M] [ContinuousConstSMul O M]
    (ρ : Representation Λ (G F Ω) M) (ρ' : Representation O (G F Ω) M) (h : ∀ g m, ρ g m = ρ' g m)
    (A : Formalism.GaloisCohomology.Places F Ω) (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype)))
    (L' : ∀ v, Submodule O (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)))
    (hL : ∀ v, ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ y, y ∈ L v ↔ trH _ _ (fun g m => h (Subgroup.subtype _ g) m) y ∈ L' v)
    (x : H1 ρ) :
    x ∈ Formalism.GaloisCohomology.SelAll ρ A (Formalism.GaloisCohomology.bkCond ρ A l Sig L) ↔
      trH ρ ρ' h x ∈ Formalism.GaloisCohomology.SelAll ρ' A (Formalism.GaloisCohomology.bkCond ρ' A l Sig L') := by
  have hJ : ∀ v, Continuous (Dec (F := F) (A.1 v)).subtype := fun _ => continuous_subtype_val
  refine (mem_Sel ρ _ hJ _ _).trans (Iff.trans (forall_congr' fun v => ?_) (mem_Sel ρ' _ hJ _ _).symm)
  rw [← trH_res]
  unfold Formalism.GaloisCohomology.bkCond
  by_cases h1 : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · simp only [ite_eq_left h1]
    exact hL v h1 _
  · by_cases h2 : v ∈ Sig
    · simp only [ite_eq_right h1, ite_eq_left h2, Submodule.mem_top]
    · simp only [ite_eq_right h1, ite_eq_right h2]
      exact mem_H1ur_iff _ _ _ _ _

theorem mem_span_iff {Λ O W W' : Type} [CommRing Λ] [CommRing O] [AddCommGroup W] [Module Λ W] [AddCommGroup W']
    [Module O W'] (T : W ≃+ W') (χ : Λ → O) (hT : ∀ a x, T (a • x) = χ a • T x) (S : Set W) (S' : Set W')
    (h1 : ∀ x ∈ S, T x ∈ S') (h2 : ∀ (t : O), ∀ y ∈ S', T.symm (t • y) ∈ S) (x : W) :
    x ∈ Submodule.span Λ S ↔ T x ∈ Submodule.span O S' := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (h1 x hx)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := T)]; exact add_mem hx hy
    | smul a x _ hx => rw [hT]; exact Submodule.smul_mem _ _ hx
  · intro hx
    have : ∀ y ∈ Submodule.span O S', ∀ t : O, T.symm (t • y) ∈ Submodule.span Λ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx => exact fun t => Submodule.subset_span (h2 t x hx)
      | zero => intro t; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro t; rw [smul_add, map_add (f := _)]; exact add_mem (hx t) (hy t)
      | smul a x _ hx => intro t; rw [smul_smul]; exact hx _
    simpa using this _ hx 1

theorem length_eq_of_equiv {Λ O V W W' : Type} [CommRing Λ] [CommRing O] [AddCommGroup V] [Module Λ V] [Module O V]
    [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module O W'] (K : Submodule Λ V) (K' : Submodule O V)
    (S : Submodule Λ W) (S' : Submodule O W') (T : W ≃+ W') (e : K ≃ₗ[Λ] S) (hK : ∀ v, v ∈ K' ↔ v ∈ K)
    (hS : ∀ w, w ∈ S ↔ T w ∈ S') (he : ∀ (t : O) (x x' : K), x'.1 = t • x.1 → T (e x').1 = t • T (e x).1) :
    Module.length O S' = Module.length O K' := by
  let f : K' →ₗ[O] S' :=
    { toFun := fun x => ⟨T (e ⟨x.1, (hK _).1 x.2⟩).1, (hS _).1 (e _).2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change T _ = T _ + T _
        rw [← map_add (f := _), ← Submodule.coe_add, ← map_add (f := _)]
        rfl
      map_smul' := fun t x => Subtype.ext (he t _ _ rfl) }
  refine (LinearEquiv.ofBijective f ⟨fun x y hxy => ?_, fun y => ?_⟩).length_eq.symm
  · have := e.injective (Subtype.ext (T.injective (congrArg Subtype.val hxy)))
    exact Subtype.ext (congrArg (fun a : K => a.1) this)
  · obtain ⟨x, hx⟩ := e.surjective ⟨T.symm y.1, (hS _).2 (by simpa using y.2)⟩
    refine ⟨⟨x.1, (hK _).2 x.2⟩, Subtype.ext ?_⟩
    change T (e x).1 = _
    rw [hx]
    simp

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) (k : ℕ)

theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  exact Nat.cast_ne_zero.2 (X.lPrime i).out.ne_zero

theorem phiK_injective : Function.Injective (phiK X i k) := (X.Ok_inj i k).comp (X.O_inj i)

theorem l_not_unit : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) := by
  have := X.Ok_fin i k
  have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  intro h
  have h2 : IsUnit (algebraMap (X.O i) (X.Ok i k) (X.l i)) := by simpa using h
  exact X.O_l i ((isUnit_map_iff _ _).1 h2)

theorem l_frac_ne_zero : ((X.l i : ℕ) : FractionRing (X.Ok i k)) ≠ 0 := by
  intro h
  apply l_ne_zero i
  apply ((IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK_injective i k))
  simp only [Function.comp_apply, map_natCast, map_zero, h]

theorem kmod_torsion (b : KmodO (X.Ok i k)) : ∃ n : ℕ, (X.l i ^ n) • b = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, n, hx⟩ := GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a
  refine ⟨n, ?_⟩
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨x, ?_⟩
  rw [Algebra.linearMap_apply, ← hx, map_natCast, nsmul_eq_mul, mul_comm, Nat.cast_pow]

variable (ψ : GE N →* (X.Ok i k)ˣ)

theorem trep_apply (g : GE N) (x : Fin D.R.r → KmodO (X.Ok i k)) (a : Fin D.R.r) :
    Trep i s k ψ g x a = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) • ∑ b, phiK X i k
      (((Tgl i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) _) a b) • x b := by
  simp [Trep, twRep, matAct, Tgl_coe, Tmat, Finset.smul_sum, smul_smul, mul_assoc]

variable (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))

def intSet : Set (H1 ((Trep i s k ψ).comp (DecV N v).subtype)) :=
  {x | ∃ (z : Z1 ((Trep i s k ψ).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin D.R.r → X.O0 i) (b : KmodO (X.Ok i k)),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin D.R.r → KmodO (X.Ok i k)) g a = phiK X i k (y g a) • b) ∧
      x = Submodule.Quotient.mk z}

set_option maxHeartbeats 1000000 in
theorem bk_le : bk bkP i s k ψ v ≤ Submodule.span (X.Ok i k) (intSet bkP i s k ψ v hv) := by
  rw [bk, dite_eq_left hv]
  refine Submodule.span_mono ?_
  rintro x ⟨z, c, y, hc, hy, hz, rfl⟩
  let Bw := bkP.br i v hv
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK Bw.Kw
  obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL c hc.1.1
  let f : ↥(DecV N v) → Fin D.R.r → X.O0 i := fun g j => Bw.eO.symm ⟨_, hn (Bw.e g) j⟩
  have hf : ∀ g j, Bw.toLL (f g j) = (X.l i : Bw.LL.1) ^ n * c (Bw.e g) j := by
    intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply]
  have hφ : Function.Injective ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k)) :=
    (IsFractionRing.injective _ _).comp (phiK_injective i k)
  have hl1 := l_frac_ne_zero i k
  refine ⟨z, ((X.l i : Bw.LL.1) ^ n) • c, f, Submodule.Quotient.mk (((X.l i : FractionRing (X.Ok i k)) ^ n)⁻¹),
    Submodule.smul_mem _ _ hc, fun g a => (hf g a).symm, fun g j => ?_, rfl⟩
  rw [hz, ← Submodule.Quotient.mk_smul, Algebra.smul_def]
  congr 1
  obtain ⟨m, d, ⟨hd, h1⟩, h2⟩ := hy g j
  have h3 : d * f g j = (X.l i : X.O0 i) ^ n * m := by
    apply GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw
    rw [map_mul, map_mul, hf, map_pow, map_natCast, ← h1]
    ring
  have h4 := congrArg ((algebraMap (X.Ok i k) (FractionRing (X.Ok i k))).comp (phiK X i k)) h3
  rw [map_mul, map_mul, map_pow, map_natCast] at h4
  simp only [RingHom.comp_apply] at h4
  have hd' : algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0 := fun h =>
    hd (hφ (by rw [map_zero]; exact h))
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hl1)]
  apply mul_left_cancel₀ hd'
  rw [h4, ← h2]
  ring

set_option maxHeartbeats 1000000 in
theorem le_bk (hψ : ∀ σ ∈ DecV N v, ψ σ = 1) :
    Submodule.span (X.Ok i k) (intSet bkP i s k ψ v hv) ≤ bk bkP i s k ψ v := by
  rw [bk, dite_eq_left hv]
  refine Submodule.span_le.2 ?_
  rintro x ⟨z, c, f, b, hc, hy, hz, rfl⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, n, hx⟩ := GlobalTheory.BKIntegralToRational.exists_mul_pow_eq (l_not_unit i k) a
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s) f := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle
    convert hc using 1
    funext g j
    rw [← hy, MulEquiv.apply_symm_apply]
  obtain ⟨d, hdd⟩ : ∃ d, d = ((X.l i : ℕ) : X.O0 i) ^ n := ⟨_, rfl⟩
  have hd : d ≠ 0 := hdd ▸ pow_ne_zero _ (l_ne_zero i)
  have hd' : phiK X i k d ≠ 0 := (map_ne_zero_iff _ (phiK_injective i k)).2 hd
  have hd1 : algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d) ≠ 0 := by simpa using hd'
  have hd2 : (bkP.br i v hv).toLL d ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKIntegralToRational.toLL_injective _)).2 hd
  let z' : Z1 ((Trep i s k ψ).comp (DecV N v).subtype) := ⟨fun g j => Submodule.Quotient.mk
        (algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) /
          algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d)),
      continuous_pi fun j => (GlobalTheory.BKIntegralToRational.continuous_div_mk (X.twistBaseCoefficientRing_isAdic i) (phiK X i k) hd hd').comp
        (GlobalTheory.BKIntegralToRational.continuous_of_crys _ _ hf j), fun g h => by
      funext j
      rw [Pi.add_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, trep_apply, hψ g g.2, inv_one, Units.val_one,
        one_smul]
      beta_reduce
      rw [GlobalTheory.BKIntegralToRational.cocycle_of_crys _ _ hf g h j]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← Submodule.mkQ_apply, map_add (f := _), map_sum, map_mul, add_div, Finset.sum_div, mul_div_assoc,
        ← LinearMap.map_smul, Algebra.smul_def]⟩
  have hzz : z = x • z' := by
    apply Subtype.ext
    funext g j
    rw [hz, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
    simp only [z']
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, ← hx]
    congr 1
    simp only [hdd, map_pow, map_natCast] at hd1 ⊢
    field_simp
  rw [hzz, Submodule.Quotient.mk_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', ((bkP.br i v hv).toLL d)⁻¹ • c,
    fun g j => algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k (f g j)) /
          algebraMap _ (FractionRing (X.Ok i k)) (phiK X i k d), Submodule.smul_mem _ _ hc,
    fun g a => ⟨f g a, d, ⟨hd, ?_⟩, mul_div_cancel₀ _ hd1⟩, fun _ _ => rfl, rfl⟩)
  change (bkP.br i v hv).toLL d * (((bkP.br i v hv).toLL d)⁻¹ * c ((bkP.br i v hv).e g) a) = _
  rw [hy, mul_inv_cancel_left₀ hd2]

section Char

variable {M : ℕ} {ι : Type} [Fintype ι] (u : ι → (X.Ok i k)ˣ) (hu : ∀ q, u q ^ (X.l i ^ M) = 1)

def delChar : Del X i M ι →* (X.Ok i k)ˣ where
  toFun δ := ∏ q, u q ^ (Multiplicative.toAdd δ q).val
  map_one' := by simp
  map_mul' δ δ' := by
    have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add]

def lamChar : abelian₂ X i M ι →+* X.Ok i k :=
  MonoidAlgebra.liftNCRingHom (phiK X i k) ((Units.coeHom _).comp (delChar i k u hu)) fun _ _ => Commute.all _ _

theorem lamChar_single (δ : Del X i M ι) (c : X.O0 i) :
    lamChar i k u hu (MonoidAlgebra.single δ c) = phiK X i k c * (delChar i k u hu δ : (X.Ok i k)ˣ) := by
  simp [lamChar, MonoidAlgebra.liftNCRingHom]

theorem lamChar_algebraMap (c : X.O0 i) : lamChar i k u hu (algebraMap _ _ c) = phiK X i k c := by
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, lamChar_single]
  simp

theorem lamChar_of (δ : Del X i M ι) :
    lamChar i k u hu (MonoidAlgebra.of _ _ δ) = (delChar i k u hu δ : (X.Ok i k)ˣ) := by
  rw [MonoidAlgebra.of_apply, lamChar_single]
  simp

theorem lamChar_toLam (F : MvPolynomial ι (X.O0 i)) :
    lamChar i k u hu (toLam X i M ι F) =
      MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.algHom_C, lamChar_algebraMap, MvPolynomial.eval₂_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, MvPolynomial.eval₂_add]
  | mul_X p q hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, toLam, MvPolynomial.aeval_X, map_sub,
      map_one, lamChar_of]
    congr 3
    change ∏ q', u q' ^ _ = _
    rw [Finset.prod_eq_single q (fun q' _ hq' => by simp [Pi.single_eq_of_ne hq']) (by simp)]
    simp only [toAdd_ofAdd, Pi.single_eq_same]
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]

theorem lamChar_delInv (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (hψ : ∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) (g : GE N) :
    lamChar i k u hu ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) := by
  have h : Units.map (lamChar i k u hu).toMonoidHom (delInv i M d g)⁻¹ = ψ g := by
    apply Units.ext
    rw [hψ]
    exact lamChar_of i k u hu (delAll X i M d g)
  rw [← h, map_inv, inv_inv]
  rfl

end Char


set_option maxHeartbeats 1000000 in
theorem length_selT {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [Module Λ (KmodO (X.Ok i k))] (χ : Λ →+* X.Ok i k)
    (hχ : ∀ (c : Λ) (b : KmodO (X.Ok i k)), c • b = χ c • b) (hχ0 : ∀ c, χ (algebraMap (X.O0 i) Λ c) = phiK X i k c)
    (κ : GE N →* Λˣ) (hκ : ∀ g, χ (κ g : Λˣ) = (((ψ g)⁻¹ : (X.Ok i k)ˣ) : X.Ok i k))
    (hψ : TrivAbove ψ (X.l i)) (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ)
    (e : ↥(LinearMap.ker (matAct (M := KmodO (X.Ok i k)) Φ)) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ (KmodO (X.Ok i k)) Q))
    (he : ∀ (f : KmodO (X.Ok i k) →ₗ[Λ] KmodO (X.Ok i k))
      (x x' : ↥(LinearMap.ker (matAct (M := KmodO (X.Ok i k)) Φ)))
      (z z' : Z1 (repOn (Tgl i s) κ (KmodO (X.Ok i k)))),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e x).1 = Submodule.Quotient.mk z → (e x').1 = Submodule.Quotient.mk z') :
    Module.length (X.Ok i k) (selT bkP i s k Q ψ) = IsDiscreteValuationRing.addVal (X.Ok i k) (χ Φ.det) := by
  have h : ∀ g m, repOn (Tgl i s) κ (KmodO (X.Ok i k)) g m = Trep i s k ψ g m := by
    intro g m
    funext c
    rw [trep_apply, ← hκ, ← hχ]
    simp only [← hχ0, ← hχ]
    rfl
  rw [RingHom.map_det, ← GlobalTheory.length_ker_matAct_kmod_eq_addVal_det]
  refine length_eq_of_equiv _ _ _ _ (trH _ _ h) e (fun x => ?_) (fun w => ?_) (fun t x x' hx => ?_)
  · rw [LinearMap.mem_ker, LinearMap.mem_ker]
    refine Eq.congr_left (funext fun c => ?_)
    simp [matAct, hχ]
  · refine mem_selAll_iff _ _ h _ _ _ _ _ (fun v hv y => ?_) w
    have hv' : v ∈ placesOver D.host.E (X.l i) := hv
    rw [le_antisymm (bk_le bkP i s k ψ v hv') (le_bk bkP i s k ψ v hv' (hψ v hv' _ (N.plOm.2 v))), bkOn, dite_eq_left hv']
    refine mem_span_iff _ χ (fun c x => trH_smul _ _ _ c (χ c) (fun m => funext fun j => hχ c (m j)) x) _ _ ?_ ?_ y
    · rintro _ ⟨z, c, y, b, hc, hy, hz, rfl⟩
      exact ⟨trZ _ _ (fun g m => h (Subgroup.subtype _ g) m) z, c, y, b, hc, hy,
        fun g j => (hz g j).trans (by rw [hχ, hχ0]), trH_mk _ _ _ z⟩
    · rintro t _ ⟨z, c, y, b, hc, hy, hz, rfl⟩
      refine ⟨(trZ _ _ (fun g m => h (Subgroup.subtype _ g) m)).symm (t • z), c, y, t • b, hc, hy, fun g j => ?_,
        trH_symm_smul _ _ _ t z⟩
      rw [hχ, hχ0, smul_comm, ← hz]
      exact congrFun (trZ_symm_smul _ _ _ t z g) j
  · have hex := exists_mk (repOn (Tgl i s) κ (KmodO (X.Ok i k))) (e x).1
    refine hex.elim fun z hz => ?_
    let f : KmodO (X.Ok i k) →ₗ[Λ] KmodO (X.Ok i k) :=
      { toFun := fun b => t • b
        map_add' := smul_add t
        map_smul' := fun c b => by rw [RingHom.id_apply, hχ, hχ, smul_comm] }
    refine (exists_smul_cocycle _ _ h t z).elim fun z' hz' => ?_
    have h1 : ∀ c, x'.1 c = f (x.1 c) := fun c => congrFun hx c
    have h2 : ∀ g c, z'.1 g c = f (z.1 g c) := fun g c => congrFun (hz' g) c
    exact trH_eq_smul _ _ h t _ _ z z' hz' hz (he f x x' z z' h1 h2 hz)

theorem twisted_selmer_lengths_eq_determinant_valuation : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    SelmerLengthsByDeterminant bkP := by
  intro D N X bkP i s M ι _ P d Q _ hA _ a Φ hC F hF k u ψ hu hψ
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) (KmodO (X.Ok i k)) := Module.compHom _ (lamChar i k u hu)
  have htr : TrivAbove ψ (X.l i) := fun v hv A hvA σ hσ => by
    rw [hψ]
    exact Finset.prod_eq_one fun q _ => by rw [(hA.2.2 q).2.2.1 v hv A hvA σ hσ]; simp
  rw [sLen, lenN, valE, length_selT bkP i s k ψ (lamChar i k u hu) (fun _ _ => rfl) (lamChar_algebraMap i k u hu)
    (delInv i M d) (lamChar_delInv i k ψ u hu d hψ) htr Q Φ (e _ (kmod_torsion i k))
    (he _ _ (kmod_torsion i k) (kmod_torsion i k)), ← hF, lamChar_toLam]

end GlobalTheory.SelDetLength
end
end

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwExportSup

theorem heckeLaws_of_range (D : D7) (hC : HkComm D) (hO : OffRange D) : HeckeLaws D.nexp := by
  intro i hi
  refine ⟨fun j b k P k' P' h h' => ?_, (hO i hi).2⟩
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · exact (hC i hi j hj b k P k' P' h h').eq
  · haveI := (hO i hi).1 j hj b
    exact LinearMap.ext fun x => Subsingleton.elim _ _

theorem twistTheorem_allPowers_of_selmer_supLattice :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), ThmS (BlochKatoReduction.bk0 D) → ResidualBoundOddPrimes (BlochKatoReduction.bk0 D) → ThmC (BlochKatoReduction.bk0 D) →
      BlochKatoReduction.Gen.AdmACD (BlochKatoReduction.bk0 D) N0 → DelUTie D.nexp → ThURel D.nexp → HkComm D → OffRange D → AllGood D.nexp →
      BlochKatoReduction.Gen.adm8 D.ntw D.nexp → SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
      IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → D.nexp.sig_all → HkSS D →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro D E N0 hS h103 hC hACD hTie hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS
  have hX : GaloisSideTwistedSelmerAuxiliaryPrimes (BlochKatoReduction.bk0 D) :=
    GlobalTheory.TwSys.galois_twisted_selmer_auxprimes_of_matrix_and_bounds D D.nd D.ntw (BlochKatoReduction.bk0 D) hS
      (GlobalTheory.SelDetLength.twisted_selmer_lengths_eq_determinant_valuation D D.nd D.ntw (BlochKatoReduction.bk0 D)) h103 hC
  have hP : PropABCD D.nexp :=
    GlobalTheory.TwistDet.propABCD_of_rel D D.nd D.ntw D.nexp hRel (heckeLaws_of_range D hHC hOff) hGood h8
  have hAB : admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 :=
    GlobalTheory.TwistChoiceAll.admissibleIndexBoundAllPowers_of_conditions D D.nd D.ntw (BlochKatoReduction.bk0 D) N0 hTie hP hX hACD
  have hInt : IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := GlobalTheory.T.admInt_of_sup_laws D E hG hFull hHk hU hT hComm
  have hAlg : IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := GlobalTheory.T.admALG_of_commG_var D hComm
  exact GlobalTheory.exportAll_of_six_inputs D E N0 hAB hInt hAlg hT4 hL3 (GlobalTheory.T.admT3_of_hecke_semisimple D E hInt hAlg hSig hSS)

end GlobalTheory.TwExportSup
end

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.Published

namespace GlobalTheory.TwExportTop

theorem twistAllPowers_of_galoisCohomology_classField :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), LocalSituation.Conclusion5 D → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) → BlochKatoReduction.adm2 D → BlochKatoReduction.adm8 D → AllGood D.nexp → D.nexp.sig_all → BlochKatoReduction.adm9 D N0 → BlochKatoReduction.adm10 D → GlobalTheory.UnivChar.IsUnivChar D.nexp → OffRange D → ThURel D.nexp → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.admT4 D.nexp E → TypeKept E → UnivSup D E → SupG D → SupFull D → SupHk D → CommG D → HkComm D → HkSS D → ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D E N0 h5 h1 h2 h8 hGood hSig h9 h10 hUniv hOff hRel
    hL3 hT4 hT hU hG hFull hHk hComm hHC hSS
  exact GlobalTheory.TwExportSup.twistTheorem_allPowers_of_selmer_supLattice D E N0
    (GlobalTheory.T.selmerPresentationMatrix_of_galois_cohomology hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (GlobalTheory.T.residualSelmerBound_of_auxiliaryPrimes_odd hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (GlobalTheory.T.boundModTwoUniformizerAtTwo_of_chebotarev hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    ⟨h1, h2, (GlobalTheory.BlochKato₂.duality_dim_of_localTheorem D h5).1, h4, h9, h10⟩
    (GlobalTheory.UnivChar.delUTie_of_isUnivChar D.nexp (GlobalTheory.AdmChars.exists_admissible_family D.ntw hRC) hUniv)
    hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS

end GlobalTheory.TwExportTop
