module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.NormAssemble

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval M p) = aeval (cT σ M) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]
    have hp : ((M ^ k).map σ)ᵀ = ((M.map σ)ᵀ) ^ k := by
      rw [← Matrix.transpose_pow, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    simp only [cT, Matrix.map_smul', hp]
    ext i j; simp [Matrix.transpose_smul]
    left; rw [← hp]; rfl

def toFld {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r) : E[X] →+* Fld Q :=
  AdjoinRoot.mk Q.1

def sr {E : Type} [Field E] [NumberField E] [IsCMField E] (Q : E[X]) (h : IsSelfRecip E Q.natDegree Q) :
    SelfRecip E Q.natDegree := ⟨Q, h⟩

theorem exists_norm_of_factors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → (∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q)) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = aeval γ.val m := by
  intro E _ _ _ n γ hγ hP hself m hy
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  set P := γ.val.charpoly with hPdef
  have hPsep : P.Separable := hP.2.2.1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  have hCH : aeval γ.val P = 0 := Matrix.aeval_self_charpoly _
  have haγ : aeval γ.val a * γ.val = 1 := by
    have := congrArg (aeval γ.val) hab
    simpa [hCH] using this
  have hu : cT σ γ.val * γ.val = 1 := by
    have : cT σ γ.val * 1 * γ.val = 1 := hγ
    simpa using this
  have h1 : γ.val * (γ⁻¹).val = 1 := Units.mul_inv γ
  have hcTa : cT σ γ.val = aeval γ.val a := by
    calc cT σ γ.val = cT σ γ.val * γ.val * (γ⁻¹).val := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = aeval γ.val a * γ.val * (γ⁻¹).val := by rw [hu, haγ]
      _ = aeval γ.val a := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hsr : ∀ Q : S, IsSelfRecip E Q.1.natDegree Q.1 := fun Q =>
    hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2
  have hloc : ∀ Q : S, ∃ fQ : E[X], toFld (sr Q.1 (hsr Q)) fQ *
      invol (sr Q.1 (hsr Q)) (toFld _ fQ) = toFld _ m := by
    intro Q
    obtain ⟨y, hy'⟩ := hy _ (sr Q.1 (hsr Q)) (hmem Q.1 Q.2).2.2
    obtain ⟨fQ, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨fQ, hy'⟩
  choose fQ hfQ using hloc
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : S => Ideal.span {Q.1}) := by
    intro Q Q' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcopS Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun Q => Ideal.Quotient.mk (Ideal.span {Q.1}) (fQ Q))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : ∀ Q : S, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 (fQ Q) := by
    intro Q
    have := congrFun hq Q
    rw [Ideal.quotientInfToPiQuotient_mk] at this
    exact this
  set g := (f.map σ).comp a * f - m with hg
  have hdiv : ∀ Q ∈ S, Q ∣ g := by
    intro Q hQ
    let Q' : SelfRecip E Q.natDegree := sr Q (hsr ⟨Q, hQ⟩)
    have hQP := (hmem Q hQ).2.2
    have ha : toFld Q' a = (alpha Q')⁻¹ := by
      have := congrArg (toFld Q') hab
      rw [map_add (f := _), map_mul, map_mul, map_one] at this
      have hX : toFld Q' X = alpha Q' := AdjoinRoot.mk_X
      have hPz : toFld Q' P = 0 := AdjoinRoot.mk_eq_zero.2 hQP
      rw [hX, hPz, mul_zero, add_zero] at this
      exact eq_inv_of_mul_eq_one_left this
    have hc : toFld Q' ((f.map σ).comp a) = invol Q' (toFld Q' f) := by
      change AdjoinRoot.mk Q'.1 ((f.map σ).comp a) = AdjoinRoot.lift _ _ (eval₂_conj_inv_root Q') (AdjoinRoot.mk Q'.1 f)
      rw [← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_def, eval₂_map]
      change eval₂ _ (toFld Q' a) f = _
      rw [ha]; rfl
    have hfQ' : toFld Q' (fQ ⟨Q, hQ⟩) * invol Q' (toFld Q' (fQ ⟨Q, hQ⟩)) = toFld Q' m := hfQ ⟨Q, hQ⟩
    have hf' : toFld Q' f = toFld Q' (fQ ⟨Q, hQ⟩) := hf ⟨Q, hQ⟩
    have : toFld Q' g = 0 := by
      rw [hg, map_sub, map_mul, hc, hf', mul_comm, hfQ', sub_self]
    exact AdjoinRoot.mk_eq_zero.1 this
  have hprod : (∏ Q ∈ S, Q) ∣ g := Finset.prod_dvd_of_coprime hcopS hdiv
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hPg : P ∣ g := hassoc.symm.dvd.trans hprod
  obtain ⟨k, hk⟩ := hPg
  have hg0 : aeval γ.val g = 0 := by rw [hk, map_mul, hCH, zero_mul]
  refine ⟨aeval γ.val f, ?_, ?_⟩
  · rw [show γ.val * aeval γ.val f = aeval γ.val (X * f) by simp,
      show aeval γ.val f * γ.val = aeval γ.val (f * X) by simp, mul_comm]
  · rw [cT_aeval, hcTa, ← aeval_comp, ← map_mul]
    rw [hg, map_sub] at hg0
    exact sub_eq_zero.1 hg0

end GlobalTheory.NormAssemble
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecInv
open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm


open GlobalTheory.FlagNorm in
theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ordL_mul_of_ne [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_mul_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {d : K} (hd : d ≠ 0) (x : K) :
    (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem gram_eq_mul (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (v : ι → Fin n → K) :
    (Matrix.of fun i j => hform σ H (v i) (v j)) =
      cT σ (Matrix.of fun p i => v i p) * H * Matrix.of fun p i => v i p := by
  ext i j
  simp only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cols_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {ι : Type} (v : ι → Fin n → K) :
    (Matrix.of fun p i => (M *ᵥ v i) p) = M * Matrix.of fun p i => v i p := by
  ext p i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem det_cT (σ : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K) :
    (cT σ T).det = σ T.det := by
  unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem gram_det_change (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b b' : Module.Basis ι K W) :
    ∃ d : K, d ≠ 0 ∧
      (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
        σ d * d * (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set T := b.toMatrix b' with hT
  have hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T := by
    ext p j
    have hs := congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [Matrix.of_apply, ← hs, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]
  have hTT : T * b'.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b'
  have hd : T.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨T.det, hd, ?_⟩
  rw [gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol,
    cT_mul]
  set B := Matrix.of fun p i => (b i : Fin n → K) p
  rw [show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]
  simp only [Matrix.det_mul, det_cT]
  ring

theorem sign_basis [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι K W) (b' : Module.Basis ι' K W) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set e : ι' ≃ ι := b'.indexEquiv b
  have hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) =
      (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e := by
    ext i j
    simp [Module.Basis.reindex_apply]
  obtain ⟨d, hd, hdet⟩ := gram_det_change σ H W (b.reindex e.symm) b'
  rw [hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]

theorem aeval_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    aeval (k⁻¹ * a * k).val Q = (k⁻¹).val * aeval a.val Q * k.val := by
  have hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UnitaryClasses.SgnConj

namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ker_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) =
      (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).comap (Matrix.toLin' k.val) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun y => k.val *ᵥ y) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_zero]

def invEquiv {n : ℕ} (k : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' (k⁻¹).val) (Matrix.toLin' k.val)
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])

theorem map_invEquiv {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).map (invEquiv k : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) := by
  rw [ker_conj, Submodule.map_equiv_eq_comap_symm]
  rfl

theorem sgnOn_conj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K),
    sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  intro K _ _ σ hσ n Q a k
  set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))
  set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))
  let b0 := Module.finBasis K V
  let b'' : Module.Basis (Fin (Module.finrank K V)) K V' :=
    b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))
  have hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K) := by
    intro i
    simp [b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]
  unfold sgnOn gramOn
  rw [sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]
  congr 3
  rw [gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]
  simp only [hb'']
  rw [cols_mulVec, cT_mul]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.UnitaryClasses.SgnConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGLStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  first | exact @GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | exact GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | (intros; apply GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureType
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

open PureTriple

theorem exists_prod_act_comp_eq_one_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  intro E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdA := hA ℂ (RingHom.id ℂ) Function.injective_id
  have hdB := hB ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdA hdB
  simp only [RingHom.id_apply] at hdA hdB
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧
      (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧
      ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ b') := by
    intro T a b hd
    by_cases h0 : ρ = H.rt0
    · exact ⟨a, b, rfl, h0 ▸ hd⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hd τ).1 (h2 τ h)⟩⟩
  obtain ⟨pA, qA, hpqA, hdetA⟩ := key A 1 0 hdA
  obtain ⟨pB, qB, hpqB, hdetB⟩ := key B p q hdB
  obtain ⟨gA, tyA, htyA⟩ := AllClasses.exists_isTypeFn H pA qA
  obtain ⟨gB, tyB, htyB⟩ := AllClasses.exists_isTypeFn H pB qB
  obtain ⟨uA, HA, χA, -, hAH, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hBH, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩ := exists_datum_period hT hL A htyA hdetA uA hAH
  obtain ⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩ := exists_datum_period hT hL B htyB hdetB uB hBH
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH
  choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1
  let GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap
  let GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := fun s =>
    FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap
  have hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hactA s (FA.symm z)
    rw [FA.apply_symm_apply] at e
    exact e
  have hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s := fun s z => by
    have e := hactB s (FB.symm z)
    rw [FB.apply_symm_apply] at e
    exact e
  have hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a)) := fun s a => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPA.1 s a i).symm
  have hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b)) := fun s b => by
    simp only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPB.1 s b i).symm
  have hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z) := fun r s z => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0 := fun r hr z hz => by
    have hr' : (r : E) ≠ 0 := by exact_mod_cast hr
    have e : diagMul tyB (r : E) (FB.symm z) = 0 := by
      have := congrArg FB.symm hz
      simpa [GB] using this
    have e' : FB.symm z = 0 := funext fun k => by
      have := congrFun e k
      simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left ((map_ne_zero (tyB k)).2 hr')
    simpa using congrArg FB e'
  have hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z) := by
    intro i s z
    haveI := (hψ i).isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i)
      (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have := DA.fin
  have := DA.proj
  have := DB.fin
  have := DB.proj
  have hrkA : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hpA, hqA, hpqA]
  haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : DA.La)
  have hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b) := fun i => by
    have hm : Ψ i (FA (PeA a)) ∈ uB.Λ := hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))
    exact ⟨b, by rw [hb, FB.apply_symm_apply]⟩
  choose b hb using hb
  have hrkB : Module.finrank (𝓞 E) DB.La = p + q := by rw [DB.rank, hpB, hqB, hpqB]
  have hni : ¬ LinearIndependent (𝓞 E) b := fun hi => by
    have := hi.fintype_card_le_finrank
    rw [Fintype.card_fin, hrkB] at this
    omega
  obtain ⟨x, hx, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hni
  refine ⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩
  let Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := ∑ i, Ψ i ∘ₗ GA (x i)
  have hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z) := fun z => by
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]
  have hΘa : Θ (FA (PeA a)) = 0 := by
    rw [hΘ]
    calc ∑ i, Ψ i (GA (x i) (FA (PeA a))) = ∑ i, FB (PeB (x i • b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcomm, hb, hGPB]
      _ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]
  have hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z) := fun s z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGAc, hcomm]
  have hΘl : ∀ a', Θ (FA (PeA a')) = 0 := fun a' => by
    obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul hrkA ha a'
    refine hGBinj r hr _ ?_
    rw [← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]
  have hΘ0 : Θ.restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on uA.full fun z hz => ?_
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))
    have ez : z = FA (PeA a') := by rw [ha', FA.apply_symm_apply]
    rw [ez]
    exact hΘl a'
  have hΘz : ∀ z, Θ z = 0 := fun z => LinearMap.congr_fun hΘ0 z
  have hs : Smooth A.t.G.hom := A.ab.smooth
  have hp : IsProper B.t.G.hom := B.ab.proper
  have hr : IsReduced A.t.G.left := isReduced_of_smooth_complex _ A.t.G.hom hs
  refine ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_
  obtain ⟨z, rfl⟩ := uA.ex_onto y
  have hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) =
      uB.ex (∑ i ∈ s, Ψ i (GA (x i) z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]; exact ((uB.ker 0).2 uB.Λ.zero_mem).symm
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]
  rw [hpr, ← hΘ, hΘz, comp_one]
  exact (uB.ker 0).2 uB.Λ.zero_mem

end GlobalTheory.CM.PureHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureTypeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  first | exact @GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | exact GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure | (intros; apply GlobalTheory.CM.PureHom.exists_prod_act_comp_eq_one_of_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffTorusIntegralUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffTorusIntegralUnits
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (φ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, φ (a * y) = M *ᵥ φ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun φ
  let f : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective f := Algebra.leftMulMatrix_injective b
  have hf : f a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hf]
  exact (isIntegral_algHom_iff f hinj).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with hc
  · exact hc.choose_spec.1
  · exact continuous_id

theorem isClosed_UL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
  unfold UL; rw [if_neg hw]
  have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
      (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
  rw [this]
  refine IsClosed.preimage ?_ isClosed_singleton
  unfold cT
  exact ((((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose).matrix_mul continuous_const).matrix_mul
    Units.continuous_val)

def linModel (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) :
    B.A ≃ₗ[K.E] (Fin n → K.E) where
  toFun y i := e.symm (ψ y i)
  invFun v := ψ.symm fun i => e (v i)
  map_add' y z := by
    funext i
    simp
  map_smul' c y := by
    funext i
    simp [hψ c y]
  left_inv y := by
    simp
  right_inv v := by
    funext i
    simp

theorem linModel_mul (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (a : B.A)
    (g : GLw n w) (ha : ∀ y, ψ (a * y) = g.val *ᵥ ψ y) (y : B.A) :
    linModel w e B ψ hψ (a * y) = ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
      linModel w e B ψ hψ y := by
  funext i
  change e.symm (ψ (a * y) i) = _
  rw [ha]
  exact RingHom.map_mulVec e.symm.toRingHom _ _ i

end GlobalTheory.KapOrb.CptInt

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem mem_cptPart_iff_torusOf_mem_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h ∈ twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩, (h ∈ cptPart (twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩) ↔ torusOf w B ψ h.1 ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ w hw K e hbr B Q u x n γ hγ ψ hfit hmod h hh
  set T := twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩ with hTdef
  have hcomm : ∀ t ∈ T, (t : GLw n w) * γ = γ * t := by
    intro t ht
    have := congrArg Subtype.val (show t * ⟨γ, hγ⟩ = ⟨γ, hγ⟩ * (MonoidHom.id (UL n w)) t from ht)
    simpa using this
  have spec : ∀ t ∈ T, ∀ y, ψ ((torusOf w B ψ (t : GLw n w) : B.A) * y) = (t : GLw n w).val *ᵥ ψ y :=
    fun t ht => (GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute E w hw K e B Q u x n γ ψ hfit hmod t t.2 (hcomm t ht)).2
  have specInv : ∀ t ∈ T, ∀ y, ψ ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y) =
      ((t : GLw n w)⁻¹).val *ᵥ ψ y := by
    intro t ht y
    have h1 := spec t ht ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcl := isClosed_UL w hw n
  have hint : ∀ z, z ∈ (algebraMap K.O K.E).range ↔ Valued.v (e z) ≤ 1 := hbr.2.1
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  set φ := linModel w e B ψ hmod.1 with hφ
  have key : ∀ s ∈ T, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) ↔
      torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A := by
    intro s hs
    have hI1 : IsIntegral K.O ((torusOf w B ψ (s : GLw n w) : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (spec s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((torusOf w B ψ (s : GLw n w))⁻¹ : B.Aˣ) : B.A)) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (specInv s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl s]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  have tmul : ∀ s ∈ T, ∀ t ∈ T, torusOf w B ψ ((s * t : UL n w) : GLw n w) =
      torusOf w B ψ (s : GLw n w) * torusOf w B ψ (t : GLw n w) := by
    intro s hs t ht
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, spec s hs, spec t ht, Matrix.mulVec_mulVec]
    simp
  have tinv : ∀ s ∈ T, torusOf w B ψ ((s⁻¹ : UL n w) : GLw n w) = (torusOf w B ψ (s : GLw n w))⁻¹ := by
    intro s hs
    apply torusOf_spec
    intro y
    rw [specInv s hs]
    simp
  have tone : torusOf w B ψ ((1 : UL n w) : GLw n w) = 1 := by
    apply torusOf_spec
    intro y
    simp
  let H' : Subgroup (UL n w) :=
    { carrier := {s | s ∈ T ∧ torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A}
      one_mem' := ⟨T.one_mem, by rw [tone]; exact (intUnits K.O B.A).one_mem⟩
      mul_mem' := by
        rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
        exact ⟨T.mul_mem hs ht, by rw [tmul s hs t ht]; exact (intUnits K.O B.A).mul_mem hs' ht'⟩
      inv_mem' := by
        rintro s ⟨hs, hs'⟩
        exact ⟨T.inv_mem hs, by rw [tinv s hs]; exact (intUnits K.O B.A).inv_mem hs'⟩ }
  constructor
  · intro hc
    have hle : cptPart T ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro s ⟨hs, hsc⟩
      exact ⟨hs, (key s hs).1 hsc⟩
    exact (hle hc).2
  · intro hi
    exact Subgroup.subset_closure ⟨hh, (key h hh).2 hi⟩

end GlobalTheory.KapOrb.CptInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffTorusIntegralUnitsStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_torus_integral_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h ∈ twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩, (h ∈ cptPart (twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩) ↔ torusOf w B ψ h.1 ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  first | exact @GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits | exact GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits | (intros; apply GlobalTheory.KapOrb.CptInt.mem_cptPart_iff_torusOf_mem_intUnits <;> assumption)
end
end
