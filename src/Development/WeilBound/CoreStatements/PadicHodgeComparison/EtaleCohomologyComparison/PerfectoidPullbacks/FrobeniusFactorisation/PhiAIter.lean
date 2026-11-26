module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BcTens
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.SmoothModelFiniteLengthLink
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.LsSeqEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseqStatement
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_limit_of_lseq : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W] (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  first | exact @GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | exact GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | (intros; apply GlobalTheory.CompanionTheory.TowerLim.module_finite_lim <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeLimitSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicCompleteTensorFiniteStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicCompleteTensorFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowSmulEqZero
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TensorComplete

section Elementary

variable {A : Type} [CommRing A] (π : A)

theorem smodEq_span_iff {M : Type} [AddCommGroup M] [Module A M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem isAdicComplete_span_iff {M : Type} [AddCommGroup M] [Module A M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_span_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule A M)] := by
        intro m n hmn
        rw [smodEq_span_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_span_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_span_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_span_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

variable {π}

theorem isAdicComplete_of_linearEquiv {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have : e.symm x = 0 := h1 _ fun n => by
      obtain ⟨z, hz⟩ := hx n
      exact ⟨e.symm z, by rw [← map_smul, hz]⟩
    simpa using this
  · obtain ⟨L, hL⟩ := h2 (fun n => e.symm (u n)) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩
    refine ⟨e L, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    exact ⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩

theorem isAdicComplete_prod {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : IsAdicComplete (Ideal.span {π}) M)
    (h' : IsAdicComplete (Ideal.span {π}) M') : IsAdicComplete (Ideal.span {π}) (M × M') := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  obtain ⟨h1', h2'⟩ := (isAdicComplete_span_iff π).1 h'
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · refine Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.1, by rw [← hz]; rfl⟩
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.2, by rw [← hz]; rfl⟩
  · obtain ⟨L, hL⟩ := h2 (fun n => (u n).1) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.1, by simpa using congrArg Prod.fst hz⟩
    obtain ⟨L', hL'⟩ := h2' (fun n => (u n).2) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.2, by simpa using congrArg Prod.snd hz⟩
    refine ⟨(L, L'), fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    obtain ⟨z', hz'⟩ := hL' n
    exact ⟨(z, z'), Prod.ext hz hz'⟩

theorem isAdicComplete_fin_pi {M : Type} [AddCommGroup M] [Module A M]
    (h : IsAdicComplete (Ideal.span {π}) M) (n : ℕ) :
    IsAdicComplete (Ideal.span {π}) (Fin n → M) := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · funext i
    refine h1 _ fun k => ?_
    obtain ⟨z, hz⟩ := hx k
    exact ⟨z i, by rw [← hz]; rfl⟩
  · choose z hz using hu
    have key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L := fun i =>
      h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩
    choose L hL using key
    refine ⟨L, fun k => ?_⟩
    choose w hw using fun i => hL i k
    exact ⟨w, funext hw⟩

theorem isAdicComplete_of_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module A M] (E : ℕ)
    (h : ∀ x : M, π ^ E • x = 0) : IsAdicComplete (Ideal.span {π}) M := by
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · obtain ⟨z, rfl⟩ := hx E
    exact h z
  · have tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k) := by
      intro n k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨w, hw⟩ := hu (n + k)
        refine ⟨z + π ^ k • w, ?_⟩
        rw [smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]
        abel
    refine ⟨u E, fun n => ?_⟩
    obtain ⟨z, hz⟩ := tel n E
    obtain ⟨w, hw⟩ := tel E n
    rw [h w, add_comm E n] at hw
    refine ⟨z, ?_⟩
    rw [hz, ← sub_eq_zero.1 hw.symm]

end Elementary

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

theorem irreducible_dvd_of_not_isUnit {q r : R} (hq : Irreducible q) (hr : ¬IsUnit r) : q ∣ r := by
  have hmax : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq
  have heq : Ideal.span {q} = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← Ideal.mem_span_singleton, heq]
  exact (IsLocalRing.mem_maximalIdeal r).2 hr

theorem exists_pow_smul_directSum_eq_zero {ι : Type} [Fintype ι] (q : ι → R)
    (hq : ∀ i, Irreducible (q i)) (e : ι → ℕ) {r : R} (hr : ¬IsUnit r) :
    ∃ E : ℕ, ∀ x : DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}), r ^ E • x = 0 := by
  classical
  refine ⟨∑ i, e i, fun x => ?_⟩
  refine DFinsupp.ext fun i => ?_
  have hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i} := by
    rw [Submodule.mem_span_singleton]
    have h1 : q i ^ e i ∣ r ^ (∑ i, e i) :=
      (pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans
        (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
  change r ^ (∑ i, e i) • x i = 0
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem _ y hmem

theorem pow_natCast_smul_tensor_eq_zero {O T : Type} [CommRing O] [Algebra R O] [AddCommGroup T]
    [Module R T] (p E : ℕ) (h : ∀ x : T, (p : R) ^ E • x = 0) (t : O ⊗[R] T) :
    (p : O) ^ E • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o x =>
    have h1 : (p : O) ^ E * o = (p : R) ^ E • o := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

end Tensor

theorem isAdicComplete_tensor : ∀ (p : ℕ) [Fact p.Prime] (R O : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [CommRing O] [Algebra R O]
    [IsAdicComplete (Ideal.span {(p : O)}) O],
    (p : R) ≠ 0 → ¬IsUnit (p : R) →
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] N) := by
  intro p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := N)
  obtain ⟨E, hE⟩ := exists_pow_smul_directSum_eq_zero q hq e hp2
  have hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R)) :=
    isAdicComplete_of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans
        (TensorProduct.finsuppScalarRight R O O (Fin n)).symm)
      (isAdicComplete_fin_pi inferInstance n)
  have htors : IsAdicComplete (Ideal.span {(p : O)})
      (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i})) :=
    isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)
  exact isAdicComplete_of_linearEquiv
    ((TensorProduct.prodRight R O O _ _).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm)
    (isAdicComplete_prod hfree htors)

end GlobalTheory.CompanionTheory.TensorComplete
end
end

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorCompleteFinite

open GlobalTheory.CompanionTheory.TensorComplete

theorem isAdicComplete_of_linearEquiv_univ {A : Type} [CommRing A] {π : A} {M : Type} {M' : Type 1}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  have hM : ∀ (n : ℕ) (x : M), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) →
      e x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M).map (e : M →ₗ[A] M') ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  have hM' : ∀ (n : ℕ) (x : M'), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') →
      e.symm x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M').map (e.symm : M' →ₗ[A] M) ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e.symm x = 0 := by
      refine h.toIsHausdorff.haus' (e.symm x) (fun n => ?_)
      rw [SModEq.sub_mem, sub_zero]
      have hx' := (SModEq.sub_mem).mp (hx n)
      rw [sub_zero] at hx'
      exact hM' n x hx'
    simpa using congrArg e h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e.symm (f n)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, ← map_sub]
      exact hM' m _ ((SModEq.sub_mem).mp (hf hmn)))
    refine ⟨e L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have h2 := hM n _ ((SModEq.sub_mem).mp (hL n))
    rwa [map_sub, LinearEquiv.apply_symm_apply] at h2

theorem isAdicComplete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) →
    ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
      (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L],
      IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  intro W _ _ _ l hl A _ _ hA L _ _ _
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hl.ne_zero Nat.cast_zero
  obtain ⟨p, hpmem, hpu⟩ : ∃ p ∈ l.primeFactorsList, ¬IsUnit (p : W) := by
    by_contra hcon
    push_neg at hcon
    apply hl.1
    rw [← Nat.prod_primeFactorsList hl0, Nat.cast_list_prod]
    refine List.prod_isUnit (fun m hm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hcon q hq
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpmem
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactorsList hpmem
  have hmu : IsUnit (m : W) := by
    have h := hl.isUnit_or_isUnit (show (l : W) = (p : W) * (m : W) by rw [hm, Nat.cast_mul])
    exact h.resolve_left hpu
  have hmA : IsUnit (m : A) := by
    have h := hmu.map (algebraMap W A)
    rwa [map_natCast] at h
  have hI : Ideal.span {(l : A)} = Ideal.span {(p : A)} := by
    rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit hmA]
  have hp0 : (p : W) ≠ 0 := by
    intro h
    apply hl.ne_zero
    rw [hm, Nat.cast_mul, h, zero_mul]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hA' : IsAdicComplete (Ideal.span {(p : A)}) A := by
    rw [← hI]
    exact hA
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' W L
  have hN := isAdicComplete_tensor p W A hp0 hpu ((Fin n → W) ⧸ LinearMap.ker f)
  rw [hI]
  exact isAdicComplete_of_linearEquiv_univ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (f.quotKerEquivOfSurjective hf)) hN

end GlobalTheory.CompanionTheory.TensorCompleteFinite
end

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_complete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A] (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L], IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  first | exact @GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | exact GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | (intros; apply GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeLimitSystem
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerExt

section
variable {W : Type} [CommRing W] (l : ℕ) {A : Type} [CommRing A] [Algebra W A]
  {M : Type*} [AddCommGroup M] [Module W M]

theorem pow_smul_tmul (n : ℕ) (a : A) (m : M) :
    ((l : A) ^ n) • (a ⊗ₜ[W] m) = a ⊗ₜ[W] (((l : W) ^ n) • m) := by
  have h : ((l : W) ^ n) • a = (l : A) ^ n * a := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [← TensorProduct.smul_tmul, h, TensorProduct.smul_tmul', smul_eq_mul]

theorem pow_smul_eq_zero (n : ℕ) (h : ∀ x : M, ((l : W) ^ n) • x = 0) (t : A ⊗[W] M) :
    ((l : A) ^ n) • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [pow_smul_tmul, h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem lTensor_pow_smul (n : ℕ) (v : A ⊗[W] M) :
    LinearMap.lTensor A (((l : W) ^ n) • (LinearMap.id : M →ₗ[W] M)) v = ((l : A) ^ n) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [pow_smul_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

theorem mem_pow_smul_top {N : Type*} [AddCommGroup N] [Module A N] (n : ℕ) (v : N) :
    v ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A N) ↔ ∃ u : N, v = ((l : A) ^ n) • u := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Submodule.mem_top, rfl⟩
end

section
variable {W : Type} [CommRing W] (l : ℕ) (S : Sys.{1} W) (A : Type) [CommRing A] [Algebra W A]

theorem r_baseChange_pr (n : ℕ) (w : A ⊗[W] S.lim) :
    (S.r n).baseChange A ((pr S (n + 1)).baseChange A w) = (pr S n).baseChange A w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have hx : S.r n (x.1 (n + 1)) = x.1 n := x.2 n
    simp only [LinearMap.baseChange_tmul]
    change a ⊗ₜ[W] S.r n (x.1 (n + 1)) = a ⊗ₜ[W] x.1 n
    rw [hx]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_eq_pow_smul [Module.Flat W A] (n : ℕ)
    (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : (pr S n).baseChange A w = 0) :
    ∃ v : A ⊗[W] S.lim, w = ((l : A) ^ n) • v := by
  have hex : Function.Exact (((l : W) ^ n) • (LinearMap.id : S.lim →ₗ[W] S.lim)) (pr S n) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hker x hx
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      change (pr S n) (((l : W) ^ n) • y) = 0
      rw [map_smul]
      exact hkill _
  have hw' : (LinearMap.lTensor A (pr S n)) w = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hw
  obtain ⟨v, rfl⟩ := (Module.Flat.lTensor_exact A hex w).1 hw'
  exact ⟨v, lTensor_pow_smul l n v⟩

theorem baseChange_pr_pow_smul (n : ℕ) (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (u : A ⊗[W] S.lim) : (pr S n).baseChange A (((l : A) ^ n) • u) = 0 := by
  rw [map_smul]
  exact pow_smul_eq_zero l n hkill _

theorem exists_baseChange_pr_eq (n c : ℕ)
    (hcok : ∀ (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) (t : A ⊗[W] S.M n) :
    ∃ w : A ⊗[W] S.lim, (pr S n).baseChange A w = ((l : A) ^ c) • t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨y, hy⟩ := hcok m
    refine ⟨a ⊗ₜ[W] y, ?_⟩
    rw [pow_smul_tmul, ← hy, LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    exact ⟨w₁ + w₂, by rw [map_add (f := _), h₁, h₂, smul_add]⟩

theorem eq_zero_of_baseChange_pr [Module.Flat W A]
    [IsHausdorff (Ideal.span {(l : A)}) (A ⊗[W] S.lim)]
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : ∀ n, (pr S n).baseChange A w = 0) : w = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance w fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top]
  exact exists_eq_pow_smul l S A n (hkill n) (hker n) w (hw n)

theorem exists_lift [Module.Flat W A]
    [IsPrecomplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim)] (c : ℕ)
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (hcok : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x)
    (z : ∀ n, A ⊗[W] S.M n) (hz : ∀ n, (S.r n).baseChange A (z (n + 1)) = z n) :
    ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w = ((l : A) ^ c) • z n := by
  choose f hf using fun n => exists_baseChange_pr_eq l S A n c (hcok n) (z n)
  have hstep : ∀ n, f n ≡ f (n + 1) [SMOD ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro n
    rw [SModEq.sub_mem, mem_pow_smul_top]
    refine exists_eq_pow_smul l S A n (hkill n) (hker n) _ ?_
    rw [map_sub, ← r_baseChange_pr S A n (f (n + 1)), hf (n + 1), map_smul, hz, hf n, sub_self]
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {(l : A)}) ^ m • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem] at *
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) ((SModEq.sub_mem).1 (hstep n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance hmono
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, mem_pow_smul_top] at h
  obtain ⟨u, hu⟩ := h
  have h0 : (pr S n).baseChange A (f n - L) = 0 := by
    rw [hu]
    exact baseChange_pr_pow_smul l S A n (hkill n) u
  rw [map_sub, sub_eq_zero, hf n] at h0
  exact h0.symm

end

theorem limit_extension_upTo : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  intro W _ _ _ l hl S c hfin hkill hker hcok A _ _ _ _
  haveI hcompl : IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim) :=
    GlobalTheory.T.adic_complete_tensor_finite W l hl A S.lim
  have hinj := eq_zero_of_baseChange_pr l S A hkill hker
  refine ⟨hinj, ?_⟩
  have hlift : ∀ z : (tens A S).lim, ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w =
      ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := fun z =>
    exists_lift l S A c hkill hker hcok (fun n => z.1 n) fun n => z.2 n
  choose g hg using hlift
  refine ⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hg⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, map_add (f := _), hg, hg, hg]
    exact sub_eq_zero.2 (smul_add ((l : A) ^ c) (x.1 n : A ⊗[W] S.M n) (y.1 n : A ⊗[W] S.M n))
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, RingHom.id_apply, map_smul, hg, hg]
    exact sub_eq_zero.2 (smul_comm ((l : A) ^ c) a (x.1 n : A ⊗[W] S.M n))

end GlobalTheory.CompanionTheory.TowerExt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeLimitSystemStatement
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_base_change_limit_system : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo | exact GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo | (intros; apply GlobalTheory.CompanionTheory.TowerExt.limit_extension_upTo <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.NuPull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem bW_red (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)) :
    (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by apply GlobalTheory.T.witt_comparison_reduction_compat

theorem bW_phi (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n) :
    phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by apply GlobalTheory.T.witt_comparison_frobenius_compat

theorem bW_gal (r : Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ)
    (y : (HSW r M j).M n) : galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by apply GlobalTheory.T.witt_comparison_galois_fixed

theorem bW_pull (r : Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n) :
    pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by apply GlobalTheory.T.witt_comparison_pullback_compat

theorem nu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j) :
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by apply GlobalTheory.T.teichmuller_nu_reduction_compat

theorem nu_phi (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by apply GlobalTheory.T.teichmuller_nu_frobenius_compat

theorem nu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) =
      galM r M σ hσ n j (Mid.nu r M n j hT x) := by apply GlobalTheory.T.teichmuller_nu_galois_compat

theorem nu_pull (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p)
    (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by apply GlobalTheory.T.teichmuller_nu_pullback_compat

theorem mu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) =
      Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by apply GlobalTheory.T.teichmuller_mu_reduction_compat

theorem mu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) =
      Mid.mu r M n j hT (galM r M σ hσ n j t) := by apply GlobalTheory.T.teichmuller_mu_galois_compat

theorem flatW (r : Res l K) : Module.Flat (WittVector l r.k) (AW r) := by apply GlobalTheory.T.witt_acris_flat

theorem adicA : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by apply GlobalTheory.T.acris_isAdicComplete_span_prime

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.ExistsAlpha
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb.Fa

variable {W A : Type} [CommRing W] [CommRing A] [Algebra W A]

def ev {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) : A ⊗[W] L →+ T :=
  TensorProduct.liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun y => a • g y) fun y y' => by rw [map_add (f := _), smul_add])
    fun a a' => AddMonoidHom.ext fun y => add_smul a a' (g y)) fun w a y => by
      change (w • a) • g y = a • g (w • y)
      rw [hg, Algebra.smul_def, mul_comm, mul_smul]

theorem ev_tmul {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) (a : A) (y : L) : ev g hg (a ⊗ₜ y) = a • g y := rfl

theorem ev_smul {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) (a : A) (z : A ⊗[W] L) : ev g hg (a • z) = a • ev g hg z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => rw [TensorProduct.smul_tmul', ev_tmul, ev_tmul, smul_eq_mul, mul_smul]
  | add z z' h h' => rw [smul_add, map_add (f := _), map_add (f := _), h, h', smul_add]

theorem add_ext {L : Type 1} [AddCommGroup L] [Module W L] {T : Type 1} [AddCommGroup T] {f f' : A ⊗[W] L →+ T}
    (h : ∀ a y, f (a ⊗ₜ y) = f' (a ⊗ₜ y)) (z : A ⊗[W] L) : f z = f' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => exact h b y
  | add z z' h h' => rw [map_add (f := _), map_add (f := _), h, h']

theorem ev_bij {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y)
    (h : Tens W (N := fun _ : Unit => A) (M := fun _ => L) (M' := T) fun _ a y => a • g y) : Function.Bijective (ev g hg) := by
  obtain ⟨e, he⟩ := h
  have : ⇑(ev g hg) = e ∘ (fun z => Pi.single () z) := funext fun z =>
    add_ext (f := ev g hg) (f' := e.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Unit => A ⊗[W] L) ())) (fun a y => (he () a y).symm) z
  rw [this]
  exact e.bijective.comp ⟨Pi.single_injective (M := fun _ : Unit => A ⊗[W] L) (), fun f => ⟨f (), funext fun _ => Pi.single_eq_same _ _⟩⟩

theorem core [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ) (hl : Irreducible (l : W)) (S : Sys.{1} W) (c : ℕ) (h1 : Module.Finite W S.lim)
    (h2 : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0) (h3 : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (h4 : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
    (T : Sys.{1} A) (g : ∀ n, S.M n →+ T.M n) (hg : ∀ n (w : W) y, g n (w • y) = algebraMap W A w • g n y)
    (hr : ∀ n y, T.r n (g (n + 1) y) = g n (S.r n y))
    (hb : ∀ n, Tens W (N := fun _ : Unit => A) (M := fun _ => S.M n) (M' := T.M n) fun _ a y => a • g n y)
    (g' : ∀ n, S.lim →+ T.M n) (hg' : ∀ n (w : W) y, g' n (w • y) = algebraMap W A w • g' n y) (e : ∀ n y, g' n y = g n (y.1 n)) :
    (∀ w, (∀ n, ev (g' n) (hg' n) w = 0) → w = 0) ∧
      ∀ z : ∀ n, T.M n, (∀ n, T.r n (z (n + 1)) = z n) → ∃ w, ∀ n, ev (g' n) (hg' n) w = (l ^ c) • z n := by
  obtain ⟨hs, α, hα⟩ := GlobalTheory.T.flat_base_change_limit_system W l hl S c h1 h2 h3 h4 A
  have hev : ∀ n w, ev (g' n) (hg' n) w = ev (g n) (hg n) ((Tw.pr S n).baseChange A w) := fun n =>
    add_ext (f' := (ev (g n) (hg n)).comp ((Tw.pr S n).baseChange A).toAddMonoidHom) fun a y => by
      rw [ev_tmul, e]; rfl
  have hbij := fun n => ev_bij (g n) (hg n) (hb n)
  refine ⟨fun w hw => hs w fun n => (hbij n).1 (by rw [← hev, hw, map_zero]), fun z hz => ?_⟩
  choose u hu using fun n => (hbij n).2 (z n)
  have hc : ∀ n, (S.r n).baseChange A (u (n + 1)) = u n := fun n => (hbij n).1 (by
    rw [hu, ← hz, ← hu]
    exact add_ext (f := (ev (g n) (hg n)).comp ((S.r n).baseChange A).toAddMonoidHom)
      (f' := (T.r n).toAddMonoidHom.comp (ev (g (n + 1)) (hg (n + 1)))) (fun a y => by
        change a • g n (S.r n y) = T.r n (a • g (n + 1) y)
        rw [map_smul, hr]) _)
  refine ⟨α ⟨u, hc⟩, fun n => ?_⟩
  rw [hev, hα, ev_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact congrArg _ (hu n)

theorem exists_alpha {P H : Type 1} [AddCommGroup P] [AddCommGroup H] {T : ℕ → Type 1} [∀ n, AddCommGroup (T n)] (E : ∀ n, P →+ T n)
    (ν : ∀ n, H →+ T n) (k : ℕ) (hs : ∀ w, (∀ n, E n w = 0) → w = 0) (hx : ∀ x, ∃ w, ∀ n, E n w = k • ν n x) :
    ∃ α : H →+ P, ∀ n x, E n (α x) = k • ν n x := by
  choose a ha using hx
  exact ⟨AddMonoidHom.mk' a fun x y => sub_eq_zero.1 (hs _ fun n => by
    rw [map_sub, map_add (f := _), ha, ha, ha, map_add (f := _), nsmul_add, sub_self]), fun n x => ha x n⟩

theorem alpha_op {P H P' H' : Type 1} [AddCommGroup P] [AddCommGroup H] [AddCommGroup P'] [AddCommGroup H'] {T T' : ℕ → Type 1}
    [∀ n, AddCommGroup (T n)] [∀ n, AddCommGroup (T' n)] {E : ∀ n, P →+ T n} {ν : ∀ n, H →+ T n} {k : ℕ} {α : H →+ P}
    (hα : ∀ n x, E n (α x) = k • ν n x) {E' : ∀ n, P' →+ T' n} {ν' : ∀ n, H' →+ T' n} {k' : ℕ} {α' : H' →+ P'}
    (hα' : ∀ n x, E' n (α' x) = k' • ν' n x) (hs : ∀ w, (∀ n, E' n w = 0) → w = 0) (o : ∀ n, T n →+ T' n) (x : H) (x' : H') (w' : P')
    (h1 : ∀ n, E' n w' = o n (E n (α x))) (h2 : ∀ n, ν' n x' = o n (ν n x)) :
    k • α' x' = k' • w' ∧ (k = k' → α' x' = w') :=
  ⟨sub_eq_zero.1 (hs _ fun n => by
      rw [map_sub, map_nsmul, map_nsmul, hα', h1, hα, map_nsmul, h2, smul_comm, sub_self]),
    fun h => sub_eq_zero.1 (hs _ fun n => by rw [map_sub, hα', h1, hα, map_nsmul, h2, h, sub_self])⟩

section Pack
variable {S S' : Sys.{1} W} {T T' H H' : Sys.{1} A}

def E (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) : A ⊗[W] S.lim →+ T.M n :=
  ev (A := A) (AddMonoidHom.mk' (fun y : S.lim => g.f n (y.1 n)) fun _ _ => map_add (g.f n) _ _)
    fun w y => LinearMap.map_smulₛₗ (g.f n) w _

theorem E_tmul (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (a : A) (y : S.lim) : E g n (a ⊗ₜ y) = a • g.f n (y.1 n) := rfl

theorem E_smul (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (a : A) (w : A ⊗[W] S.lim) : E g n (a • w) = a • E g n w := ev_smul _ _ a w

theorem E_r (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (w : A ⊗[W] S.lim) : T.r n (E g (n + 1) w) = E g n w :=
  add_ext (f := (T.r n).toAddMonoidHom.comp (E g (n + 1))) (fun a y => by
    change T.r n (a • g.f (n + 1) (y.1 (n + 1))) = a • g.f n (y.1 n)
    rw [map_smul, g.comm, y.2 n]) w

def nuL {ψ : A →+* A} (ν : Sys.Hom H T ψ) (n : ℕ) : H.lim →+ T.M n :=
  AddMonoidHom.mk' (fun x : H.lim => ν.f n (x.1 n)) fun _ _ => map_add (ν.f n) _ _

def beta (g : Sys.Hom S T (algebraMap W A)) (μ : Sys.Hom T H (RingHom.id A)) : A ⊗[W] S.lim →ₗ[A] H.lim where
  toFun w := ⟨fun n => μ.f n (E g n w), fun n => by rw [μ.comm, E_r]⟩
  map_add' w w' := Subtype.ext (funext fun n => by
    change μ.f n (E g n (w + w')) = μ.f n (E g n w) + μ.f n (E g n w')
    rw [map_add (f := _), map_add (f := _)])
  map_smul' a w := Subtype.ext (funext fun n => by
    change μ.f n (E g n (a • w)) = a • μ.f n (E g n w)
    rw [E_smul, map_smul])

structure Pin (l : ℕ) (g : Sys.Hom S T (algebraMap W A)) {ψ : A →+* A} (ν : Sys.Hom H T ψ) (e : ℕ) (α : H.lim →+ A ⊗[W] S.lim) : Prop where
  sep : ∀ w, (∀ n, E g n w = 0) → w = 0
  pin : ∀ n x, E g n (α x) = (l ^ e) • nuL ν n x

theorem pin_ex [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ) (hl : Irreducible (l : W)) (c : ℕ) (h1 : Module.Finite W S.lim)
    (h2 : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0) (h3 : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (h4 : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
    (g : Sys.Hom S T (algebraMap W A))
    (hb : ∀ n, Tens W (N := fun _ : Unit => A) (M := fun _ => S.M n) (M' := T.M n) fun _ a y => a • g.f n y)
    {ψ : A →+* A} (ν : Sys.Hom H T ψ) : ∃ α, Pin l g ν c α := by
  obtain ⟨hs, hx⟩ := core l hl S c h1 h2 h3 h4 T (fun n => (g.f n).toAddMonoidHom) (fun n w y => LinearMap.map_smulₛₗ (g.f n) w y)
    (fun n y => g.comm n y) hb (fun n => AddMonoidHom.mk' (fun y : S.lim => g.f n (y.1 n)) fun _ _ => map_add (g.f n) _ _)
    (fun n w y => LinearMap.map_smulₛₗ (g.f n) w _) fun _ _ => rfl
  obtain ⟨α, hα⟩ := exists_alpha (E g) (nuL ν) (l ^ c) hs fun x => hx (fun n => nuL ν n x) fun n => (ν.lim x).2 n
  exact ⟨α, hs, hα⟩

variable {l e e' : ℕ} {g : Sys.Hom S T (algebraMap W A)} {g' : Sys.Hom S' T' (algebraMap W A)} {ψ : A →+* A} {ν : Sys.Hom H T ψ}
  {ν' : Sys.Hom H' T' ψ} {α : H.lim →+ A ⊗[W] S.lim} {α' : H'.lim →+ A ⊗[W] S'.lim}

theorem Pin.lin (h : Pin l g ν e α) (a : A) (x : H.lim) : α (a • x) = ψ a • α x :=
  sub_eq_zero.1 (h.sep _ fun n => by
    rw [map_sub, E_smul, h.pin, h.pin, smul_comm, sub_eq_zero]
    exact congrArg _ (LinearMap.map_smulₛₗ (ν.f n) a _))

theorem Pin.fac (h : Pin l g ν e α) (μ : Sys.Hom T H (RingHom.id A)) (x y : H.lim) (hy : ∀ n, μ.f n (ν.f n (x.1 n)) = y.1 n) :
    beta g μ (α x) = ((l : A) ^ e) • y := Subtype.ext (funext fun n => by
  change μ.f n (E g n (α x)) = ((l : A) ^ e) • y.1 n
  rw [h.pin, map_nsmul, ← hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)

theorem Pin.op (h : Pin l g ν e α) (h' : Pin l g' ν' e' α') {τ : A →+* A} (oT : ∀ n, T.M n →ₛₗ[τ] T'.M n) (oS : S.lim → S'.lim)
    (hS : ∀ n y, g'.f n ((oS y).1 n) = oT n (g.f n (y.1 n))) (o : A ⊗[W] S.lim →+ A ⊗[W] S'.lim) (ho : ∀ a y, o (a ⊗ₜ y) = τ a ⊗ₜ oS y)
    (x : H.lim) (x' : H'.lim) (hx : ∀ n, ν'.f n (x'.1 n) = oT n (ν.f n (x.1 n))) :
    ((l : A) ^ e) • α' x' = ((l : A) ^ e') • o (α x) ∧ (e = e' → α' x' = o (α x)) := by
  have := alpha_op h.pin h'.pin h'.sep (fun n => (oT n).toAddMonoidHom) x x' (o (α x)) (fun n =>
    add_ext (f := (E g' n).comp o) (f' := (oT n).toAddMonoidHom.comp (E g n)) (fun a y => by
      change E g' n (o (a ⊗ₜ y)) = oT n (a • g.f n (y.1 n))
      rw [ho, E_tmul, hS, LinearMap.map_smulₛₗ]) _) hx
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact ⟨this.1, fun he => this.2 (by rw [he])⟩

def tmap {L L' : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup L'] [Module W L'] (τ : A →+* A) {τW : W →+* W} (o : L →ₛₗ[τW] L')
    (hτ : ∀ w, τ (algebraMap W A w) = algebraMap W A (τW w)) : A ⊗[W] L →+ A ⊗[W] L' :=
  TensorProduct.liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun y => τ a ⊗ₜ[W] o y) fun y y' => by rw [map_add (f := _), tmul_add])
    fun a a' => AddMonoidHom.ext fun y => by
      change τ (a + a') ⊗ₜ[W] o y = τ a ⊗ₜ[W] o y + τ a' ⊗ₜ[W] o y
      rw [map_add (f := _), add_tmul]) fun w a y => by
      change τ (w • a) ⊗ₜ[W] o y = τ a ⊗ₜ[W] o (w • y)
      rw [LinearMap.map_smulₛₗ, Algebra.smul_def, map_mul, hτ, ← Algebra.smul_def, smul_tmul]

end Pack

end CrystallineSemistableComparison.Pb.Fa
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K)

def sT (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := HMS r M j

def sH (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := M.HS true j

def gH (M : Model l K) (j : ℕ) : Sys.Hom (HSW r M j) (sT r M j) (algebraMap (WittVector l r.k) (AW r)) :=
  ⟨fun n => bW r M n j, fun n y => bW_red r M n j y⟩

def ψA (N : ℕ) : AW r →+* AW r := Mid.phiA l N

variable {N : ℕ} (hT : Mid.TeichmullerCongruence r N)

def nuH (M : Model l K) (j : ℕ) : Sys.Hom (sH r M j) (sT r M j) (ψA r N) := ⟨fun n => Mid.nu r M n j hT, fun n x => nu_red r hT M n j x⟩

def muH (M : Model l K) (j : ℕ) : Sys.Hom (sT r M j) (sH r M j) (RingHom.id _) := ⟨fun n => Mid.mu r M n j hT, fun n x => mu_red r hT M n j x⟩

theorem lw_fin (M : Model l K) (hM : M.Sm) (j : ℕ) : Module.Finite (WittVector l r.k) (HSW r M j).lim := by
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  exact GlobalTheory.T.module_finite_limit_of_lseq _ l _ _ E (smooth_model_finite_length_link r M hM j)

theorem pin_all (M : Model l K) (j : ℕ) : ∃ (e : ℕ) (α : (sH r M j).lim →+ AW r ⊗[WittVector l r.k] (HSW r M j).lim),
    M.Sm → Fa.Pin l (gH r M j) (nuH r hT M j) e α := by
  by_cases hM : M.Sm
  swap
  · exact ⟨0, 0, fun h => absurd h hM⟩
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  have ha : ∀ n, IsArtinian (WittVector l r.k) ((HSW r M j).M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (GlobalTheory.T.finite_length_of_lseq_first _ l _ _ E (smooth_model_finite_length_link r M hM j) n)).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.bounded_cokernel_limit_to_level _ l _ _ E ha (lw_fin r M hM (j + 1))
  have := flatW r
  have : IsAdicComplete (Ideal.span {(l : AW r)}) (AW r) := adicA
  obtain ⟨α, hα⟩ := Fa.pin_ex l (WittVector.irreducible l) c (lw_fin r M hM j) E.kill (GlobalTheory.T.limit_divisible_of_vanishing_level _ l _ _ E ha) hc (gH r M j)
    (bc_tens r M hM j) (nuH r hT M j)
  exact ⟨c, α, fun _ => hα⟩

theorem iter_lim {R : Type} [CommRing R] {S : Sys.{1} R} {σ : R →+* R} (φ : Sys.Hom S S σ) (N n : ℕ) (x : S.lim) :
    ((⇑φ.lim.toAddMonoidHom)^[N] x).1 n = (⇑(φ.f n))^[N] (x.1 n) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

def betaP (M : Model l K) (j : ℕ) : AL r M j →ₗ[(per l K).A] HL M j where
  toFun w := Fa.beta (A := AW r) (gH r M j) (muH r hT M j) w
  map_add' := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_add
  map_smul' a w := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_smul (ofA r a) w

theorem phiA_iter (N : ℕ) (a : Acris l) :
    Mid.phiA l N a = (ACris.phi (K := ℂ_[l]) (p := l))^[N] a := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiA_succ, Function.iterate_succ_apply', ih]

def φA : AW r →+* AW r := ACris.phi (K := ℂ_[l]) (p := l)

def σA (σ : Gal(PadicAlgCl l/K)) : AW r →+* AW r := ACris.galCris σ

def Pinned (F : Fac r N) : Prop := ∀ M : Model l K, M.Sm → ∀ j, Fa.Pin l (gH r M j) (nuH r hT M j) (F.e M j) (F.α M j) ∧
  ∀ w, F.β M j w = Fa.beta (gH r M j) (muH r hT M j) w

def MuNu : Prop := ∀ (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j),
  Mid.mu r M n j hT (Mid.nu r M n j hT x) = (⇑(B.phiHc (B.schFn M.p) (okToOC l K) n j))^[N] x

theorem fac_ex (hmn : MuNu r hT)
    (hφ : ∀ w, ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w))
    (hσ : ∀ (g : K.fixingSubgroup) w, ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) (r.w w) = r.w w) :
    ∃ F : Fac r N, Pinned r hT F := by
  choose e α h using pin_all r hT
  refine ⟨{ e := e
            α := α
            β := betaP r hT
            phiT := fun M j => Fa.tmap (A := AW r) (φA r) (Wc.phiS l (B.schFn M.p) r.ρ j).lim hφ
            galT := fun M j g => Fa.tmap (A := AW r) (σA r (IntermediateField.fixingSubgroupEquiv K g)) (τW := RingHom.id _) LinearMap.id (hσ g)
            phiT_tmul := fun _ _ _ _ _ => rfl
            galT_tmul := fun _ _ _ _ _ _ => rfl
            lin := ?_, fac := ?_, phi := ?_, gal := ?_, galβ := ?_, nat := ?_ }, fun M hM j => ⟨h M j hM, fun _ => rfl⟩⟩
  · intro M hM j a x
    exact ((h M j hM).lin a x).trans (congrArg (fun b : AW r => b • α M j x) (phiA_iter N a))
  · intro M hM j x
    exact (h M j hM).fac (muH r hT M j) x _ fun n => (hmn M n j _).trans (iter_lim (M.phiH j) N n x).symm
  · intro M hM j x
    exact ((h M j hM).op (h M j hM) (τ := φA r) (fun n => phiM r M n j) (Wc.phiS l (B.schFn M.p) r.ρ j).lim
      (fun n y => (bW_phi r M n j _).symm) _ (fun _ _ => rfl) x (phiL M j x) fun n => nu_phi r hT M n j _).2 rfl
  · intro M hM j g x
    exact ((h M j hM).op (h M j hM) (τ := σA r (IntermediateField.fixingSubgroupEquiv K g)) (fun n => galM r M _ (hσ g) n j) id
      (fun n y => (bW_gal r M _ (hσ g) n j _).symm) _ (fun _ _ => rfl) x (galL M j g x) fun n => nu_gal r hT M _ (hσ g) n j _).2 rfl
  · intro M hM j g y
    refine Subtype.ext (funext fun n => (mu_gal r hT M _ (hσ g) n j _).trans (congrArg (Mid.mu r M n j hT) ?_))
    have e1 : Fa.E (gH r M j) n ((1 : AW r) ⊗ₜ y) = bW r M n j (y.1 n) := (Fa.E_tmul _ n 1 y).trans (one_smul _ _)
    exact (congrArg (galM r M _ (hσ g) n j) e1).trans ((bW_gal r M _ (hσ g) n j _).trans e1.symm)
  · intro M M' u hu hM hM' j x
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul, sub_eq_zero]
    exact ((h M' j hM').op (h M j hM) (τ := RingHom.id _) (fun n => pullM r u hu n j) (Wc.pullS l r.ρ (B.schMap u hu) j).lim
      (fun n y => (bW_pull r u hu n j _).symm) (LinearMap.lTensor (AW r) (Wc.pullS l r.ρ (B.schMap u hu) j).lim).toAddMonoidHom
      (fun _ _ => rfl) x (pullL u hu j x) fun n => nu_pull r hT u hu n j _).1

end CrystallineSemistableComparison.Pb
