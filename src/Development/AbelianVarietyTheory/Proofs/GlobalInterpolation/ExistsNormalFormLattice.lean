module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumValsQOfInvariant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegSumLogDerivNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormalFormLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.QNormalShape

section Abstract

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]

theorem mem_span_basis_iff [IsDomain O] [IsFractionRing O F] {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) (v : Fin N → F) :
    v ∈ Submodule.span O (Set.range b) ↔ ∀ l, b.repr v l ∈ Set.range (algebraMap O F) :=
  b.mem_span_iff_repr_mem O v

theorem isLattice_span_basis {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) :
    Submodule.IsFullLattice F (Submodule.span O (Set.range b)) := by
  have hfg : (Submodule.span O (Set.range b)).FG := Submodule.fg_span (Set.finite_range _)
  have hspan : Submodule.span F (↑(Submodule.span O (Set.range b)) : Set (Fin N → F)) = ⊤ := by
    rw [Submodule.span_span_of_tower, b.span_eq]
  refine { fg := hfg, span_eq_top := hspan, linearIndepOn := ?_ }
  intro s hs hli
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact linearIndepOn_empty F id
  · have : Nontrivial O := (algebraMap O F).domain_nontrivial
    have : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 <| by
      intro a a' heq
      apply hli.linearIndependent.smul_left_injective ⟨x, hx⟩
      simpa only [id_eq, algebraMap_smul] using congrArg (fun t : F => t • x) heq
    refine Submodule.linearIndepOn_of_finrank_le_finrank_span _ hfg ?_ hs hli
    rw [hspan, finrank_top, Module.finrank_eq_card_basis b]
    exact finrank_range_le_card b

theorem mem_normalForm_iff {Y : Type} [AddCommGroup Y] [Module F Y] [Module O Y] {c : ℕ} (q : O)
    (M : Submodule O Y) (a : Fin c → Y) (e : Fin c → ℤ) (z y : Y) :
    y ∈ IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm F q M a e z ↔ ∃ m ∈ M, ∃ s : Fin c → O,
      y = m + ∑ i, s i • ((algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)) := by
  unfold IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_sup]
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, rfl⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩

theorem irreducible_of_notMem_sq [IsDomain O] [IsDiscreteValuationRing O] {q : O}
    (h1 : q ∈ IsLocalRing.maximalIdeal O) (h2 : q ∉ IsLocalRing.maximalIdeal O ^ 2) : Irreducible q := by
  refine ⟨h1, fun a b hab => ?_⟩
  by_contra h
  rw [not_or] at h
  exact h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)

end Abstract

theorem exists_shape : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord → ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (n c : ℕ)
    (h : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ∃ r ∈ Loc.R1 E n c, ∃ (e : Fin c → ℤ) (z : Fin n → E),
      (r * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z := by
  intro H E _ _ _ P hd n c h
  have hP := P.isPrime
  have hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField E P.asIdeal.primeCompl hS
  have : IsLocalization.AtPrime A P.asIdeal := Localization.subalgebra.isLocalization_ofField E _ hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ hS
  have hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a := by
    intro a
    constructor
    · rintro ⟨⟨x, r, s, hs, rfl⟩, rfl⟩
      refine ⟨r, s, hs, ?_⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _
      field_simp
    · rintro ⟨r, s, hs, e⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      refine ⟨⟨a, r, s, hs, ?_⟩, rfl⟩
      rw [← e]
      field_simp
  have hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
  have hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) := by
    refine irreducible_of_notMem_sq ?_ ?_
    · rw [← hmax]
      exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · rw [← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]
      rintro ⟨s, hs, hm⟩
      exact (Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2
  obtain ⟨r, hr, e, z, hz⟩ := H A E _ hq n c
    (Submodule.span A (Set.range (Pi.basisFun E (Fin n))))
    (by first | exact isLattice_span_basis (Pi.basisFun E (Fin n))
              | exact (isLattice_span_basis (Pi.basisFun E (Fin n))).toIsLattice)
    (Submodule.span A (Set.range ((Pi.basisFun E (Fin (n + c))).map h)))
    (by first | exact isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)
              | exact (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)).toIsLattice)
  refine ⟨r, hr, e, z, ?_⟩
  have hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E) := by
    rw [map_natCast, map_natCast]
  ext y
  have hy := SetLike.ext_iff.1 hz y
  rw [mem_normalForm_iff, hqE] at hy
  simp only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr,
    LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy
  simp only [Set.mem_image, Set.mem_ofPred_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨l, hl, rfl⟩, s, hs⟩ := hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩
    exact ⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    choose t ht using fun i => (hA _).2 (hs i)
    obtain ⟨v, hv, hv'⟩ := hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩
    refine ⟨h.symm v, hv, ?_⟩
    rw [← hv']
    simp

end GlobalTheory.QNormalShape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowDvdOfMulNatCastEqOfNotMemPrime
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem pow_dvd_of_mul_natCast_eq_of_notMem_prime {R : Type} [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R)
    (hI : I.IsPrime) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I) {s : R} (hs : s ∉ I) :
    ∀ (d i : ℕ) (r : R), s * (i : R) = (q : R) ^ d * r → q ^ d ∣ i := by
  intro d
  induction d with
  | zero => intro i r _; simp
  | succ d ih =>
    intro i r h
    have hiI : (i : R) ∈ I := by
      have : s * (i : R) ∈ I := by
        rw [h, pow_succ', mul_assoc]
        exact I.mul_mem_right _ hqI
      exact (hI.mem_or_mem this).resolve_left hs
    have hdvd : q ∣ i := by
      by_contra hn
      have hc : IsCoprime (q : R) (i : R) := by
        have := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom R)
        simpa using this
      obtain ⟨a, b, hab⟩ := hc
      exact hI.one_notMem (hab ▸ I.add_mem (I.mul_mem_left a hqI) (I.mul_mem_left b hiI))
    obtain ⟨j, rfl⟩ := hdvd
    have hq0 : (q : R) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h' : s * (j : R) = (q : R) ^ d * r := by
      apply mul_left_cancel₀ hq0
      push_cast at h
      linear_combination h
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left q (ih j r h')

theorem sum_valsQ_eq_of_support_intAt : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (K : Type) [Field K] (f : E → K) (A₀ : ℕ), (∀ a, f a ≠ 0 → IntAt P ((qOf P : E) ^ A₀ * a)) → ∀ A B : ℕ, A₀ ≤ A → ∑ a ∈ LocE.valsQ E (qOf P) A B, f a = ∑ a ∈ LocE.valsQ E (qOf P) A₀ B, f a := by
  intro E _ _ P hq K _ f A₀ hf A B hA
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hA
  have hqP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  generalize qOf P = q at *
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨q ^ d * i, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hi hpos
    · push_cast
      field_simp
      ring
  · intro a ha hna
    by_contra hfa
    apply hna
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨r, s, hs, hrs⟩ := hf _ hfa
    have h1 : s * (i : 𝓞 E) = (q : 𝓞 E) ^ d * r := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      simp only [map_mul, map_pow, map_natCast]
      rw [← hrs]
      field_simp
      ring
    obtain ⟨j, rfl⟩ := pow_dvd_of_mul_natCast_eq_of_notMem_prime P.asIdeal P.isPrime hq hqP hs d i r h1
    refine ⟨j, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this] at hi
      exact Nat.lt_of_mul_lt_mul_left hi
    · push_cast
      field_simp
      ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartz
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory

theorem boxSum_eq_of_funBdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  intro E _ _ K _ _ P hq ι _ _ f N hf A B hA hB
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  unfold boxSum
  refine weighted_sum_piFinset ι E K
    (fun g => (∀ a, g a ≠ 0 → IntAt P ((qOf P : E) ^ N * a)) ∧
      ∀ a u, IntAt P u → g (a + (qOf P : E) ^ N * u) = g a) _ _ _ _ ?_ f ?_
  · rintro g ⟨h1, h2⟩
    rw [sum_valsQ_of_invariant E P K g N h2 A B hB,
      sum_valsQ_eq_of_support_intAt E P hq K g N h1 A N hA]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  · intro t i
    refine ⟨fun a ha => ?_, fun a u hu => ?_⟩
    · simpa using hf.1 _ ha i
    · have e : Function.update t i (a + (qOf P : E) ^ N * u)
          = Function.update t i a + ((qOf P : E) ^ N) • (Pi.single i u : ι → E) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      simp only [e]
      refine hf.2 _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simpa [hj] using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartzStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  first | exact @GlobalTheory.boxSum_eq_of_funBdd | exact GlobalTheory.boxSum_eq_of_funBdd | (intros; apply GlobalTheory.boxSum_eq_of_funBdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartz
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz

variable {E : Type} [Field E] {n' c' n c : ℕ}

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add (x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (x + y) = _root_.Formalism.L2.Col.Loc.chArg x + _root_.Formalism.L2.Col.Loc.chArg y := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.add_apply, _root_.GlobalTheory.QNormal.atN_add, Finset.sum_add_distrib]

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul (a : E) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (a • x) = a * _root_.Formalism.L2.Col.Loc.chArg x := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.smul_apply, _root_.GlobalTheory.QNormal.atN_smul, Finset.mul_sum]

def freeMap (u : Loc.FC n' c' n c → E) : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : Loc.IsFree n' n c l.1 s.1 then u ⟨(l, s), hf⟩ else 0)

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E) (a : E) :
    _root_.Formalism.L2.Col.Loc.xx1 xj (t + a • u) = _root_.Formalism.L2.Col.Loc.xx1 xj t + a • _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u := by
  unfold _root_.Formalism.L2.Col.Loc.xx1 _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap
  rw [← map_smul, ← map_add (f := _)]
  congr 1
  ext l s
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp

variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

private lemma intAt_atN_of_intV {N : ℕ} {v : Fin N → E}
    (hv : _root_.GlobalTheory.QNormal.IntV P v) (i : ℕ) : _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.atN v i) := by
  unfold _root_.Formalism.L2.Col.Loc.atN
  split_ifs with h
  · exact hv ⟨i, h⟩
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

private lemma intV_eN' (N s : ℕ) :
    _root_.GlobalTheory.QNormal.IntV P (_root_.Formalism.L2.Col.Loc.eN E N s) := by
  intro l
  dsimp only [_root_.Formalism.L2.Col.Loc.eN]
  split_ifs
  · exact _root_.GlobalTheory.QNormal.intAt_one P
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg
    {y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} (hy : _root_.GlobalTheory.QNormal.IntHom P y) :
    _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.chArg y) := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  exact _root_.GlobalTheory.QNormal.intAt_sum _ _ fun i _ =>
    intAt_atN_of_intV (hy _ (intV_eN' _ _)) _

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap {u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E}
    (hu : ∀ i, _root_.Formalism.L2.Col.IntAt P (u i)) : _root_.GlobalTheory.QNormal.IntHom P (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u) := by
  rw [_root_.GlobalTheory.QNormal.intHom_iff]
  intro s l
  simp only [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, Matrix.of_apply]
  split_ifs with hf
  · exact hu _
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type)
    [Field K] (P : HeightOneSpectrum (𝓞 E))
    (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : _root_.Formalism.L2.Col.Loc.SF E K (n' + c') (n + c)), N ≤ D →
    _root_.GlobalTheory.QNormal.CharTo P D psi → _root_.GlobalTheory.QNormal.HomBdd P N Psi →
    ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
      _root_.GlobalTheory.QNormal.FunBdd P N (_root_.GlobalTheory.QNormal.integrand psi Psi xj) ∧
      ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
        _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
  intro E _ _ K _ P n' c' n c psi D N Psi hND hpsi hPsi xj
  obtain ⟨hPsi1, hPsi2⟩ := hPsi
  obtain ⟨hpsi1, hpsi2⟩ := hpsi
  have hchar : ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
      _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := fun t ht => by
    rw [← _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul]
    exact _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg (hPsi1 _ ht)
  refine ⟨?_, hchar⟩
  unfold _root_.GlobalTheory.QNormal.FunBdd
  refine ⟨fun t ht i => ?_, fun t u hu => ?_⟩
  · have hne : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 := fun h => ht (by simp [_root_.GlobalTheory.QNormal.integrand, h])
    have hint := (_root_.GlobalTheory.QNormal.intHom_iff _).1 (hPsi1 _ hne)
    obtain ⟨⟨l, s⟩, hf⟩ := i
    have hentry := hint s l
    simpa only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      _root_.GlobalTheory.QNormal.linearMap_unfolding_apply_single, dif_pos hf] using hentry
  · have hfree := _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap (P := P) hu
    have hPsi_eq : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj (t + (_root_.Formalism.L2.Col.qOf P : E) ^ N • u)) = Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) := by
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul]
      exact hPsi2 _ _ hfree
    simp only [_root_.GlobalTheory.QNormal.integrand, hPsi_eq]
    by_cases h0 : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) = 0
    · simp [h0]
    · congr 1
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul, _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add,
        _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul, neg_add]
      have hx : _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ D * -_root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
        rw [mul_neg]
        exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono hND (hchar t h0))
      have hy : _root_.Formalism.L2.Col.IntAt P (-((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u))) :=
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul N
          (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg hfree))
      rw [hpsi1 _ _ hx (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul D hy), hpsi2 _ hy, mul_one]

end GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartzStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), N ≤ D → CharTo P D psi → HomBdd P N Psi → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), FunBdd P N (integrand psi Psi xj) ∧ ∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → IntAt P ((qOf P : E) ^ N * Loc.chArg (Loc.xx1 xj t)) := by
  first | exact @GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | exact GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | (intros; apply GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_zpow_mul {P : HeightOneSpectrum (𝓞 E)} {e : ℤ} (he : 0 ≤ e) {a : E} (ha : IntAt P a) :
    IntAt P ((qOf P : E) ^ e * a) := by
  lift e to ℕ using he
  rw [zpow_natCast]
  exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul e ha

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) : IntV P (Loc.inX E n c z) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hz _
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  simp only [Loc.eN]
  split_ifs
  · exact intAt_one P
  · exact ⟨0, 1, one_notMem P, by simp⟩

theorem intV_sum {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (h : ∀ i ∈ s, IntV P (f i)) : IntV P (∑ i ∈ s, f i) := by
  intro l
  rw [Finset.sum_apply]
  exact intAt_sum s _ (fun i hi => h i hi l)

theorem intV_glue {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) (i : Fin c) :
    IntV P (if i.1 = 0 then Loc.inX E n c z else 0) := by
  split_ifs
  · exact intV_inX hz
  · exact IntV.zero P

theorem decomp {n c : ℕ} (x : Fin (n + c) → E) :
    x = Loc.inX E n c (fun a => x (Fin.castAdd c a)) + ∑ i : Fin c, x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) := by
  funext l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) l
  · have h1 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
      intro i
      simp only [Loc.eN, Fin.val_castAdd]
      rw [if_neg]
      omega
    simp [inX_castAdd, Finset.sum_apply, h1]
  · have h2 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.natAdd n b) = if i = b then 1 else 0 := by
      intro i
      by_cases hib : i = b
      · subst hib
        simp [Loc.eN]
      · simp only [Loc.eN, Fin.val_natAdd, if_neg hib]
        rw [if_neg]
        intro h
        apply hib
        ext
        omega
    have h3 : Loc.inX E n c (fun a => x (Fin.castAdd c a)) (Fin.natAdd n b) = 0 := by
      rw [inX_apply, dite_eq_right (by simp)]
    simp [Finset.sum_apply, h2, h3]

theorem mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {e : Fin c → ℤ} (he : ∀ i, e i ≤ 0) {z : Sp E n}
    (hz : IntV P z) {x : Sp E (n + c)} (hx : IntV P x) : x ∈ nfLat P n c e z := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  set w : Sp E n := ∑ i : Fin c, x (Fin.natAdd n i) • (if i.1 = 0 then z else 0) with hw
  refine ⟨(fun a => x (Fin.castAdd c a)) - w, ?_, fun i => x (Fin.natAdd n i) * (qOf P : E) ^ (-e i), ?_, ?_⟩
  · rw [mem_stdAt_iff, sub_eq_add_neg]
    refine IntV.add (fun l => hx _) (IntV.neg ?_)
    refine intV_sum _ _ (fun i _ => IntV.smul (hx _) ?_)
    split_ifs
    · exact hz
    · exact IntV.zero P
  · intro i
    show IntAt P (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i))
    rw [mul_comm]
    exact intAt_zpow_mul (by linarith [he i]) (hx _)
  · have hs : ∀ i : Fin c, (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i)) • nfGen (qOf P) n c e z i =
        x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) +
          Loc.inX E n c (x (Fin.natAdd n i) • (if i.1 = 0 then z else 0)) := by
      intro i
      simp only [nfGen, smul_smul, mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one, smul_add]
      congr 1
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, ← map_sum, ← hw, map_sub]
    conv_lhs => rw [decomp x]
    abel

theorem smul_int_of_mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c j : ℕ} {e : Fin c → ℤ} (he : ∀ i, -(j : ℤ) ≤ e i)
    {z : Sp E n} (hz : IntV P z) {x : Sp E (n + c)} (hx : x ∈ nfLat P n c e z) : IntV P (((qOf P : E) ^ j) • x) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hx
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  rw [mem_stdAt_iff] at hl
  have key : ∀ i : Fin c, ((qOf P : E) ^ j) • (s i • nfGen (qOf P) n c e z i) =
      ((qOf P : E) ^ ((j : ℤ) + e i) * s i) •
        (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0) := by
    intro i
    simp only [nfGen, smul_smul]
    congr 1
    rw [zpow_add₀ hq, zpow_natCast]
    ring
  rw [smul_add, Finset.smul_sum, ← LinearMap.map_smul (Loc.inX E n c)]
  refine IntV.add (intV_inX (fun k => ?_)) (intV_sum _ _ (fun i _ => ?_))
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul j (hl k)
  · rw [key i]
    refine IntV.smul ?_ (IntV.add (intV_eN P _ _) (intV_glue hz i))
    exact intAt_zpow_mul (by linarith [he i]) (hs i)

end Lattice

theorem inclAt (X : Fields) (Pr : Primes X) (R : Ranks) : InclAt Pr R := by
  intro j P hP h k hNF hk
  obtain ⟨e, z, he, hz, himg⟩ := hNF
  have hk' : ∀ x, k x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ lamYat (Pr := Pr) (R := R) j P := hk
  rw [mem_stdAt_iff] at hz
  constructor
  · intro x hx
    have hxi : IntV P x := (mem_lamYat (R := R) hP x).1 hx
    have hmem : x ∈ nfLat P (R.N j) (cOf R j) e z := mem_nfLat (fun i => (he i).2) hz hxi
    rw [← himg] at hmem
    obtain ⟨y', hy', rfl⟩ := hmem
    refine ⟨k.symm y', ?_, ?_⟩
    · rw [← hk']
      simpa using hy'
    · simp [LinearEquiv.mul_apply]
  · intro x hx
    have h1 : h (k x) ∈ nfLat P (R.N j) (cOf R j) e z := by
      rw [← himg]
      exact ⟨k x, (hk' x).2 hx, rfl⟩
    have h2 := smul_int_of_mem_nfLat (fun i => (he i).1) hz h1
    rw [mem_lamYat hP]
    intro l
    have h3 := h2 l
    simpa [LinearEquiv.mul_apply] using h3

end GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalFormStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSandwich_of_latticeNormalForm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks), GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R := by
  first | exact @GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | exact GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | (intros; apply GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormCoordinates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.lattice_normal_form_coordinates

open GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

variable {F : Type} [Field F] {n c : ℕ}

theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN F N i = 0 := by
  funext l
  unfold Loc.eN
  have := l.2
  rw [if_neg (by omega)]
  rfl

theorem sum_eN_apply (g : Fin c → F) (l : Fin (n + c)) :
    (∑ i : Fin c, g i • Loc.eN F (n + c) (n + i.1)) l = if h : l.1 < n then 0 else g ⟨l.1 - n, by omega⟩ := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Loc.eN, smul_eq_mul]
  split_ifs with h
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega), mul_zero]
  · rw [Finset.sum_eq_single ⟨l.1 - n, by omega⟩]
    · rw [if_pos (by simp; omega), mul_one]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hl
      exact hb (Fin.ext (by simp; omega))
    · simp

theorem decomp (v : Fin (n + c) → F) :
    v = Loc.inX F n c (fun a => v (Fin.castAdd c a)) +
      ∑ i : Fin c, v (Fin.natAdd n i) • Loc.eN F (n + c) (n + i.1) := by
  funext l
  rw [Pi.add_apply, inX_apply, sum_eN_apply]
  split_ifs with h
  · rw [add_zero]
    rfl
  · rw [zero_add]
    congr 1
    exact Fin.ext (by simp; omega)

theorem isFrame : IsFrame (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg (Fin.natAdd n i)
    rw [sum_eN_apply, dite_eq_right (by simp)] at this
    simpa using this
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    funext l
    have h1 := congrFun hg l
    rw [sum_eN_apply] at h1
    by_cases h : l.1 < n
    · rw [dite_eq_left h] at h1
      exact h1.symm
    · rw [inX_apply, dite_eq_right h]
      rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [decomp v]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem flag_le (i : Fin c) :
    flag (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) i ≤ Loc.Ufl F n c i.1 := by
  refine sup_le ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    exact inX_mem_Ufl _ x
  · rintro _ ⟨l, hl, rfl⟩
    have : l.1 < i.1 := hl
    exact eN_mem_Ufl (by omega)

theorem R1cond_of {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ x, r (Loc.inX F n c x) ∈ Loc.Ufl F n c 0)
    (h2 : ∀ i : Fin c, i.1 = 0 → r (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1))
    (h3 : ∀ i : Fin c, r (Loc.eN F (n + c) (n + i.1)) - Loc.eN F (n + c) (n + i.1) ∈ Loc.Ufl F n c i.1) :
    Loc.R1cond F n c r := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [decomp v, map_add (f := _), map_sum]
    refine add_mem (Ufl_mono (Nat.zero_le i) (h1 _)) (Submodule.sum_mem _ fun j _ => ?_)
    by_cases hj : j.1 < i
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := add_mem (Ufl_mono hj.le (h3 j)) (eN_mem_Ufl (F := F) (n := n) (c := c) (i := i) (s := n + j.1) (by omega))
      rwa [sub_add_cancel] at this
    · rw [mem_Ufl.1 hv (Fin.natAdd n j) (by simp; omega), zero_smul, map_zero]
      exact zero_mem _
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [eN_eq_zero (by omega), map_zero]
    · exact h2 ⟨0, hc⟩ rfl
  · by_cases hi : i < c
    · exact h3 ⟨i, hi⟩
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

theorem R1cond_inv {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) :
    Loc.R1cond F n c r⁻¹ := by
  have key : ∀ i, ∀ v ∈ Loc.Ufl F n c i, r⁻¹ v ∈ Loc.Ufl F n c i := by
    intro i v hv
    have hle : (Loc.Ufl F n c i).map r.toLinearMap ≤ Loc.Ufl F n c i := by
      rintro _ ⟨w, hw, rfl⟩
      exact hr.1 i w hw
    have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
    rw [← heq] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have : r⁻¹ (r.toLinearMap w) = w := r.symm_apply_apply w
    rwa [this]
  refine ⟨key, ?_, fun i => ?_⟩
  · show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, hr.2.1]
  · have h := neg_mem (key i _ (hr.2.2 i))
    have e : r⁻¹ (r (Loc.eN F (n + c) (n + i))) = Loc.eN F (n + c) (n + i) := r.symm_apply_apply _
    rwa [map_sub, e, neg_sub] at h

theorem mem_unipotentRadical_of_isSemidirect {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : IsSemidirect (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) r) :
    r ∈ Loc.R1 F n c := by
  obtain ⟨γ, g, u, hg, hu, rfl⟩ := hr
  have h1 : Loc.R1cond F n c g := by
    refine R1cond_of (fun x => ?_) (fun i _ => hg.2 i) (fun i => ?_)
    · have := hg.1 ⟨Loc.inX F n c x, x, rfl⟩
      obtain ⟨y, hy⟩ := (γ ⟨Loc.inX F n c x, x, rfl⟩).2
      rw [show g (Loc.inX F n c x) = Loc.inX F n c y from this.trans hy.symm]
      exact inX_mem_Ufl 0 y
    · rw [show g (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1) from hg.2 i, sub_self]
      exact zero_mem _
  have h2 : Loc.R1cond F n c u := by
    refine R1cond_of (fun x => ?_) hu.2.1 (fun i => flag_le i (hu.2.2 i))
    rw [hu.1 _ ⟨x, rfl⟩]
    exact inX_mem_Ufl 0 x
  exact ⟨h1.mul h2, R1cond_inv (h1.mul h2)⟩

theorem isLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type} [AddCommGroup V] [Module F V] [Module O V]
    [IsScalarTower O F V] [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W] (φ : V ≃ₗ[F] W)
    (L : Submodule O V) (hL : Submodule.IsLattice F L) :
    Submodule.IsLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h : ((L.map (φ.toLinearMap.restrictScalars O) : Submodule O W) : Set W) = φ.toLinearMap '' (L : Set V) := rfl
  intro s hs hli
  have hs' : φ.symm '' s ⊆ (L : Set V) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := h ▸ hs hy
    simpa using hz
  have hi : LinearIndepOn O id (φ.symm '' s) := by
    apply (linearIndepOn_id_imageₛ_iff (f := φ.symm.toLinearMap.restrictScalars O) φ.symm.injective.injOn).2
    exact hli
  have hf := hL.linearIndepOn (φ.symm '' s) hs' hi
  have hm := (linearIndepOn_id_imageₛ_iff (f := φ.toLinearMap) φ.injective.injOn).2 hf
  simpa [Set.image_image, Function.comp_def] using hm

theorem isFullLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type}
    [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
    [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W]
    (φ : V ≃ₗ[F] W) (L : Submodule O V) (hL : Submodule.IsFullLattice F L) :
    Submodule.IsFullLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  haveI := isLattice_map φ L hL.toIsLattice
  refine { span_eq_top := ?_ }
  change Submodule.span F (φ.toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span φ.toLinearMap, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem latticeNormalFormCoord_of : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm → GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord := by
  intro H O F _ _ _ _ _ _ q hq n c L hL Λ hΛ
  let φ := LinearEquiv.ofInjective (Loc.inX F n c) inX_injective
  obtain ⟨r, e, z, hr, ⟨z', rfl⟩, h⟩ := H O F (Fin (n + c) → F) q hq c _ _ isFrame _ (by
    first | exact isFullLattice_map φ L hL | exact isLattice_map φ L hL) Λ hΛ
  refine ⟨r, mem_unipotentRadical_of_isSemidirect hr, e, z', ?_⟩
  rw [h]
  congr 1
  unfold inY
  rw [← Submodule.map_comp]
  rfl

end GlobalTheory.Proof.lattice_normal_form_coordinates
end
end
