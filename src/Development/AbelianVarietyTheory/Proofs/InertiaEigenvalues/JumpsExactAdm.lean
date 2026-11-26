module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttached
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

end GlobalTheory.TripleGal.Jumps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttached
noncomputable section

namespace GlobalTheory.TripleGal.HodgeOfAtt

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem not_mem_placesOver_of_ne {D : D7} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem not_mem_pD (D : D7) (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : v ∉ D.ntw.pD i := by
  intro hp
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hp
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  split_ifs at hv' with h
  · exact not_mem_placesOver_of_ne D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv' hv
  · exact not_mem_placesOver_of_ne D.host.pde_prime hl (Ne.symm h) v hv' hv

end GlobalTheory.TripleGal.HodgeOfAtt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttached
noncomputable section

namespace GlobalTheory.TripleUnramified

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y ∈ A := by
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', mem_smul_iff, mem_smul_iff,
    map_inv₀, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · have hdec' : σ • g • A = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, hdec', inv_smul_smul]
  ·
    have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff, ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
      exact (ValuationSubring.valuation_le_one_iff _ _).1 hx
    have key := (valuation_smul_lt_one_iff A g _).1 (hval (g x) hx')
    have e : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      simp [AlgEquiv.mul_apply, map_sub]
    rwa [e] at key

end Galois

end GlobalTheory.TripleUnramified

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isδMap_of_dense_δLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  intro l _ Q _ C _ D DC J JC h hl hJ hH hd x
  have hlC : (l : C) ∈ JC := by
    have := hJ (Ideal.mem_map_of_mem h hl)
    simpa using this
  have hpow : ∀ m : ℕ, (J ^ m).map h ≤ JC ^ m := fun m => by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hJ m
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha, hxa⟩ := hd x (n + 1)
  have ha' := (mem_δLocus).1 ha
  set y := x - a with hy
  have hxy : x = a + y := by rw [hy]; ring
  have h1 : D.δ (a + y) - D.δ a ∈ J ^ n := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l Q D J hl n a y hxa
  have h1' : h (D.δ x) - h (D.δ a) ∈ JC ^ n := by
    rw [hxy, ← map_sub]; exact hpow n (Ideal.mem_map_of_mem h h1)
  have hyC : h y ∈ JC ^ (n + 1) := hpow (n + 1) (Ideal.mem_map_of_mem h hxa)
  have h2 : DC.δ (h a + h y) - DC.δ (h a) ∈ JC ^ n := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l C DC JC hlC n (h a) (h y) hyC
  have h2' : DC.δ (h x) - DC.δ (h a) ∈ JC ^ n := by rw [hxy, map_add (f := _)]; exact h2
  have key : h (D.δ x) - DC.δ (h x) ∈ JC ^ n := by
    have := (JC ^ n).sub_mem h1' h2'
    rw [ha'] at this
    convert this using 1; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus : ∀ (l : ℕ) [Fact l.Prime] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (D : Delta l Q) (DC : Delta l C) (J : Ideal Q) (JC : Ideal C) (h : Q →+* C), (l : Q) ∈ J → J.map h ≤ JC → IsHausdorff JC C → (∀ (x : Q) (n : ℕ), ∃ a ∈ δLocus D DC h, x - a ∈ J ^ n) → IsδMap D DC h := by
  first | exact @GlobalTheory.isδMap_of_dense_δLocus | exact GlobalTheory.isδMap_of_dense_δLocus | (intros; apply GlobalTheory.isδMap_of_dense_δLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPure
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

end GlobalTheory.PurityInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.UnivCharIne

theorem surj_conj (D : D7) {B : Type} [CommGroup B] (χ : G D.host.E D.nd.Om →* B) (hA : AntiHom D.ntw.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring D.nd.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A := by
    ext y
    show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem delU_ine : ∀ D : D7, GlobalTheory.UnivChar.IsUnivChar D.nexp → (∀ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M → ∀ P (hP : P ∈ Q), (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧ ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0) := by
  intro D hU i Q M hQ P hP
  obtain ⟨-, hQ'⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hQ' P hP
    rwa [GlobalTheory.GalChar.isConjPl_unique h h'']
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hQ' P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩
    rcases hv with rfl | hv
    · exact hsP A hA b
    · exact surj_conj D χ h2 hv hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩
  have e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ) := by
    intro σ
    rw [hU]
    exact (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ
  refine ⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, hx⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩
  · rw [e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]
    rfl

end GlobalTheory.UnivCharIne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.JointDiag

theorem aeval_restrict_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) (y : W) :
    ((aeval (T.restrict hW) q y : W) : V) = aeval T q (y : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      LinearMap.restrict_apply, Submodule.coe_smul]
    rw [Module.End.pow_restrict n hW]
    rfl

theorem ker_prod {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⨆ r ∈ s, f.eigenspace r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))

theorem iSup_eigenspace_eq_top_of_aeval {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (p : K[X]) (hs : p.Separable) (hp : p.Splits) (h0 : aeval f p = 0) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  classical
  have hne : p ≠ 0 := hs.ne_zero
  let s : Finset K := ⟨p.roots, nodup_roots hs⟩
  have hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod := rfl
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := LinearMap.congr_fun h0 x
    rw [hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.resolve_left hc
  rw [ker_prod] at hker
  rw [eq_top_iff, ← hker]
  exact iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r

theorem le_iSup_jointEigenspace_inf : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) (W : Submodule K V), (∀ a c, Commute (T a) (T c)) → (∀ a, ∀ x ∈ W, T a x ∈ W) → (∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ ∀ x ∈ W, Polynomial.aeval (T a) p x = 0) → W ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
  intro K V ι _ _ _ _ T W hc hW hp
  let S : ι → Module.End K W := fun a => (T a).restrict (hW a)
  have hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0 := by
    intro a
    obtain ⟨p, hs, hsp, hx⟩ := hp a
    refine ⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [aeval_restrict_coe]
    simpa using hx y y.2
  have hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ := by
    intro a μ
    obtain ⟨p, hs, _, h0⟩ := hS0 a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤ := by
    intro a
    obtain ⟨p, hs, hsp, h0⟩ := hS0 a
    simp_rw [hmax]
    exact iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0
  have hcomm : Pairwise fun i j => Commute (S i) (S j) := fun i j _ =>
    LinearMap.restrict_commute (hc i j) (hW i) (hW j)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag
  simp_rw [hmax] at htop
  have hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤
      ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [SetLike.mem_coe] at hy ⊢
    rw [Submodule.mem_iInf]
    intro a
    have h := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)
    have h' := congrArg Subtype.val h
    simp only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'
    rw [LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, h', sub_self]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a) := by
    rw [htop]; trivial
  exact hle ⟨⟨x, hx⟩, hmem, rfl⟩

end GlobalTheory.JointDiag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdeal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.IdealSubMembership

theorem padicInt_ringHom_ext {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] {J : Ideal A}
    (hlJ : (l : A) ∈ J) [IsHausdorff J A] (φ ψ : ℤ_[l] →+* A) : φ = ψ := by
  ext c
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
  have h1 : c = ((c.appr n : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * d := by rw [← hd]; ring
  have e : φ c - ψ c = (l : A) ^ n * (φ d - ψ d) := by
    rw [h1]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ n)

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} (hJ : J ≤ (⊥ : Ideal A).jacobson) {q : ℕ}
    (hq : (q : A) ∈ J) {x y : A} (hx : x ^ q = x) (hy : y ^ q = y) (hxy : x - y ∈ J) : x = y := by
  set S := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i) with hS
  have hS1 : S * (x - y) = x - y := by
    rw [hS, geom_sum₂_mul, hx, hy]
  have hSJ : S ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy' : Ideal.Quotient.mk J y = Ideal.Quotient.mk J x := (Ideal.Quotient.eq.2 hxy).symm
    have hq' : (q : A ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]; exact hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    simp only [map_mul, map_pow, hxy']
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp
    have : ∀ i ∈ Finset.range q, (Ideal.Quotient.mk J x) ^ i * (Ideal.Quotient.mk J x) ^ (q - 1 - i) =
        (Ideal.Quotient.mk J x) ^ (q - 1) := fun i hi => by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hq', zero_mul]
  have hu : IsUnit (S * (-1) + 1) := (Ideal.mem_jacobson_bot.1 (hJ hSJ)) (-1)
  have h2 : (S * (-1) + 1) * (x - y) = 0 := by linear_combination -hS1
  rw [← sub_eq_zero]
  exact (hu.mul_right_eq_zero).1 h2

variable {l : ℕ} [hl : Fact l.Prime]

theorem sub_mem_I {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (x : bk.S) :
    BK.hf f x - BK.hf g x ∈ B.I := by
  have h : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
    (bk.str.apply_symm_apply _).symm
  rw [← Ideal.Quotient.eq]
  exact (f.f_str _ x h).trans (g.f_str _ x h).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧
      B.I = Ideal.span {BK.hf f bk.E} := by
  intro l _ K bk B f g
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨fun w => ?_, sub_mem_I bk f g X, ?_⟩
  · let φ1 : Wq l bk.a →+* B.A := (BK.hf f).comp C
    let φ2 : Wq l bk.a →+* B.A := (BK.hf g).comp C
    have hz := padicInt_ringHom_ext hlJ (φ1.comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (φ2.comp (algebraMap ℤ_[l] (Wq l bk.a)))
    have ht : ∀ z : Fq l bk.a, φ1 (WittVector.teichmuller l z) = φ2 (WittVector.teichmuller l z) := by
      intro z
      have hq : ((l ^ bk.a : ℕ) : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
        rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hlJ _ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      have hp : WittVector.teichmuller l z ^ (l ^ bk.a) = WittVector.teichmuller l z := by
        rw [← map_pow, Fq.pow_card]
      refine eq_of_pow_eq_self (IsAdicComplete.le_jacobson_bot _) hq ?_ ?_
        (Ideal.mem_sup_right (sub_mem_I bk f g _))
      · rw [← map_pow, hp]
      · rw [← map_pow, hp]
    have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
      rw [span_teich]; exact Submodule.mem_top
    change φ1 w = φ2 w
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ht z
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, hx]
      exact congrArg (· * φ2 x) (RingHom.congr_fun hz c)
  · rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f]
    change Ideal.map f.f (Ideal.span ({bk.E} : Set bk.prism.A)) = _
    rw [Ideal.map_span]
    exact congrArg Ideal.span (Set.image_singleton (f := f.f) (a := bk.E))

end GlobalTheory.BSP.IdealSubMembership
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdealStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧ B.I = Ideal.span {BK.hf f bk.E} := by
  first | exact @GlobalTheory.BSP.IdealSubMembership.main | exact GlobalTheory.BSP.IdealSubMembership.main | (intros; apply GlobalTheory.BSP.IdealSubMembership.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (TwDatum Twisted SameBelow SamePair LiesUnder TwistedPlaceSettings namedPrimes expDat GoodDatum GoodSystem
  recorded ExistsChoice WithToricIntegralityConstant FamTwGood TwGoodClosed)

namespace GlobalTheory.TwistGoodCompare

variable {D : D7}

def AtPlace (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w, Twisted D w → LiesUnder D (t w).1 w ∨ LiesUnder D (t w).1 (D.what₂.places.conj w)

theorem isUnit_of_toOe (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w))
    (h : IsUnit (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
      (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
        (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))) : IsUnit y := by
  haveI := c.Oe_loc w
  have h1 := (isUnit_map_iff _ _).1 h
  clear h
  generalize c.k' w = k at h1
  generalize c.twI w = i at y k h1
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)
  have h2 := (isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1
  by_contra hy
  have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero] at this
    exact (D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)
  have hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_
    rw [← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]
    exact D.ntw.O_l i
  have hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hy
  rw [← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap] at hm
  exact hm h2

theorem pos_iff_not_isUnit (c : NChoice D) (w : D.what₂.places.Pl) (x : D.what₂.LL) (z : c.Oe w)
    (h : c.embW w x = algebraMap (c.Oe w) (FractionRing (c.Oe w)) z) :
    0 < D.what₂.places.val w x ↔ ¬ IsUnit z := by
  rcases eq_or_ne x 0 with rfl | h0
  · have : z = 0 := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])
    simp [this]
  have hx : 0 ≤ D.what₂.places.val w x := (c.embW_w w x).2 ⟨z, h.symm⟩
  have hmul := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ h0, AddValuation.map_one] at hmul
  have e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
    rw [D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)] at *
    norm_cast at *
    omega
  rw [e1, c.embW_w, not_iff_not]
  have hz : c.embW w x ≠ 0 := by simpa using h0
  constructor
  · rintro ⟨u, hu⟩
    refine IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)
    rw [map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]
  · rintro ⟨u, rfl⟩
    refine ⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    rw [map_inv₀, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ x' : ↥D.LL0, (x' : D.what₂.LL) = star (x : D.what₂.LL) := by
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  exact ⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩

theorem liesUnder_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) :
    LiesUnder D (c.twI w) (if c.sd w then w else D.what₂.places.conj w) := by
  intro x
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w))
      (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' =
      D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y) := by
    intro x' hx'
    have e := h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])
    simp only [map_one, mul_one] at e
    rw [pos_iff_not_isUnit c w _ _ e, not_iff_not]
    exact ⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩
  rw [hleft]
  cases hs : c.sd w
  · obtain ⟨x', hx'⟩ := exists_star hG (x : ↥D.LL0)
    rw [if_neg (by simp), D.conj_val, ← hx']
    refine (key x' ?_).symm
    rw [hs, if_neg (by simp)]
    exact D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])
  · rw [if_pos rfl]
    exact (key x (by rw [hs, if_pos rfl])).symm

theorem atPlace_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) : AtPlace (recorded c) := by
  intro w _
  have := liesUnder_of_tie hG h w
  split_ifs at this
  exacts [Or.inl this, Or.inr this]

end GlobalTheory.TwistGoodCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimplificationCharpoly

private theorem charpoly_eq_of_filtration_graded_eq {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (G : ℕ → Submodule k V)
      (f g : Module.End k V), Monotone G → G 0 = ⊥ → G n = ⊤ → (∀ i, ∀ x ∈ G i, f x ∈ G i) →
      (∀ i, ∀ x ∈ G (i + 1), g x - f x ∈ G i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  induction n with
  | zero =>
    intro V _ _ _ G f g _ h0 hn _ _
    have hV : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ G 0 := by rw [hn]; exact Submodule.mem_top
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hfg : f = g := by
      ext x
      rw [hV x, map_zero, map_zero]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ G f g hmono h0 hn hf hd

    have hg : ∀ i, ∀ x ∈ G i, g x ∈ G i := by
      intro i x hx
      cases i with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx, map_zero]
        exact Submodule.zero_mem _
      | succ j =>
        have e : g x = f x + (g x - f x) := by abel
        rw [e]
        exact Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))
    set A := G n with hA
    rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n),
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]
    congr 1
    ·
      refine ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n))
        (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_
      · rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
      · exact Submodule.comap_subtype_self A
      · intro i x hx
        exact hf i x hx
      · intro i x hx
        exact hd i x hx
    ·
      congr 1
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      have hx : x ∈ G (n + 1) := by rw [hn]; exact Submodule.mem_top
      have := hd n x hx
      rw [← neg_mem_iff, neg_sub] at this
      exact this

theorem charpoly_eq_of_filtration {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (F : ℕ → Submodule k V)
      (f g : Module.End k V), F 0 = ⊥ → F n = ⊤ → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
      (∀ i, ∀ x ∈ F (i + 1), g x - f x ∈ F i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  intro V _ _ _ F f g h0 hn hf hd

  refine charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_
  · simp only [partialSups_zero, h0]
  · exact eq_top_iff.mpr (hn ▸ le_partialSups F n)
  · intro i
    have hle : partialSups F i ≤ (partialSups F i).comap f := by
      refine partialSups_le F i _ (fun j hj x hx => ?_)
      exact le_partialSups_of_le F hj (hf j x hx)
    exact fun x hx => hle hx
  · intro i
    have hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f) := by
      refine partialSups_le F (i + 1) _ (fun j hj x hx => ?_)
      cases j with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx]
        exact Submodule.zero_mem _
      | succ m =>
        exact le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)
    exact fun x hx => hle hx

theorem charpoly_eq : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V),
    GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ →
      ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  intro k Γ _ _ W _ _ _ V _ _ _ s ρ hss g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss
  obtain ⟨-, m, Ws, e, hst, hint, hρ⟩ := hss
  have hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j := by
    intro j x hx
    have h := hst j
    unfold Stable at h
    exact h g x hx

  let H : ℕ → Submodule k W := fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j
  have hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i := by
    intro i
    have hle : H i ≤ (H i).comap (s g) :=
      iSup₂_le fun j hj x hx =>
        (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)
    exact fun x hx => hle hx
  rw [← e.charpoly_conj (s g)]
  refine charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g)
    ?_ ?_ ?_ ?_
  · have h0 : H 0 = ⊥ := by simp [H]
    simp only [h0, Submodule.map_bot]
  · have hm : H m = ⊤ := by
      rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
      exact iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt
    simp only [hm, Submodule.map_top, LinearEquiv.range]
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    simpa [LinearEquiv.conj_apply] using hH i _ hx
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx
    have hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap
        ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V)) := by
      refine iSup₂_le fun j hj v hv => ?_
      have hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i :=
        iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j'
          (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))
      have h1 := Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)
      simpa [LinearEquiv.conj_apply] using h1
    have h2 := hle hx
    simpa using h2

end GlobalTheory.SemisimplificationCharpoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfParts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfParts
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem firstAdmissibilityAt_of_parts : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  intro D bkP i s h1 h2 h3 h4
  exact ⟨h1, h2, fun v => (h3 v).1, fun v => (h3 v).2, h4⟩

end GlobalTheory.TripleGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfPartsStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  first | exact @GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | exact GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | (intros; apply GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecompForms

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  intro D i r ρ π
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩

end GlobalTheory.DecompForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecompStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDecomp_iff_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  first | exact @GlobalTheory.DecompForms.main | exact GlobalTheory.DecompForms.main | (intros; apply GlobalTheory.DecompForms.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducesWAndExistsEmb
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalEmbedding

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (φ : ↥K →ₐ[ℚ_[l]] ↥L) (y : ↥K) : ‖((φ y : ↥L) : PadicAlgCl l)‖ = ‖(y : PadicAlgCl l)‖ := by
  have h1 : minpoly ℚ_[l] ((φ y : ↥L) : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.val.comp φ) (L.val.comp φ).toRingHom.injective y
  have h2 : minpoly ℚ_[l] (y : PadicAlgCl l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq K.val K.val.toRingHom.injective y
  change spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem inducesW_and_exists_emb : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → InducesW D.nd i τ w ∧ ∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp τ = D.host.emb g := by
  intro D i w hw LL' τ' τ h
  refine ⟨fun x => ?_, ?_⟩
  · rw [mem_place_iff D i w hw x, h, norm_algHom τ']
    exact Iff.rfl
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((D.naut.iotaQC i).toRingHom.comp τ)
    exact ⟨g, hg.symm⟩

end GlobalTheory.LocalEmbedding

end
end
