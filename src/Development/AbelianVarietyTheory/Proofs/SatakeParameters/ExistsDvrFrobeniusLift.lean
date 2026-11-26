module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.UnramCompletion

variable {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))

theorem intValuation_eq_of_notMem_sq {a : 𝓞 E} (h1 : a ∈ Q.asIdeal) (h2 : a ∉ Q.asIdeal ^ 2) :
    Q.intValuation a = exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (Q.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := mt (Q.intValuation_le_pow_iff_mem a 2).1 h2
  have h0 : Q.intValuation a ≠ 0 := Q.intValuation_ne_zero a ha
  rw [← exp_log h0] at e1 e2 ⊢
  rw [exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem ringHom_ext_of_continuous {f g : Q.adicCompletion E → Q.adicCompletion E}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k : E, f (algebraMap E _ k) = g (algebraMap E _ k)) : f = g :=
  (denseRange_algebraMap E Q).equalizer hf hg (funext h)

theorem exists_ringEquiv (c : E ≃+* E) (hc : Mem.Chr.ConjPl c Q Q) :
    ∃ σ : Q.adicCompletion E ≃+* Q.adicCompletion E, Continuous σ ∧
      (∀ k : E, σ (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (σ x) = Valued.v x := by
  obtain ⟨s, s1, s2, s3⟩ := Mem.Chr.exists_finCompl_map c hc
  obtain ⟨t, t1, t2, -⟩ := Mem.Chr.exists_finCompl_map c.symm ((Mem.Chr.conjPl_symm_iff c Q Q).2 hc)
  refine ⟨RingEquiv.ofRingHom s t ?_ ?_, s1, s2, s3⟩
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (s1.comp t1) continuous_id fun k => by
      simp [s2, t2])
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (t1.comp s1) continuous_id fun k => by
      simp [s2, t2])

theorem intAt_iff (x : E) : Formalism.L2.Col.IntAt Q x ↔ Q.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 := congrArg (Q.valuation E) h
    rw [map_mul, (valuation_eq_one_iff_notMem Q).2 hs, one_mul] at h1
    rw [h1]
    exact Q.valuation_le_one r
  · intro hx
    obtain ⟨n, d, h⟩ := Q.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

end GlobalTheory.UnramCompletion

open Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory.UnramCompletion

end GlobalTheory.UnramCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPow
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    IntAt P a ↔ a ∈ (P.valuation E).integer := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, Valuation.mem_integer_iff]

theorem mem_stdAt {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := by
  letI : StarRing E := starRingOfComm
  exact mem_localization_standardLattice P x

theorem intAt_mulVec (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a b, IntAt P (A a b)) (w : Fin n → E) (hw : ∀ i, IntAt P (w i)) (i : Fin n) :
    IntAt P ((A *ᵥ w) i) := by
  rw [intAt_iff_mem]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ ((intAt_iff_mem P _).1 (hA i j)) ((intAt_iff_mem P _).1 (hw j))

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_of_cong (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d : ℕ) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b))) (a b : Fin n) :
    IntAt P (M a b) := by
  have hq : ((qOf P : E) ^ d) ≠ 0 := pow_ne_zero _ (qOf_ne_zero P)
  have e : M a b = (1 : Matrix (Fin n) (Fin n) E) a b +
      (qOf P : E) ^ d * (((qOf P : E) ^ d)⁻¹ * (M a b - (1 : Matrix (Fin n) (Fin n) E) a b)) := by
    field_simp
    ring
  rw [e, intAt_iff_mem]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ ?_ ((intAt_iff_mem P _).1 (h a b)))
  · rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · exact Subring.pow_mem _ (natCast_mem _ _) _

theorem map_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n →ₗ[E] Sp E n)
    (hf : ∀ a b, IntAt P (LinearMap.toMatrix' f a b)) {x : Sp E n} (hx : x ∈ stdAt E n P) :
    f x ∈ stdAt E n P := by
  rw [mem_stdAt] at hx ⊢
  intro i
  rw [← LinearMap.toMatrix'_mulVec]
  exact intAt_mulVec P _ hf x hx i

theorem glint_of_cong {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ *
      (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P := by
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => map_stdAt P g.toLinearMap (intAt_of_cong P d _ hg) hx⟩, ?_⟩
  · have := map_stdAt P g.symm.toLinearMap (intAt_of_cong P d _ hg') hx
    simpa using this
  · intro w hw
    set A : Matrix (Fin n) (Fin n) E :=
      ((qOf P : E) ^ d)⁻¹ • (LinearMap.toMatrix' g.toLinearMap - (1 : Matrix (Fin n) (Fin n) E)) with hA
    have hAi : ∀ a b, IntAt P (A a b) := by
      intro a b
      simpa [hA, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hg a b
    have e : ((qOf P : E) ^ d)⁻¹ • (g w - w) = A *ᵥ w := by
      have h1 : (g w : Sp E n) = LinearMap.toMatrix' g.toLinearMap *ᵥ w := by
        rw [LinearMap.toMatrix'_mulVec]; rfl
      rw [hA, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← h1]
    rw [e, mem_stdAt]
    rw [mem_stdAt] at hw
    exact intAt_mulVec P _ hAi w hw

end GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPowStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n),
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  g ∈ Formalism.L2.Col.GLint E n P ∧ ∀ w ∈ Formalism.L2.Col.stdAt E n P, ((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ • (g w - w) ∈ Formalism.L2.Col.stdAt E n P := by
  first | exact @GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | exact GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | (intros; apply GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem exists_primitiveRoot_of_good {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hmem : ζ ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) (IntermediateField.subset_adjoin _ _ ?_)
    simpa using hζ.pow_eq_one
  have hLL : ζ ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨ζ, hmem⟩
  refine ⟨⟨ζ, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ LL.1.val.toRingHom.injective

theorem setCS_of_wordsAT {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
    (hG : Good K 1 LL) (Wc : Wach P K LL) (hs : Wc.s = 1) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h11 : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) (d : ℕ)
    (hA : WordsAT l Wd d) (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L) (hF : F.Onto)
    (c₁ : IsCrys (P.PD K) T₁.ρ) (c₂ : IsCrys (P.PD K) T₂.ρ)
    (hj : ∀ a, TruncatedSeriesCountingBounds.JumpsAt Wc T₁ a (Wd.win a))
    (hlow : ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), TruncatedSeriesCountingBounds.lowCount Wc T₂ a Wd.η ≤ (Wd.m : ℤ)) :
    RamifiedCoefficientChains.SetCS Wc d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  classical
  obtain ⟨hev, hup, -, -, hbig⟩ := hA
  have hp : (P.PD K).p = l := P.PD_p K
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod (Module.finrank ℚ_[l] ↥(K0 K))))
    Finset.univ_nonempty Wd.sz
  have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
    refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Finset.le_sup (Finset.mem_univ a)
  have hbig' := hbig _ hgr
  refine ⟨⟨?_, hs, by omega⟩, by omega, hev, ?_, by rw [hp]; exact exists_primitiveRoot_of_good hG, ⟨c₁, c₂, hF⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩⟩
  · exact (goodO_finExt_integers l LL).1
  · intro a τ hτ u hu
    have hw := hj a τ hτ u hu
    have hua := hup a
    unfold NWord.win at hw
    unfold RamifiedCoefficientChains.JumpWinS
    by_cases hpar : (a.val + d) % 2 = 1
    · have h0 : ¬ (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = true := by simpa [hpar] using hua
      simp only [hu1, if_true, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_false, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
    · have h0 : (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = false := by simpa [hpar] using hua
      simp only [hu1, Bool.false_eq_true, if_false, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_true, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
  · intro a τ hτ
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have h := hlow ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over Wc τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over P K LL Wc hK a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · intro a
    have h := (hbig' a).2
    rw [hp]
    unfold RamifiedCoefficientChains.aR RamifiedCoefficientChains.lam RamifiedCoefficientChains.hpar
    push_cast
    exact h
  · intro a
    have h := (hbig' a).1
    unfold RamifiedCoefficientChains.hpar
    push_cast
    exact h

theorem settingC_of_wordsAT : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  intro D L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F h₁ h₂ hF
  have hT1 := hB.t1 T₁ h₁
  have hT2 := hB.t2 T₂ h₂
  exact setCS_of_wordsAT hG (WW HW i w hw Cx hG) ((HW (D.nd.l i)).W_s _ 1 _ hG) hB.unram h11 Wd d hA
    T₁ T₂ F hF hT1.1 hT2.1 hT1.2.1 hT2.2

end GlobalTheory.HTW.RecS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjectionStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  first | exact @GlobalTheory.HTW.RecS.settingC_of_wordsAT | exact GlobalTheory.HTW.RecS.settingC_of_wordsAT | (intros; apply GlobalTheory.HTW.RecS.settingC_of_wordsAT <;> assumption)
end
end
