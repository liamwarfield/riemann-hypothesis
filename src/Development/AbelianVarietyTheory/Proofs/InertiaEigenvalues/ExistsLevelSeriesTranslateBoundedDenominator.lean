module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePart
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePart
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isIntegral_of_finAdele_valuation_le_one {E : Type} [Field E] [NumberField E] (x : E)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q) ≤ 1) :
    IsIntegral ℤ x := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E x fun Q => by
    have := h Q
    rwa [show (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) Q = (x : Q.adicCompletion E) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem map_fin_eq_of_isRat (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) (hR : GlobalTheory.Member.IsRat V γ γ') :
    Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1 =
      Matrix.GeneralLinearGroup.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) γ' := by
  have hf : (fin V γ).1 = finHom V γ := rfl
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  rw [hf]
  simp only [finHom, MonoidHom.comp_apply]
  rw [show matHom V γ = _ from hR]
  simp only [Formalism.UG.bc, Matrix.GeneralLinearGroup.map, incA, inclR, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe, Matrix.GeneralLinearGroup.map_apply]
  change ι ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (Algebra.TensorProduct.includeRight ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b))) = algebraMap D.host.E _ ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact h1 _

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem exists_coprime_isIntegral_of_bnd {E : Type} [Field E] [NumberField E] {n : ℕ} (l c : ℕ)
    (A : Matrix (Fin n) (Fin n) E)
    (h : GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 E) E)) •
      A.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)))) :
    ∃ m : ℕ, m.Coprime l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * A a b) := by
  obtain ⟨m, hm, hv⟩ := h
  refine ⟨m, hm, fun a b => isIntegral_of_finAdele_valuation_le_one _ fun Q => ?_⟩
  have := hv a b Q
  simpa [Matrix.smul_apply, Matrix.map_apply, map_mul, mul_assoc] using this

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem denomAt_of_isRat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → ∀ (V : HSp D) (l c : ℕ) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), GlobalTheory.Member.IsRat V γ γ' → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1).1) → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1)⁻¹.1) → DenomAt l c γ' := by
  intro D ι h1 V l c γ γ' hR hb1 hb2
  have hM := map_fin_eq_of_isRat D ι h1 V γ γ' hR
  rw [hM] at hb1 hb2
  rw [← map_inv] at hb2
  obtain ⟨m₁, hm₁, hi₁⟩ := exists_coprime_isIntegral_of_bnd l c (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb1
  obtain ⟨m₂, hm₂, hi₂⟩ := exists_coprime_isIntegral_of_bnd l c ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) hb2
  have hn : ∀ k : ℕ, IsIntegral ℤ (k : D.host.E) := fun k => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (k : ℤ)))
  refine ⟨m₁ * m₂, Nat.Coprime.mul_left hm₁ hm₂, fun a b => ⟨?_, ?_⟩⟩
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₂ : D.host.E) * ((((m₁ * l ^ c : ℕ) : D.host.E)) * (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₂).mul (hi₁ a b)
  · have e : (((m₁ * m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b =
        (m₁ : D.host.E) * ((((m₂ * l ^ c : ℕ) : D.host.E)) * ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := by
      push_cast; ring
    rw [e]; exact (hn m₁).mul (hi₂ a b)

end GlobalTheory.LevelSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePartStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → ∀ (V : HSp D) (l c : ℕ) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), GlobalTheory.Member.IsRat V γ γ' → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1).1) → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1)⁻¹.1) → DenomAt l c γ' := by
  first | exact @GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd | exact GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd | (intros; apply GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOver
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.FinOneAt


set_option maxHeartbeats 1600000 in
theorem oneAt_fin_eq_one : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (HeightOneSpectrum.under (𝓞 D.host.F) P) - algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) P)) k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v ((ι (a ⊗ₜ[D.host.F] 1)) P - algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → ∀ (V : HSp D) (l : ℕ) (z : GA D V), OneAt V l z → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι hι hint happ V l z hz Q hlQ i j
  let α : Af D.host.F := singleV D.host.F (Q.under (𝓞 D.host.F)) 1
  have hε : IsPlaceIdem D (Q.under (𝓞 D.host.F)) (pairA D.host.F 0 α) :=
    ⟨α, rfl, GlobalTheory.PlaceIdem.single_same _, fun v' h => GlobalTheory.PlaceIdem.single_ne h⟩
  have hlv : ((l : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) Q.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hlQ
  have h0 := hz _ _ hε hlv i j
  have hα : ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) Q = 1 := by
    change ι (α ⊗ₜ[D.host.F] (1 : D.host.E)) Q = 1
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ α 1 Q n (by
      rw [map_one, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h1 : ι (finPart D ((Formalism.L2.Theta.mt V z - 1) i j)) Q = 0 := by
    have := congrArg (fun x => ι (finPart D x) Q) h0
    simp only [map_mul, map_zero] at this
    rw [GlobalTheory.PlaceIdem.mul_ap, hα, one_mul] at this
    exact this
  have hm : ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) = ι (finPart D (Formalism.L2.Theta.mt V z i j)) := rfl
  rw [hm]
  rw [Matrix.sub_apply, map_sub, map_sub] at h1
  refine (sub_eq_zero.1 h1).trans ?_
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    exact congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) (map_zero ι)

end GlobalTheory.LevelSeries.FinOneAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOverStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (HeightOneSpectrum.under (𝓞 D.host.F) P) - algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) P)) k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v ((ι (a ⊗ₜ[D.host.F] 1)) P - algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → ∀ (V : HSp D) (l : ℕ) (z : GA D V), OneAt V l z → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  first | exact @GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one | exact GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one | (intros; apply GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOver
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem exists_pow_mul_v_le_one_of_mem {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∈ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ a : ℕ, ∀ d : ℕ, a ≤ d → Valued.v (((p ^ d : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  set e := N.factorization p with he
  set r := N / p ^ e with hr
  have hcop : r.Coprime p := (Nat.coprime_ordCompl hp hN0).symm
  have hsplit : p ^ e * r = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hrQ : (r : 𝓞 E) ∉ Q.asIdeal := by
    intro hrQ
    have h1 : ((Nat.gcd r p : ℕ) : ℤ) = r * Nat.gcdA r p + p * Nat.gcdB r p := Nat.gcd_eq_gcd_ab r p
    rw [hcop] at h1
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h1
    push_cast at h2
    have h3 : (1 : 𝓞 E) ∈ Q.asIdeal := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hrQ) (Ideal.mul_mem_right _ _ hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have hvr : Valued.v ((r : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (r : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (r : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hrQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e' : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e', mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hex : Valued.v (((p ^ e : ℕ) : Q.adicCompletion E) * x) ≤ 1 := by
    rw [← hsplit] at hNx
    rw [Nat.cast_mul, mul_comm ((p ^ e : ℕ) : Q.adicCompletion E), mul_assoc, Valuation.map_mul,
      hvr, one_mul] at hNx
    exact hNx
  refine ⟨e, fun d hd => ?_⟩
  have hde : p ^ d = p ^ (d - e) * p ^ e := by rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hde, Nat.cast_mul, mul_assoc, Valuation.map_mul]
  exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) hex

theorem exists_pow_clears_denom_over :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  intro E _ _ p hp n A
  classical
  have h0 : Ideal.span {(p : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hF := Ideal.finite_factors h0
  have hmemF : ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal →
      Q ∈ {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {(p : 𝓞 E)}} := fun Q hQ =>
    Ideal.dvd_span_singleton.mpr hQ
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : (p : 𝓞 E) ∈ t.1.asIdeal then
      Classical.choose (exists_pow_mul_v_le_one_of_mem p hp t.1 h ((A t.2.1 t.2.2) t.1)) else 0
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hF.toFinset ×ˢ Finset.univ
  refine ⟨T.sup f, fun d hd Q hQ i j => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  have hmem : (Q, i, j) ∈ T := by
    simp only [T, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ, and_true]
    exact hmemF Q hQ
  have hle : f (Q, i, j) ≤ d := le_trans (Finset.le_sup hmem) hd
  have hspec := Classical.choose_spec (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q))
  have hfQ : f (Q, i, j) = Classical.choose (exists_pow_mul_v_le_one_of_mem p hp Q hQ ((A i j) Q)) := by
    simp only [f, dif_pos hQ]
  exact hspec d (hfQ ▸ hle)

end GlobalTheory.StdAtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOverStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  first | exact @GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | exact GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | (intros; apply GlobalTheory.StdAtPrime.exists_pow_clears_denom_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegral
open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

theorem bnd_of_integral_over_prime : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  intro E _ _ p hp n A hA
  let S : Set (HeightOneSpectrum (𝓞 E)) := {Q | ∃ i j, ¬ Valued.v ((A i j) Q) ≤ 1}
  have hS : S.Finite := by
    have hsub : S ⊆ ⋃ i, ⋃ j, {Q | ¬ (A i j) Q ∈ Q.adicCompletionIntegers E} := by
      rintro Q ⟨i, j, h⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨i, j, fun hm => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm)⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_) hsub
    exact Filter.eventually_cofinite.mp (A i j).2
  refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
  · have hpQ : (p : 𝓞 E) ∉ Q.asIdeal := by
      obtain ⟨i', j', h⟩ := hQ
      exact fun hm => h (hA Q hm i' j')
    exact exists_coprime_natCast_mul_v_le_one p hp Q hpQ _
  · by_contra h
    exact hQ ⟨i, j, h⟩

end GlobalTheory.StdAtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegralStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), (∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((A i j) Q) ≤ 1) → GlobalTheory.StdAtPrime.Bnd p A := by
  first | exact @GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | exact GlobalTheory.StdAtPrime.bnd_of_integral_over_prime | (intros; apply GlobalTheory.StdAtPrime.bnd_of_integral_over_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePower
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

open GlobalTheory.StdAtPrime

namespace GlobalTheory.MoveDenom


set_option maxHeartbeats 1600000 in
theorem denomAt_of_move : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  intro D V hstd l hl s
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  obtain ⟨c1, hc1⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1).1
  obtain ⟨c2, hc2⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1)⁻¹.1
  refine ⟨max c1 c2, ?_⟩
  intro z hz γ h γ' k bad hrat hlb hsob hk hk' heq
  set C : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ((l ^ max c1 c2 : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) with hC
  have bs : Bnd l (C • (M (fin V s).1).1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc1 _ (le_max_left _ _) Q hQ i j
  have bs' : Bnd l (C • (M (fin V s).1)⁻¹.1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 _ (le_max_right _ _) Q hQ i j
  have ez := GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt D ι h1 h2 h3 V l z hz
  have bz : Bnd l (M (fin V z).1).1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [ez Q hQ i j]; exact one_entry_v_le_one _ Q i j
  have bz' : Bnd l (M (fin V z).1)⁻¹.1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [inv_eq_one_off _ _ Q (ez Q hQ) i j]; exact one_entry_v_le_one _ Q i j
  have bk' : Bnd l (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k hk
  have bk : Bnd l (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k⁻¹ hk'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨-, e', P', he', hb', hs'⟩ := hsob
  have hp' : ∀ PP ∈ P', (l : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hlb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj l e' P' he' hp'
  obtain ⟨bh, bh'⟩ := GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite l hl _ (M (fin V h).1) S hSf hSp fun Q hQ i j =>
    GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e' h hs' Q (hS0 Q hQ) i j
  have eγ : fin V γ = fin V s * fin V z * k⁻¹ * (fin V h)⁻¹ := by
    have e1 : fin V (s * z) = fin V s * fin V z := map_mul _ _ _
    rw [e1] at heq
    rw [heq]; group
  have eMγ : M (fin V γ).1 = M (fin V s).1 * M (fin V z).1 * (M k.1)⁻¹ * (M (fin V h).1)⁻¹ := by
    rw [eγ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      map_mul, map_mul, map_mul, map_inv, map_inv]
  apply GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart D ι h1 V l (max c1 c2) γ γ' hrat
  · rw [eMγ, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul]
    exact bnd_mul l _ _ _ (bnd_mul l _ _ _ (bnd_mul l _ _ _ bs bz) bk') bh'
  · rw [eMγ, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv,
      Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.mul_smul]
    exact bnd_mul l _ _ _ bh (bnd_mul l _ _ _ bk (bnd_mul l _ _ _ bz' bs'))

end GlobalTheory.MoveDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePowerStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  first | exact @GlobalTheory.MoveDenom.denomAt_of_move | exact GlobalTheory.MoveDenom.denomAt_of_move | (intros; apply GlobalTheory.MoveDenom.denomAt_of_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslates
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isThetaFunO_of_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hψ : IsStdChar D ψ (-1) := hP.1.weil.std
  have h0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hP.2.2.2.2.2.2.2.2
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, -, rfl⟩ := hx
    exact GlobalTheory.AnisoMean.isTheta_heisO hψ h0 y
  | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ V W
  | add x y _ _ hx hy => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (a : ℂ) hx

end GlobalTheory.LevelSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslatesStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  first | exact @GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | exact GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | (intros; apply GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandard
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LatOpen.exists_open_hLat_std : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V h1
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup V 1).map (finHom V).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup V one_pos, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  rw [← h1]
  have hk' := GlobalTheory.Member.PrincLevel.finCong_inv hk.2
  have hm := GlobalTheory.Member.PrincLevel.finCong_map hk.2
  have hm' := GlobalTheory.Member.PrincLevel.finCong_map hk'
  have hL := GlobalTheory.StdFrameCong.pj_latHat_eq V
  have e1 : ((((finHom V).rangeRestrict k)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = finHom V k⁻¹ := by
    rw [← map_inv]; rfl
  have e0 : (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [inv_one]; rfl
  unfold Bridge.hLat
  refine congrArg (Submodule.span _) (Set.ext fun v => ?_)
  show _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _ ∈ latHat D.host.F D.host.E (L0c D V)
  rw [e1, e0, Units.val_one, Matrix.one_mulVec, ← hL]
  constructor
  · intro h
    have := hm _ h
    have ekk : (finHom V k).1 * (finHom V k⁻¹).1 = 1 := by
      rw [← Units.val_mul, ← map_mul (finHom V) k k⁻¹, mul_inv_cancel k, map_one, Units.val_one]
    rwa [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
  · exact hm' _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandardStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  first | exact @GlobalTheory.LatOpen.exists_open_hLat_std | exact GlobalTheory.LatOpen.exists_open_hLat_std | (intros; apply GlobalTheory.LatOpen.exists_open_hLat_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominator
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries


set_option maxHeartbeats 1600000 in
theorem exists_move_denomAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl s hs
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hP.2.2.1, hP.2.2.2.2.2.2.1]
  obtain ⟨c, hc⟩ := GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power D V hstd l hl s
  refine ⟨c, fun z hz hOne M bad hM hbad hlb => ?_⟩
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard D V hstd
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  have hJo : IsOpen ((J₁ ⊓ J₂ : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := hJ₁o.inter hJ₂o
  obtain ⟨γ, h, kJ, hsp, e⟩ := GlobalTheory.SplitRepsOpen.exists_rep_splitOffBad D V (J₁ ⊓ J₂) bad hbad hJo (fin V (s * z))
  obtain ⟨k', hk', ek⟩ := Formalism.IndefR.TopMult.exists_lift (kJ : Bridge.Gf V)
  obtain ⟨a, ha_def⟩ : ∃ a : GA D V, a = h⁻¹ * ((γ : GA D V)⁻¹ * (s * z) * k'⁻¹) := ⟨_, rfl⟩
  have hfa : finHom V a = 1 := by
    have e' := congrArg Subtype.val e
    have ek' := congrArg Subtype.val ek
    simp only [MonoidHom.coe_rangeRestrict, Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul] at e' ek'
    rw [ha_def, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, ek', e']
    group
  have ha : a ∈ GinfC V := hfa
  have hγa : (γ : GA D V) * a ∈ GfC V := by
    have h1 : infHom V h = 1 := hsp.1
    have h2 : infHom V (s * z) = 1 := mul_mem hs hz
    have h3 : infHom V k' = 1 := hk'
    show infHom V ((γ : GA D V) * a) = 1
    rw [ha_def, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, h3]
    group
  have hs' : s * z = (γ : GA D V) * (h * a) * k' := by
    rw [ha_def]; group
  obtain ⟨γ', -, hγ'⟩ := γ.2
  have hrat : GlobalTheory.Member.IsRat V (γ : GA D V) γ' := hγ'.symm
  have hkJ : (kJ : Bridge.Gf V) ∈ J₁ := (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).1
  have hkJ' : ((kJ : Bridge.Gf V))⁻¹ ∈ J₁ := inv_mem hkJ
  have hden : DenomAt l c γ' := hc z hOne (γ : GA D V) h γ' kJ bad hrat hlb hsp (hJ₁ _ hkJ) (hJ₁ _ hkJ') e
  refine ⟨γ, h, a, γ', γ.2, hrat, ha, hγa, hsp, hden, fun e O f hf BW Q g => ?_⟩
  have hω := hP.1.weil
  have hθ : IsInfFam θ := hP.1.inf
  have hfix : om (k', 1) f = f := by
    have hk2 : fin V k' ∈ J₂ := by
      have ek2 : fin V k' = kJ := ek
      rw [ek2]; exact (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).2
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, hy, rfl⟩ := hx
      exact hJ₂ k' hk' hk2 y hy
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul r x _ hx =>
      change om (k', 1) ((r : ℂ) • x) = (r : ℂ) • x
      rw [map_smul, hx]
  have hthf : IsThetaFunO ψ V W f := GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hT : ∀ P, IsThetaFunO ψ V W (stdF ψ θ V W sW BW f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ hthf P
  have hk1 : om (k', 1) (stdF ψ θ V W sW BW f Q) = stdF ψ θ V W sW BW f Q := by
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χV χW om hθ hω (fun _ => 1) sW (fun _ => 1) BW f hT k' hk' 1
      (one_mem _) 1 (by rw [one_smul]; exact hfix) Q
    rw [one_smul] at this
    exact this
  have hp : ((s * z, g) : GA D V × GA D W) = ((γ : GA D V), 1) * ((h, g) * (a, 1)) * (k', 1) := by
    rw [hs']; simp [Prod.mk_mul_mk]
  have e1 : om (s * z, g) = om ((γ : GA D V), 1) * (om (h, g) * om (a, 1)) * om (k', 1) := by
    rw [hp, map_mul, map_mul, map_mul]
  have hth := hω.om_pres ((h, g) : GA D V × GA D W) _ (hω.om_pres ((a, 1) : GA D V × GA D W) _ (hT Q))
  show om (s * z, g) (stdF ψ θ V W sW BW f Q) 0 = om (h, g) (om (a, 1) (stdF ψ θ V W sW BW f Q)) 0
  rw [e1, Module.End.mul_apply, Module.End.mul_apply, hk1, Module.End.mul_apply,
    hω.om_aut _ γ.2 1 (one_mem _) _ hth]

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominatorStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelSeries_translate_boundedDenominator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  first | exact @GlobalTheory.LevelSeries.exists_move_denomAt | exact GlobalTheory.LevelSeries.exists_move_denomAt | (intros; apply GlobalTheory.LevelSeries.exists_move_denomAt <;> assumption)
end
