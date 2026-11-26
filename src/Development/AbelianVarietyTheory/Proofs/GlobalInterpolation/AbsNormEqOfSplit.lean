module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodules
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.BadPrimes

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_cofactor {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal := by
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hP]
  rcases P.isPrime.mul_le.1 hle with h | h
  · have : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q', hQ, hm⟩
  · have : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q, hQ.symm, hm.trans (mul_comm _ _)⟩

theorem absNorm_eq_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hq : (Ideal.absNorm v.asIdeal).Prime) {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P', -, hm⟩ := exists_cofactor hs hP
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E), ← h2,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E]
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hP2 : Ideal.absNorm P'.asIdeal ≠ 1 := fun h => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact (((Nat.Prime.mul_eq_prime_sq_iff hq hP1 hP2).1 h1)).1

theorem notMem_sq_of_split {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {a : 𝓞 F} (ha : a ∉ v.asIdeal ^ 2)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  intro hm2
  obtain ⟨P', hne, hm⟩ := exists_cofactor hs hP
  have hav : a ∈ v.asIdeal := by
    rw [← hP, Ideal.under_def, Ideal.mem_comap]
    exact Ideal.pow_le_self two_ne_zero hm2
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hav
  have h1 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) J) := by
    rw [← mul_assoc, ← hm, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton, ← sq]
    exact hm2
  have h3 := (mul_dvd_mul_iff_left P.ne_bot).1 h1
  rcases P.prime.dvd_or_dvd h3 with h | h
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.le_of_dvd h))).symm
  · have h4 : J ≤ v.asIdeal := by
      rw [← hP, Ideal.under_def, ← Ideal.map_le_iff_le_comap]
      exact Ideal.le_of_dvd h
    apply ha
    rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
    exact Ideal.mul_mono_right h4

end Split


open GlobalTheory.Proof.NarrowJetMoments in
theorem bad_primes : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ (((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u) := by
  classical
  intro X Pr sel S mu u hX hPr hsel hT hg P hP
  have hoff : ∀ Q ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hQ
  have hmem : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    exact Finset.mem_union
  rcases (hmem P).1 hP with h | h
  · have hTP := T_mem hPr u ⟨P, h⟩
    refine ⟨fun hc => ?_, ?_, ?_, fun _ => h, fun _ => hTP⟩
    · rcases (hmem _).1 hc with h' | h'
      · apply conj_piT_notMem hPr u ⟨P, h⟩
        exact (mem_conjP P _).1 (decoFin_mem_of_mem_divs h')
      · exact hoff _ h' (natCast_mem_conjP.2 hTP)
    · rw [hPr.vT_norm u P h]
      exact hPr.T_prime u
    · rw [hPr.vT_norm u P h]
      exact (T_unif hX hPr u ⟨P, h⟩).2
  · have hn := hoff P h
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (hmem _).1 hc with h' | h'
      · exact hn (natCast_mem_conjP.1 (T_mem hPr u ⟨_, h'⟩))
      · exact conjP_notMem_rowSG hX hPr hsel hg h h'
    have hlast : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u :=
      ⟨fun h' => absurd h' hn, fun h' => T_mem hPr u ⟨P, h'⟩⟩
    rcases Finset.mem_union.1 h with h1 | h1
    · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h1
      rw [hPr.vG_norm i P hi]
      refine ⟨hPr.g_prime i, ?_, hlast⟩
      have hrk : 2 * X.f = Module.finrank ℚ X.E := by
        rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
        rfl
      have hcc : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
      refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E (cO X.E) (X.conjO (Pr.piG i)) (Pr.g i) cO_cO (hPr.g_prime i) ?_ ?_ ?_
        (hPr.vG_norm i) P hi
      · rw [hcc, mul_comm, hPr.piG_norm i]
      · rw [hcc]
        exact (hPr.piG_cop i).symm
      · rw [← hrk, ← hPr.vG_card i]
        rfl
    · obtain ⟨v, ⟨hs, ⟨hq, hq2⟩, -⟩, rfl⟩ := good_of_mem_QE h1
      rw [absNorm_eq_of_split hX.rankE hs hq (hsel v)]
      refine ⟨hq, ?_, hlast⟩
      have := notMem_sq_of_split hs hq2 (hsel v)
      rwa [map_natCast] at this

end GlobalTheory.ThetaMove.BadPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.NotSmallIso
open NumberField IsDedekindDomain

theorem UpperTheory.Ram.not_dvd_QS_of_notMem_sq :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), H.toHostRaw.Exact → ∀ (E' : Type) [Field E'] [NumberField E'] (_ : E' ≃+* H.E) (P : HeightOneSpectrum (𝓞 E')) (p : ℕ), p.Prime →
      (p : 𝓞 E') ∈ P.asIdeal → (p : 𝓞 E') ∉ P.asIdeal ^ 2 → ¬ p ∣ H.QS ∧ (H.QS : 𝓞 E') ∉ P.asIdeal := by
  intro φ H hex E' _ _ f P p hp hpP hpP2
  haveI hPp : P.asIdeal.IsPrime := P.isPrime
  let g : 𝓞 H.E ≃+* 𝓞 E' := (NumberField.RingOfIntegers.mapRingEquiv f).symm
  let Q : Ideal (𝓞 H.E) := P.asIdeal.comap g
  haveI : Q.IsPrime := Ideal.comap_isPrime g P.asIdeal
  have hndvd : ¬ p ∣ H.QS := by
    intro hdvd
    have hmem : ((p : ℕ) : 𝓞 H.E) ∈ Q := by
      show g (p : 𝓞 H.E) ∈ P.asIdeal
      rw [map_natCast]
      exact hpP
    have h2 := H.mem_sq_of_dvd_QS hex hp hdvd Q hmem
    have h3 : g (p : 𝓞 H.E) ∈ P.asIdeal ^ 2 := Ideal.le_comap_pow g 2 h2
    rw [map_natCast] at h3
    exact hpP2 h3
  refine ⟨hndvd, fun hQS => ?_⟩
  have hcop : p.Coprime H.QS := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hb := Nat.gcd_eq_gcd_ab p H.QS
  rw [hcop.gcd_eq_one] at hb
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 := congrArg (Int.cast : ℤ → 𝓞 E') hb
  push_cast at h1
  rw [h1]
  exact add_mem (P.asIdeal.mul_mem_right _ hpP) (P.asIdeal.mul_mem_right _ hQS)
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.AAUnitAway

theorem natCast_notMem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem exists_den (D : D7) (Q : Ideal (𝓞 D.host.E)) [hQ : Q.IsPrime] {l : ℕ} (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hlQ : (l : 𝓞 D.host.E) ∈ Q) :
    ∃ z : 𝓞 D.host.E, z ∉ Q ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * (z : D.host.E) := by
  have hnot : ¬ D.host.𝔟 ≤ Q := by
    intro hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hle).mul_right _
    exact natCast_notMem hQ.ne_top hlQ (Nat.Coprime.mul_left
      ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_QS D.host hl h2)).symm
      ((Nat.coprime_primes D.host.hyp.1 hl).2 hq.symm)) (D.host.der.diffSupport Q hQ hd)
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem localization_le_of_le_localization₂ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {I J : Submodule (𝓞 E) E}
    (h : I ≤ localization₂ P.asIdeal J) : localization₂ P.asIdeal I ≤ localization₂ P.asIdeal J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP P I x).1 hx
  obtain ⟨t, ht, hx⟩ := (mem_locP P J _).1 (h hx)
  refine (mem_locP P J x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases P.isPrime.mem_or_mem hm with h | h
  exacts [ht h, hs h]

theorem locP_AA (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ) (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hP : (l : 𝓞 X.E) ∈ P.asIdeal) (hc : Nat.Coprime (Ideal.absNorm cc) l) :
    localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  haveI := P.isPrime
  refine le_antisymm (localization_le_of_le_localization₂ P ?_) (localization_le_of_le_localization₂ P ?_)
  · obtain ⟨z, hz, hden⟩ := exists_den D (P.asIdeal.comap j) hl h2 hq (by rw [Ideal.mem_comap, map_natCast]; exact hP)
    refine Submodule.span_le.2 ?_
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine (mem_locP P _ _).2 ⟨j z, hz, Submodule.mem_one.2 ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    rw [e, hw]
    ring
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    refine (mem_locP P _ _).2 ⟨(Ideal.absNorm cc : ℕ), natCast_notMem P.isPrime.ne_top hP hc, ?_⟩
    have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
      refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
      simp
    convert Submodule.smul_mem _ y h1 using 1
    simp [Algebra.smul_def, mul_comm]

theorem sq_ne_neg {X : Fields} (hX : X.Ok) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f) (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p)
    (a : X.E) : a ^ 2 ≠ -(p : X.E) := by
  intro ha
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    exact (isIntegral_algebraMap (R := ℤ) (x := (p : ℤ)) |>.neg) |> fun h => by simpa using h
  obtain ⟨b, hba⟩ : ∃ b : 𝓞 X.E, algebraMap (𝓞 X.E) X.E b = a := ⟨⟨a, hint⟩, rfl⟩
  have hb : b ^ 2 = -(p : 𝓞 X.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hba, ha, map_neg, map_natCast]
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  have haP : b ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem 2 (hb ▸ P.asIdeal.neg_mem hpP)
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP ?_
  have := Ideal.pow_mem_pow haP 2
  rwa [hb, neg_mem_iff] at this

theorem notMem_small {X : Fields} (hX : X.Ok) (D : D7) (s : Seam D X) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime)
    (hn : π * X.conjO π = (p : 𝓞 X.E)) (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f)
    (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p) : p ∉ D.host.small := by
  intro hs
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  exact (UpperTheory.Ram.not_dvd_QS_of_notMem_sq D.host.toHostAx D.host.QS_exact X.E s.iE P p hp hpP
    (GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP)).1
    (Nat.dvd_of_mem_primeFactors hs)

theorem primes_ne (Z : Dat) (D : D7) (s : Seam D Z.X) (hZ : Z.Ok) :
    (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q := by
  have ha : (s.iE.symm (D.host.sqq)) ^ 2 = -(D.host.q : Z.X.E) := by
    rw [← map_pow, D.host.sqq_sq, map_neg, map_natCast]
  have hcc : ∀ x, Z.X.conjO (Z.X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : Z.X.E))
  have hPr := hZ.primes
  refine ⟨fun u => ⟨fun h => ?_, fun h => ?_⟩, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact notMem_small hZ.fields D s _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) h
  · exact sq_ne_neg hZ.fields _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) _ (h ▸ ha)
  · exact notMem_small hZ.fields D s (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) h
  · exact sq_ne_neg hZ.fields (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) _ (h ▸ ha)

theorem locP_AA_and_primes_ne : (∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ), l.Prime → l ∉ D.host.small → l ≠ D.host.q → (l : 𝓞 X.E) ∈ P.asIdeal → Nat.Coprime (Ideal.absNorm cc) l → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) ∧ ∀ (Z : Dat) (D : D7) (s : Seam D Z.X), Z.Ok → (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q :=
  ⟨locP_AA, primes_ne⟩

end GlobalTheory.AAUnitAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem small_prime_lt (eps C8 : ℝ) (he : 0 < eps) (h8 : 1 ≤ C8) : ∃ x0 : ℝ, ∀ (s : Scale) (N q0 : ℝ), s.eps = eps → x0 ≤ s.x →
    0 < N → Real.log N ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → q0 ≤ N ^ C8 → q0 < s.X' := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.scale_poly_comparison eps (2 * C8) (1 / 2) he (by norm_num)
  refine ⟨x0, fun s N q0 hs hx hN hlog hq => ?_⟩
  have h := (hx0 s hs hx).2.2.2.2.2.2
  have hx1 := s.one_lt_alt
  have h1 : 1 ≤ s.x ^ (2 * C8) := Real.one_le_rpow hx1.le (by linarith)
  have hX : 1 < s.X' := Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : s.X' ^ (1 / 2 : ℝ) < s.X' := by
    calc s.X' ^ (1 / 2 : ℝ) < s.X' ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
      _ = s.X' := Real.rpow_one _
  have h3 : N ^ C8 ≤ Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ C8)
    linarith
  have h4 : Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
      Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ (2 * C8) :=
    le_mul_of_one_le_right (Real.exp_pos _).le h1
  linarith

theorem X'_le_b (s : Scale) : s.X' ≤ s.b := by
  have := s.eps_pos
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith))

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dite_eq_left hf]
  simpa using h

theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))


open Classical in
def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  intro R H M p _ h
  obtain ⟨π, hN, hB, hA⟩ := h
  have h' : GlobalTheory.Mem.An.NormOne H.d M p := ⟨π.1, π.2, hN, hB, hA⟩
  exact ⟨(GlobalTheory.Mem.An.normOne_iff_host R H M p).1 h',
    (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d M p (by have := H.hyp.2.2.2.1; omega) h').1⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.VolumePos

section Index

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem relIndex_ne_zero {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (hM : M.FG) :
    M₀.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM
  haveI : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  haveI : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.1 ‹Module.Finite ℤ M›
  have : Finite (M.toAddSubgroup ⧸ M₀.toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨n, hn, hx⟩ := h₀ x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rw [Nat.cast_smul_eq_nsmul] at hx
    exact hx
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_localized_ne_zero (P : HeightOneSpectrum (𝓞 E)) {M₀ M : Submodule (𝓞 E) W} (h₀ : Full M₀) (h : Full M) (hM : M.FG) :
    (localization₂ P.asIdeal M₀).toAddSubgroup.relIndex (localization₂ P.asIdeal M).toAddSubgroup ≠ 0 := by
  intro h0
  have hle : (localization₂ P.asIdeal M).toAddSubgroup ≤ M.toAddSubgroup ⊔ (localization₂ P.asIdeal M₀).toAddSubgroup := by
    intro x hx
    obtain ⟨t, h1, h2⟩ := (h.inf h₀).approx {P} x
    have h3 := h1 P (Finset.mem_singleton_self P)
    have ht : t ∈ M := mem_of_locP fun Q => by
      by_cases hQ : Q = P
      · subst hQ
        have := (localization₂ Q.asIdeal M).add_mem (localization_mono Q inf_le_left h3) hx
        rwa [sub_add_cancel] at this
      · exact localization_mono Q inf_le_left (h2 Q (by simpa using hQ))
    have : x = t - (t - x) := by abel
    rw [this]
    exact sub_mem (AddSubgroup.mem_sup_left ht) (AddSubgroup.mem_sup_right (localization_mono P inf_le_right h3))
  have h4 := AddSubgroup.relIndex_eq_zero_of_le_right hle h0
  rw [AddSubgroup.relIndex_sup_right] at h4
  exact relIndex_ne_zero h₀ hM
    (AddSubgroup.relIndex_eq_zero_of_le_left (fun x hx => mem_localization_of_mem P hx) h4)

end Index

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem homO_fg {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : N.FG) (hN' : N'.FG)
    (hs : Submodule.span E (N : Set (Sp E a)) = ⊤) : (homO N N').FG := by
  obtain ⟨T, rfl⟩ := hN
  let φ : HomE E a b →ₗ[𝓞 E] (T → Sp E b) :=
    { toFun := fun x y => x y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [Submodule.span_span_of_tower] at hs
    exact LinearMap.ext_on hs fun v hv => congrFun hxy ⟨v, hv⟩
  refine Submodule.fg_of_fg_map_injective φ hφ ?_
  refine Submodule.FG.of_le (Submodule.fg_pi (p := fun _ : T => N') fun _ => hN') ?_
  rintro _ ⟨x, hx, rfl⟩ y _
  exact hx _ (Submodule.subset_span y.2)

theorem perO_fg {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hA : AA.FG)
    (hH : (homO N N').FG) : (perO AA N N').FG := by
  let B : E →ₗ[𝓞 E] HomE E a b →ₗ[𝓞 E] HomE E a b :=
    LinearMap.mk₂ (𝓞 E) (fun r x => r • x) (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
      (fun _ _ _ => smul_add _ _ _) (fun _ _ _ => smul_comm _ _ _)
  refine Submodule.FG.of_le (Submodule.FG.map₂ B hA hH) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, hr, x, hx, rfl⟩
  exact Submodule.apply_mem_map₂ B hr hx

theorem volC_pos : Formalism.L2.Ker.VolCPos := by
  intro E _ _ _ a b AA S N N' hN hN' hs hs' hA hA0
  have la : Submodule.IsLattice E (Formalism.L2.Col.stdLat E a) := Formalism.L2.Col.stdLat_lattice
  have lb : Submodule.IsLattice E (Formalism.L2.Col.stdLat E b) := Formalism.L2.Col.stdLat_lattice
  have hspan (n : ℕ) : Submodule.span E (Formalism.L2.Col.stdLat E n : Set (Sp E n)) = ⊤ := by
    rw [Formalism.L2.Col.stdLat_eq_span, Submodule.span_span_of_tower]
    have hbasis : (fun i : Fin n => (Pi.single i (1 : E) : Sp E n)) =
        ⇑(Pi.basisFun E (Fin n)) :=
      funext fun i => (Pi.basisFun_apply E (Fin n) i).symm
    rw [hbasis, (Pi.basisFun E (Fin n)).span_eq]
  have full₀ : Submodule.IsFullLattice E (Formalism.L2.Col.stdLat E b) :=
    { toIsLattice := lb, span_eq_top := hspan b }
  have full₁ : Submodule.IsFullLattice E N' :=
    { toIsLattice := Submodule.IsLattice.of_fg E hN', span_eq_top := hs' }
  have f₀ := PeriodComp.full AA (Formalism.L2.Col.stdLat E a)
    (Formalism.L2.Col.stdLat E b) la.fg full₀ hA0
  have f₁ := PeriodComp.full AA N N' hN full₁ hA0
  have g₀ := perO_fg hA (homO_fg la.fg lb.fg (hspan a))
  have g₁ := perO_fg hA (homO_fg hN hN' hs)
  refine Finset.prod_pos fun P _ => div_pos ?_ ?_
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₀ f₁ g₁))
  · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_localized_ne_zero P f₁ f₀ g₀))

end GlobalTheory.ThetaMove.VolumePos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.Moved

theorem sd_stdL (D : D7) (N : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D N) := by
  letI := D.host.cmStar
  have hr : ∀ x : D.host.E, x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → D.host.E, x ∈ StandardLatticesGL3.stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [Formalism.BasicNotions.stdH, Pi.single_apply, apply_ite] using this

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [formV, map_sum, mul_comm]

theorem inter_mem_Th {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V} {α : V → ℂ}
    (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hf : relIdx A₁ A₂ ≠ 0)
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ Th H α A₁) : inter H α A₁ A₂ F ∈ Th H α A₂ := by
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hf
  refine ⟨?_, GlobalTheory.ThetaInter.inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF.2⟩
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hU : ∀ x z, AnalyticAt ℂ (opU H x F) z := fun x z => by
    have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
    have h2 : AnalyticAt ℂ (fun z => F (z + x)) z :=
      AnalyticAt.comp (f := fun z => z + x) (hF.1 _ (Set.mem_univ _)) (analyticAt_id.add analyticAt_const)
    exact h2.mul ((analyticAt_const.mul h).sub analyticAt_const).cexp
  rw [GlobalTheory.ThetaInter.inter_eq]
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul (hU _ z))

theorem iop_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (A₁ A₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) A₁ A₂ G =
      inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) A₁ A₂ G := rfl

theorem iop_mul (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (A B : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (z : TaylorLogMetric.VC D N N') : TaylorLogMetric.Iop D T A B (fun w => c * G w) z = c * TaylorLogMetric.Iop D T A B G z := by
  unfold TaylorLogMetric.Iop
  rw [mul_left_comm, mul_finsum _ c]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [TaylorLogMetric.U]; ring

variable {D : D7} {χ : TaylorLogMetric.IdE D → ℂ} {n : ℕ} {L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}

theorem chi_detId_mul (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    χ (TaylorLogMetric.detId D L L'') = χ (TaylorLogMetric.detId D L L') * χ (TaylorLogMetric.detId D L' L'') := by
  rw [(GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').2]
  exact hχ.1 _ _ (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').1 (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L' L'' L'' h' h'' h'').1

theorem chi_detId_ne_zero (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : χ (TaylorLogMetric.detId D L L') ≠ 0 := by
  obtain ⟨⟨𝔟, -, hb⟩, h2⟩ := GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L L h h h
  have h1 : TaylorLogMetric.detId D L L = 1 := by
    rw [← mul_one (TaylorLogMetric.detId D L L), ← hb, ← mul_assoc, ← h2]
  have h3 := chi_detId_mul hχ h h' h
  have h4 : χ 1 = 1 := by simpa [Submodule.one_eq_span] using hχ.2 1
  rw [h1, h4] at h3
  exact left_ne_zero_of_mul_eq_one h3.symm

theorem thMoved_mem_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  intro D cc δ B χ a b hχ hE hL h0 ha hb
  have sa := sd_stdL D a
  have sb := sd_stdL D b
  have hne : ∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 := fun L L' h h' =>
    mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ sa h)) (zpow_ne_zero _ (chi_detId_ne_zero hχ sb h'))
  have step : ∀ L₁ L₁' L₂ L₂', StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L₁' → StandardLatticesGL3.SD D L₂ → StandardLatticesGL3.SD D L₂' → ∀ F,
      F ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁') →
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') F ∈
        Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₂ L₂') := by
    intro L₁ L₁' L₂ L₂' h₁ h₁' h₂ h₂' F hF
    have A₁ : TaylorLogMetric.admitted D a b L₁ L₁' := ⟨ha, hb, h₁, h₁'⟩
    have A₂ : TaylorLogMetric.admitted D a b L₂ L₂' := ⟨ha, hb, h₂, h₂'⟩
    rw [iop_eq]
    exact inter_mem_Th (isHerm_formV _ _ _ _) (hL.2 a b _ _ _ _ A₁ A₂).1 (hL.1 a b _ _ A₁).2 (hL.1 a b _ _ A₂).1
      (hL.1 a b _ _ A₂).2 hF
  refine ⟨fun L L' h h' => ⟨hne L L' h h', step _ _ _ _ h sb h h' _ (step _ _ _ _ sa sb h sb _ h0)⟩, ?_, ?_⟩
  · intro L L' L'' h h' h''
    funext z
    have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
    have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sb h' h'', mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h h'') e
  · intro L L₁ L' h h₁ h'
    funext z
    have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
    have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sa h h₁, mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h₁ h') e

end GlobalTheory.ThetaMove.Moved
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMovesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  first | exact @GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | exact GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | (intros; apply GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcoveStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWHlatIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem mem_locW_hlat_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ emb Pl pw hv n S lam h hS w x
  unfold locW
  simp only [vl_mem_span_intW_iff Pl pw hv]
  unfold Formalism.HermitianLatticesTheory.localization₂
  constructor
  · rintro ⟨s, hs, hsx⟩ c
    exact ⟨s, hs, hsx c⟩
  · classical
    intro hx
    choose t ht htx using hx
    have : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b)) := hS.fin_orb
    let _ : Fintype S.Cl := Fintype.ofFinite _
    refine ⟨∏ c, t c, Submonoid.prod_mem _ fun c _ => ht c, fun c => ?_⟩
    have hc := (delAtr emb lam (S.Lsh c.1 (S.rep c))).smul_mem (∏ d ∈ Finset.univ.erase c, t d) (htx c)
    rw [← mul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at hc
    exact hc

end GlobalTheory.Mem.Col2
end
end
