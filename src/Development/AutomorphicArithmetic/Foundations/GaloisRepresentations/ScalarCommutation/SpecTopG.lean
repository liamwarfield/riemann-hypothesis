module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecData

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPlace
@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Spc.EntrywiseClass

private theorem exists_root (tr nm : ℤ) (h : tr ^ 2 - 4 * nm < 0) (b : ℕ) :
    ∃ q : ℕ, q.Prime ∧ b < q ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm := by
  have hnm : 0 < nm := by nlinarith [sq_nonneg tr]
  set c : ℕ := (b + tr.natAbs + 1).factorial with hc
  have hcge : b + tr.natAbs + 1 ≤ c := Nat.self_le_factorial _
  have hcZ : (tr.natAbs : ℤ) + 1 ≤ (c : ℤ) := by omega
  have htr : tr ≤ tr.natAbs := by omega
  set g : ℤ := nm * (c : ℤ) ^ 2 - tr * c + 1 with hg
  have hcpos : (0 : ℤ) < c := by omega
  have hg1 : 1 < g := by
    have h1 : (c : ℤ) ≤ nm * c := by nlinarith
    have h2 : 0 < nm * c - tr := by omega
    have : 0 < (c : ℤ) * (nm * c - tr) := mul_pos hcpos h2
    rw [hg]; nlinarith
  have hne : g.natAbs ≠ 1 := by omega
  refine ⟨g.natAbs.minFac, Nat.minFac_prime hne, ?_, nm * c, ?_⟩
  · by_contra hle
    have hq := Nat.minFac_prime hne
    have hqc : g.natAbs.minFac ∣ c := (hq.dvd_factorial).2 (by omega)
    have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have hqc' : (g.natAbs.minFac : ℤ) ∣ (c : ℤ) := by exact_mod_cast hqc
    have h1 : (g.natAbs.minFac : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = g - c * (nm * c - tr) := by rw [hg]; ring
      rw [e]; exact dvd_sub hqg (Dvd.dvd.mul_right hqc' _)
    have := Int.eq_one_of_dvd_one (by omega) h1
    have h2 := hq.one_lt
    omega
  · have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have e : (nm * c) ^ 2 - tr * (nm * c) + nm = nm * g := by rw [hg]; ring
    rw [e]; exact Dvd.dvd.mul_left hqg _

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem not_both (u : Plc E) {a b : ℕ} (h : a.Coprime b) (ha : (a : 𝓞 E) ∈ u.asIdeal) (hb : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : 𝓞 E) = (s : 𝓞 E) * (a : 𝓞 E) + (t : 𝓞 E) * (b : 𝓞 E) := by
    exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hst).symm
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [e]
  exact u.asIdeal.add_mem (u.asIdeal.mul_mem_left _ ha) (u.asIdeal.mul_mem_left _ hb)

private theorem exists_place (q : ℕ) (hq : q.Prime) : ∃ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.ExistsPlace.exists_place q hq

private theorem finite_above (q : ℕ) (hq : q.Prime) : {w : Plc E | (q : 𝓞 E) ∈ w.asIdeal}.Finite := by
  have hq0 : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {(q : 𝓞 E)}) (by simpa using hq0)).subset fun w hw => ?_
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hw)

private theorem cj_cj (A : Arith E) (u : Plc E) : CertificateRingHomMap.cj (CertificateRingHomMap.cj u) = u := by
  apply HeightOneSpectrum.ext
  ext y
  rw [UpperTheory.Gal.G1.pCjMem E A, UpperTheory.Gal.G1.pCjMem E A, A.bar_bar]

private theorem eq_or_cj (A : Arith E) (w u : Plc E)
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = CertificateRingHomMap.cj w := by
  have hsub : (u.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ ((CertificateRingHomMap.cj w).asIdeal : Set (𝓞 E)) := by
    intro y hy
    have hy' : y ∈ u.asIdeal := hy
    have ht : IsCMField.complexConj E ((y * A.bar y : 𝓞 E) : E) = ((y * A.bar y : 𝓞 E) : E) := by
      rw [← A.bar_eq, map_mul, A.bar_bar, mul_comm]
    have hmem : ((y * A.bar y : 𝓞 E) : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E _).1 ht
    have hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) ).1
        (RingOfIntegers.isIntegral_coe (y * A.bar y))
    let z : 𝓞 (maximalRealSubfield E) := ⟨⟨_, hmem⟩, hint⟩
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) z = y * A.bar y := RingOfIntegers.ext rfl
    have h1 : z ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz]
      exact u.asIdeal.mul_mem_right _ hy'
    rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz] at h1
    rcases w.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ((UpperTheory.Gal.G1.pCjMem E A w y).2 h2)
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (CertificateRingHomMap.cj w).isPrime.ne_top h1))

end UpperTheory.Gal.Spc.EntrywiseClass

theorem UpperTheory.Gal.Spc.auxiliary_prime_holds :
    UpperTheory.Gal.Spc.AuxiliaryInertOddPrime := by
  intro E _ _ _ A n p _ S x U w₀ Up V hG X
  obtain ⟨e, he, hperf⟩ := pPerfCof E A
  obtain ⟨q, hq, hb, r, hr⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_root A.tr A.nm A.disc_neg
    (X.sup id + p + e + (A.tr ^ 2 - 4 * A.nm).natAbs + V.S.sup fun u => Ideal.absNorm u.asIdeal)
  have hX : q ∉ X := fun h => by
    have h1 := Finset.le_sup (f := id) h
    simp only [id] at h1
    omega
  have hqp : q ≠ p := by omega
  have hcop : ∀ a : ℕ, 0 < a → a < q → a.Coprime q := fun a h0 h1 =>
    ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => absurd (Nat.le_of_dvd h0 h) (by omega)).symm
  have hD : ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm := fun h => by
    have h1 : q ∣ (A.tr ^ 2 - 4 * A.nm).natAbs := Int.natCast_dvd.1 h
    have h2 : 0 < (A.tr ^ 2 - 4 * A.nm).natAbs := by have := A.disc_neg; omega
    have := Nat.le_of_dvd h2 h1
    omega
  have hs : A.SplitK q := ⟨hD, r, hr⟩
  have hgood : A.Good q := ⟨hs, hperf q (hcop e he (by omega))⟩
  have hoff : ∀ u ∈ V.S, (q : 𝓞 E) ∉ u.asIdeal := fun u hu h => by
    have h1 : Ideal.absNorm u.asIdeal ≤ V.S.sup fun u => Ideal.absNorm u.asIdeal :=
      Finset.le_sup (f := fun u : Plc E => Ideal.absNorm u.asIdeal) hu
    have h2 : 0 < Ideal.absNorm u.asIdeal := Nat.pos_of_ne_zero fun h0 => u.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact UpperTheory.Gal.Spc.EntrywiseClass.not_both u (hcop _ h2 (by omega)).symm h (Ideal.absNorm_mem u.asIdeal)
  obtain ⟨w₁, hw₁⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_place (E := E) q hq
  have SD := fun (w : Plc E) (hw : (q : 𝓞 E) ∈ w.asIdeal) => Pl.sides_holds E A x hG q hq hs w hw
  obtain ⟨ρ, -, hρ⟩ := (SD w₁ hw₁).2.2.2.2.2.1
  have hiff := (SD w₁ hw₁).2.2.2.2.2.2 ρ hρ
  have hpo : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → (p : 𝓞 E) ∉ u.asIdeal := fun u hu hp =>
    UpperTheory.Gal.Spc.EntrywiseClass.not_both u ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp) hu hp
  have hT : {w : UpperTheory.Gal.Spc.Spl E p | (q : 𝓞 E) ∈ w.1.asIdeal ∧ A.ω - (ρ : 𝓞 E) ∈ w.1.asIdeal}.Finite :=
    ((UpperTheory.Gal.Spc.EntrywiseClass.finite_above (E := E) q hq).preimage (f := fun w : UpperTheory.Gal.Spc.Spl E p => w.1)
      (fun _ _ _ _ h => Subtype.ext h)).subset fun w hw => hw.1
  have hmk : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → A.ω - (ρ : 𝓞 E) ∈ u.asIdeal →
      ∃ w ∈ hT.toFinset, w.1 = u := fun u h1 h2 =>
    ⟨⟨u, (SD u h1).2.1, hpo u h1⟩, hT.mem_toFinset.2 ⟨h1, h2⟩, rfl⟩
  refine ⟨q, hT.toFinset, hX, hq, hqp, hgood, hoff, ⟨fun w hw => (hT.mem_toFinset.1 hw).1, fun u hu => ?_, fun w hw w' hw' hne heq => ?_⟩, ?_⟩
  · rcases (SD w₁ hw₁).2.2.1 u hu with h | h
    · obtain ⟨h1, h2⟩ := (hiff u).1 h
      obtain ⟨w, hw, e⟩ := hmk u h1 h2
      exact ⟨w, hw, Or.inl e⟩
    · obtain ⟨h1, h2⟩ := (hiff _).1 h
      obtain ⟨w, hw, e⟩ := hmk _ h1 h2
      exact ⟨w, hw, Or.inr (by rw [e]; exact UpperTheory.Gal.Spc.EntrywiseClass.cj_cj A u)⟩
  · have m := hT.mem_toFinset.1 hw
    have m' := hT.mem_toFinset.1 hw'
    rcases UpperTheory.Gal.Spc.EntrywiseClass.eq_or_cj A w.1 w'.1 heq with h | h
    · exact hne (Subtype.ext h.symm)
    · refine (SD w.1 m.1).1 (((SD w.1 m.1).2.2.2.2.2.2 ρ m.2 _).2 ?_)
      rw [← h]
      exact m'
  · obtain ⟨w, hw, -⟩ := hmk w₁ hw₁ hρ
    exact ⟨w, hw⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.RelIndexNeZeroOfOpen
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacEx
open NumberField IsDedekindDomain

theorem UpperTheory.Gal.Spc.facEx :
    UpperTheory.Gal.Spc.FacEx := by
  intro E _ _ _ A n p _ S F w
  refine ⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩
  · have h := (F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2
    exact h
  · rw [F.j_tr]
    rfl
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat sim)
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.W2.Seed (Arith Setup Cong1 apart_of_not_mem pKNOpen pKNIdx pKNIff pLatCoord pRepLaws)
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.Int.Geo.Pl (Frame)
open GlobalTheory.LFun (KGL)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

private theorem th_eq (F : Frame S) (g : GUf E n) : F.th g = CertificateRingHomMap.th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem continuous_th : Continuous (CertificateRingHomMap.th : GUf E n → GUf E n) := by
  refine continuous_induced_rng.2 ?_
  exact ((GlobalTheory.SplitPts.continuous_invT _).comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

private theorem relIndex_ne_zero_of_open {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

private theorem isCompact_comap_th (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) :
    IsCompact ((K.comap F.th : Subgroup (GUf E n)) : Set (GUf E n)) := by
  have hImage : (K.comap F.th : Set (GUf E n)) = CertificateRingHomMap.th '' (K : Set (GUf E n)) := by
    ext g
    constructor
    · intro h
      exact ⟨F.th g, h, by rw [th_eq F, CertificateRingHomMap.th_th]⟩
    · rintro ⟨y, hy, rfl⟩
      change F.th (CertificateRingHomMap.th y) ∈ K
      rwa [th_eq F, CertificateRingHomMap.th_th]
  rw [hImage]
  exact hK.image continuous_th

private theorem relIdx (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) (N : ℕ) (hN : 0 < N) :
    (S.L.KN N).relIndex ((K.comap F.th).map F.j) ≠ 0 := by
  rw [← Subgroup.relIndex_comap]
  have hO := pKNOpen (pKNIff (pLatCoord pRepLaws)) E A n p S F.tr N hN
  rw [← F.j_tr] at hO
  exact relIndex_ne_zero_of_open (isCompact_comap_th F hK) hO

private theorem cong_at (F : Frame S) (k : GUf E n) (N : ℕ) (hN : 0 < N) (hk : S.L.CongOne N (F.j k)) (w : Plc E)
    (hp : (p : 𝓞 E) ∉ w.asIdeal) : Cong1 N w (F.a w * comp w k * (F.a w)⁻¹) := by
  have hk' : S.L.CongOne N (F.tr.j k) := by simpa only [← F.j_tr] using hk
  have h := ((pKNIff (pLatCoord pRepLaws)) E A n p S F.tr k).2 N hN
  simpa only [map_mul, map_inv, ← F.a_tr w, CertificateRingHomMap.comp, MonoidHom.comp_apply]
    using h.mp hk' w hp

private theorem val_nat_lt_one {w : Plc E} {r N : ℕ} (hr : (r : 𝓞 E) ∈ w.asIdeal) (hN : r ∣ N) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : (N : 𝓞 E) ∈ w.asIdeal := by
    obtain ⟨c, rfl⟩ := hN
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hr
  have h2 := (w.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E)).2 h1
  have e : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E (N : 𝓞 E)) := by
    rw [map_natCast, map_natCast]
  rw [e]
  exact (w.valuedAdicCompletion_eq_valuation' _).trans_lt h2

private theorem mul_lt_left {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) < 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' (hA _ _) le_rfl) (by simpa using hB l j)

private theorem mul_lt_right {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) < 1) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' le_rfl (hB _ _)) (by simpa using hA i l)

private theorem sub_lt_of_conj {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w (n := n))
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1) (i k : Fin n) : Valued.v ((g.val - 1) i k) < 1 := by
  have hK := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n a).2).1 ha
  have e : g.val - 1 = (a⁻¹).val * ((a * g * a⁻¹).val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by simp
    have h2 : (a⁻¹).val * (a * g * a⁻¹).val * a.val = g.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.mul_one, h1]
  rw [e]
  exact mul_lt_right (mul_lt_left hK.2 h) hK.1 i k

private theorem le_one_of_sub_lt {w : Plc E} {g : GLw n w} (h : ∀ i k, Valued.v ((g.val - 1) i k) < 1) (i k : Fin n) :
    Valued.v (g.val i k) ≤ 1 := by
  have e : g.val i k = (g.val - 1) i k + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le (h i k).le ?_)
  by_cases hik : i = k <;> simp [hik, Matrix.one_apply]

private theorem iw_of_cong {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w (n := n))
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1)
    (h' : ∀ i k, Valued.v (((a * g⁻¹ * a⁻¹).val - 1) i k) < 1) : g ∈ Iw n w := by
  have c1 := sub_lt_of_conj a g ha h
  have c2 := sub_lt_of_conj a g⁻¹ ha h'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1).2 ⟨le_one_of_sub_lt c1, le_one_of_sub_lt c2, fun i j hij => ?_⟩
  have e : g.val i j = (g.val - 1) i j := by
    simp [Matrix.one_apply, (ne_of_lt hij).symm]
  rw [e]
  exact c1 i j

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.tyEx :
    UpperTheory.Gal.Spc.TyEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hOff r W hAux N hrN hSt
  have hS0 : w₀ ∈ V.S := V.shape.mem
  have hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal := ⟨V.split, hOff.1 w₀ hS0⟩
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  choose L hL using fun w : Spl E p => facEx E A n p S F w
  have hcomp : ∀ (u : Plc E) (g : GUf E n), comp u (F.th g) = invT n _ (comp u g) := fun u g => by
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.comp_th]
  let K : Subgroup S.G.GAf := ((lev V.S V.Kw).comap F.th).map F.j ⊓ ⨅ w ∈ W, (Iw n w.1).comap (L w).pr
  have hK : ∀ k, k ∈ K ↔ (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 := by
    intro k
    simp only [K, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_iInf, Subgroup.mem_comap]
    exact and_congr_left' (exists_congr fun _ => and_comm)
  obtain ⟨-, hap, -, -, hcc, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w₀ hw.1
  have hfact : (L ⟨w₀, hw⟩).Fact K (V.J.comap (invT n _)) := by
    refine ⟨fun y hy => (hK _).2 ⟨⟨CertificateRingHomMap.loc hw.1 y, ((hL ⟨w₀, hw⟩).2 y).symm, ?_⟩, fun w hW => ?_⟩, fun g hg => ?_⟩
    · refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun u hu => ?_, fun u hu hu' => ?_⟩
      · rw [F.th_sim, UpperTheory.Gal.CertificateRingHomMap.sim_loc, inv_one]
        exact one_mem _
      · rw [hcomp]
        by_cases h1 : u = w₀
        · subst h1
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc, V.Kw0]
          exact hy
        · have h2 : u ≠ cj w₀ := fun h => (V.shape.up w₀ hS0 V.split).2 (h ▸ hu)
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
          exact one_mem _
      · have h1 : u ≠ w₀ := fun h => hu (h ▸ hS0)
        have h2 : u ≠ cj w₀ := fun h => hu' (by rw [h, hcc]; exact hS0)
        rw [hcomp, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
        exact one_mem _
    · have e : (L ⟨w₀, hw⟩).loc y = F.j (CertificateRingHomMap.loc hw.1 y) := (hL ⟨w₀, hw⟩).2 y
      rw [e, (hL w).1, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 (apart_of_not_mem (hAux.off w₀ hS0) (hAux.half.above w hW))]
      exact one_mem _
    · obtain ⟨⟨k', rfl, hk'⟩, -⟩ := (hK g).1 hg
      have e : (L ⟨w₀, hw⟩).pr (F.j k') = comp w₀ k' := (hL ⟨w₀, hw⟩).1 k'
      have h := (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk').2.1 w₀ hS0
      rw [hcomp, V.Kw0] at h
      rw [e]
      exact h
  have hle : S.L.KN N.1 ≤ K := by
    intro k hk
    obtain ⟨k', rfl, hk', -⟩ := hSt k hk
    refine (hK _).2 ⟨⟨k', rfl, hk'⟩, fun w hW => ?_⟩
    have hr := hAux.half.above w hW
    have hv := val_nat_lt_one hr hrN
    rw [(hL w).1]
    refine iw_of_cong (F.a w.1) _ (F.a_int w.1 r hAux.prime hAux.good hr) (fun i k => ?_) (fun i k => ?_)
    · exact (cong_at F k' N.1 hN hk.1 w.1 w.2.2 i k).trans_lt hv
    · have h := cong_at F k'⁻¹ N.1 hN (by rw [map_inv]; exact hk.2) w.1 w.2.2 i k
      rw [map_inv] at h
      exact h.trans_lt hv
  refine ⟨L, hw,
    { L := L ⟨w₀, hw⟩
      K := K
      K₀ := S.L.KN N.1
      J := V.J.comap (invT n _)
      ψ := V.χ.comp ((invT n _).subgroupComap V.J)
      fact := hfact
      le := hle
      ker := fun k hk h => ?_
      idx := fun h0 => relIdx F V.cpt N.1 hN (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
      cms := (pKNIdx (pKNOpen (pKNIff (pLatCoord pRepLaws))) E A n p S F.tr N.1 hN).1 },
    ⟨hL, rfl, rfl, hK, fun y y' h => ?_, fun y y' h => ?_⟩⟩
  · obtain ⟨k', rfl, -, hJ, hχ⟩ := hSt k hk
    rw [← hχ]
    refine congrArg V.χ (Subtype.ext ?_)
    show invT n _ ((L ⟨w₀, hw⟩).pr (F.j k')) = comp w₀ (F.th k')
    rw [hcomp]
    exact congrArg _ ((hL ⟨w₀, hw⟩).1 k')
  · have e : y' = invT n _ y := Units.ext h
    rw [e]
    rfl
  · exact congrArg V.χ (Subtype.ext (Units.ext h.symm))
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CnjApply
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private def cnj {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k where
  toFun x := (a⁻¹).val * x * a.val
  map_one' := by simp
  map_mul' x y := by
    have h : a.val * (a⁻¹).val = 1 := Units.mul_inv a
    calc (a⁻¹).val * (x * y) * a.val = (a⁻¹).val * x * 1 * y * a.val := by simp [Matrix.mul_assoc]
      _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private def rd (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) : AfP p ⊗[ℚ] E →+* w.adicCompletion E :=
  RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, fun x hx => by
    have := (T.Φ_ker x).1 hx w hp
    exact this⟩

private theorem rd_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : Af E) : rd T w hp (T.Φ x) = pLoc E w x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private def aw (T : Tr S) (w : Plc E) : GL (Fin n) (w.adicCompletion E) := GeneralLinearGroup.map (pLoc E w) T.a

private theorem cnj_apply {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    cnj a x = (a⁻¹).val * x * a.val := rfl

private theorem alg_mat (n : ℕ) (w : Plc E) (r : E) :
    (algebraMap E (Matrix (Fin n) (Fin n) E) r).map (algebraMap E (w.adicCompletion E)) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

private theorem cnj_alg {w : Plc E} (a : GL (Fin n) (w.adicCompletion E)) (r : E) :
    cnj a (algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  rw [cnj_apply, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, smul_mul_assoc, Matrix.mul_one,
    Units.inv_mul]

private def iotaAt (S : Setup A n p) (w : Plc E) (a : GL (Fin n) (w.adicCompletion E)) :
    S.G.C →ₐ[S.G.F] Matrix (Fin S.G.n) (Fin S.G.n) (w.adicCompletion E) :=
  { (cnj a).comp (RingHom.mapMatrix (algebraMap E (w.adicCompletion E))) with
    commutes' := fun r => (congrArg (cnj a) (alg_mat n w r)).trans (cnj_alg a r) }

private def kap0 (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  ((cnj (aw T w)).comp (RingHom.mapMatrix (rd T w hp))).comp (T.μ : _ →+* _)

private theorem rd_one (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : E) :
    rd T w hp ((1 : AfP p) ⊗ₜ x) = algebraMap E (w.adicCompletion E) x := by
  rw [← T.Φ_E x, rd_Φ]
  rfl

private theorem map_mu (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (y : Matrix (Fin n) (Fin n) E) :
    (T.μ ((1 : AfP p) ⊗ₜ[ℚ] y)).map (rd T w hp) = y.map (algebraMap E (w.adicCompletion E)) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, T.mu, rd_one, Matrix.map_apply]

private theorem map_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (M : Matrix (Fin n) (Fin n) (Af E)) :
    (M.map T.Φ).map (rd T w hp) = M.map (pLoc E w) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, rd_Φ]

private theorem at_eq (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (g : GUf E n) :
    cnj (aw T w) ((T.μ (S.mx (T.j g))).map (rd T w hp)) = (comp w g).val := by
  have h2 : aw T w * comp w g * (aw T w)⁻¹ = GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val = (T.a * mat g * T.a⁻¹).val.map (pLoc E w) := rfl
  rw [T.j_mx g, map_Φ, ← h1, ← h2, cnj_apply]
  simp [Matrix.mul_assoc]

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.plTr :
    UpperTheory.Gal.Spc.PlTr := by
  intro E _ _ _ A n p _ S T w hp
  refine ⟨⟨kap0 T w hp, iotaAt S w (aw T w), fun y => ?_⟩, fun g => at_eq T w hp g⟩
  exact congrArg (cnj (aw T w)) (map_mu T w hp y)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ValOfNotMem
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp mat sim AfQ)
open UpperTheory.Gal.W2.Seed
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.Spc

private theorem mat_comm {K : Type} [Field K] {n : ℕ} {A B C : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hB : A * B = B * A) (hC : A * C = C * A) : B * C = C * B := by
  have hsep : (Matrix.toLin' A).charpoly.Separable := by
    have := LinearMap.charpoly_toMatrix (Matrix.toLin' A) (Pi.basisFun K (Fin n))
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at this
    rwa [← this]
  have h := GroundTheory.Automorphic.commute_of_commute_of_separable_charpoly (f := Matrix.toLin' A) (g := Matrix.toLin' B)
    (g' := Matrix.toLin' C) hsep
    (by show _ * _ = _ * _
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hB])
    (by show _ * _ = _ * _
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hC])
  have h2 : Matrix.toLin' (B * C) = Matrix.toLin' (C * B) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]; exact h
  exact Matrix.toLin'.injective h2

private theorem tensor_comm {R Q C : Type} [CommRing R] [Algebra ℚ R] [CommRing Q] [Algebra ℚ Q] [Ring C] [Algebra ℚ C]
    (ev : R →ₐ[ℚ] Q) (r : R) (s : Q →ₗ[ℚ] R) (hs1 : ∀ x, ev (s x) = x) (hs2 : ∀ a, s (ev a) = r * a) (hr : ev r = 1)
    (M : R ⊗[ℚ] C)
    (H : ∀ x y : R ⊗[ℚ] C, (r ⊗ₜ[ℚ] (1 : C)) * (x * M - M * x) = 0 → (r ⊗ₜ[ℚ] (1 : C)) * (y * M - M * y) = 0 →
      (r ⊗ₜ[ℚ] (1 : C)) * (x * y - y * x) = 0)
    (x y : Q ⊗[ℚ] C) (hx : Commute x (Algebra.TensorProduct.map ev (AlgHom.id ℚ C) M))
    (hy : Commute y (Algebra.TensorProduct.map ev (AlgHom.id ℚ C) M)) : Commute x y := by
  set EV := Algebra.TensorProduct.map ev (AlgHom.id ℚ C) with hEV
  let σ : Q ⊗[ℚ] C →ₗ[ℚ] R ⊗[ℚ] C := LinearMap.rTensor C s
  have h1 : ∀ z, EV (σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [σ, hEV, hs1]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
  have h2 : ∀ z, σ (EV z) = (r ⊗ₜ[ℚ] (1 : C)) * z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [σ, hEV, hs2]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, mul_add]
  have h3 : EV (r ⊗ₜ[ℚ] (1 : C)) = 1 := by simp [hEV, hr, Algebra.TensorProduct.one_def]
  have key : ∀ z, Commute z (EV M) → (r ⊗ₜ[ℚ] (1 : C)) * (σ z * M - M * σ z) = 0 := by
    intro z hz
    rw [← h2, map_sub, map_mul, map_mul, h1, sub_eq_zero.2 hz.eq, map_zero]
  have := H _ _ (key x hx) (key y hy)
  have h4 := congrArg EV this
  rw [map_mul, h3, one_mul, map_sub, map_mul, map_mul, h1, h1, map_zero] at h4
  exact sub_eq_zero.1 h4

private theorem afp_ext {p : ℕ} {a b : AfP p} (h : ∀ v : AwayP p, AfP.eval v a = AfP.eval v b) : a = b :=
  RestrictedProduct.ext (fun v : AwayP p => v.1.adicCompletion ℚ) (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) h

private def placeZ (q : ℕ) (hq : q.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(q : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2 (Nat.prime_iff_prime_int.1 hq)
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hq.ne_zero

private def placeAway {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) : AwayP p :=
  ⟨placeZ q hq, fun h => by
    have h1 : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      rw [← h]; exact Ideal.subset_span rfl
    rw [Ideal.mem_span_singleton] at h1
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (by exact_mod_cast h1)).symm⟩

private theorem val_of_not_mem {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (z : R) (h : z ∉ v.asIdeal) (f : ℚ →+* v.adicCompletion ℚ) :
    Valued.v (f (algebraMap R ℚ z)) = 1 := by
  obtain rfl : f = algebraMap ℚ (v.adicCompletion ℚ) := RingHom.ext_rat _ _
  have h1 := v.valuation_le_one (K := ℚ) z
  have h2 : ¬ v.valuation ℚ (algebraMap R ℚ z) < 1 := fun h' => h ((v.valuation_lt_one_iff_mem z).1 h')
  have h3 : v.valuation ℚ (algebraMap R ℚ z) = 1 := le_antisymm h1 (not_lt.1 h2)
  rw [← h3]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

private theorem val_of_mem {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (z : R) (h : z ∈ v.asIdeal) (f : ℚ →+* v.adicCompletion ℚ) :
    Valued.v (f (algebraMap R ℚ z)) < 1 := by
  obtain rfl : f = algebraMap ℚ (v.adicCompletion ℚ) := RingHom.ext_rat _ _
  have h3 := (v.valuation_lt_one_iff_mem (K := ℚ) z).2 h
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R ℚ z)
  exact (this.trans_lt h3)

private theorem exists_place {p q : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    ∃ v : Plc ℚ, (q : 𝓞 ℚ) ∈ v.asIdeal ∧ (p : 𝓞 ℚ) ∉ v.asIdeal := by
  have hq0 : (q : 𝓞 ℚ) ≠ 0 := by
    intro h
    have := congrArg Rat.ringOfIntegersEquiv h
    rw [map_natCast, map_zero] at this
    exact hq.ne_zero (by exact_mod_cast this)
  have hne : Ideal.span {(q : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have := h.map Rat.ringOfIntegersEquiv
    rw [map_natCast, Int.ofNat_isUnit, Nat.isUnit_iff] at this
    exact hq.one_lt.ne' this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hqm : (q : 𝓞 ℚ) ∈ m := hle (Ideal.subset_span rfl)
  refine ⟨⟨m, hm.isPrime, fun hb => hq0 (by simpa [hb] using hqm)⟩, hqm, fun hpm => ?_⟩
  have hco : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hqp.symm)
  obtain ⟨a, b, hab⟩ := hco
  have h1 : ((a : 𝓞 ℚ) * (p : 𝓞 ℚ) + (b : 𝓞 ℚ) * (q : 𝓞 ℚ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
  have h2 : (1 : 𝓞 ℚ) ∈ m := h1 ▸ m.add_mem (m.mul_mem_left _ hpm) (m.mul_mem_left _ hqm)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 h2)

private theorem rho_idem {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (T : AdQ p) (e : AfQ)
    (he : ∀ v : Plc ℚ, ((q : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((q : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) :
    AfP.eval (placeAway hq Fact.out hqp) (T.ρ e) = 1 ∧
      ∀ v : AwayP p, v ≠ placeAway hq Fact.out hqp → AfP.eval v (T.ρ e) = 0 := by
  have hp : p.Prime := Fact.out
  have hee : e * e = e := by
    refine FiniteAdeleRing.ext ℚ fun v => ?_
    by_cases h : (q : 𝓞 ℚ) ∈ v.asIdeal
    · show e v * e v = e v
      rw [(he v).1 h, one_mul]
    · show e v * e v = e v
      rw [(he v).2 h, zero_mul]
  have hr : T.ρ e * T.ρ e = T.ρ e := by rw [← map_mul, hee]
  have h01 : ∀ v : AwayP p, AfP.eval v (T.ρ e) = 0 ∨ AfP.eval v (T.ρ e) = 1 := fun v => by
    have : AfP.eval v (T.ρ e) * AfP.eval v (T.ρ e) = AfP.eval v (T.ρ e) := by rw [← map_mul, hr]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 this
  have hrat : ∀ c : ℚ, T.ρ (algebraMap ℚ AfQ c) = algebraMap ℚ (AfP p) c := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) c
  have hev : ∀ (u : Plc ℚ) (c : ℚ), (algebraMap ℚ AfQ c) u = algebraMap ℚ (u.adicCompletion ℚ) c := fun u c =>
    DFunLike.congr_fun (RingHom.ext_rat
      ((RestrictedProduct.evalRingHom (fun v : Plc ℚ => v.adicCompletion ℚ) u).comp (algebraMap ℚ AfQ))
      (algebraMap ℚ (u.adicCompletion ℚ))) c
  have hA : ∀ v : AwayP p, v ≠ placeAway hq hp hqp → AfP.eval v (T.ρ e) = 0 := by
    intro v hv
    refine (h01 v).resolve_right fun h1 => ?_
    have hqv : (q : ℤ) ∉ v.1.asIdeal := by
      intro hmem
      apply hv
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      have hmax : (placeZ q hq).asIdeal.IsMaximal := (placeZ q hq).isMaximal
      exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hmem)).symm
    obtain ⟨t, l, hl, htl⟩ := v.1.isMaximal.exists_inv hqv
    have hlq : ∀ u : Plc ℚ, (q : 𝓞 ℚ) ∈ u.asIdeal → (l : 𝓞 ℚ) ∉ u.asIdeal := by
      intro u hu hlu
      have h1 : ((t : 𝓞 ℚ) * (q : 𝓞 ℚ) + (l : 𝓞 ℚ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) htl
      have h2 : (1 : 𝓞 ℚ) ∈ u.asIdeal := h1 ▸ u.asIdeal.add_mem (u.asIdeal.mul_mem_left _ hu) hlu
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
    let a : AfQ := algebraMap ℚ AfQ ((l : ℚ)⁻¹) * e
    have hint : IsIntAf (T.ρ a) := by
      refine (T.int a).2 fun u _ => ?_
      by_cases h : (q : 𝓞 ℚ) ∈ u.asIdeal
      · have h1 : a u = algebraMap ℚ (u.adicCompletion ℚ) ((l : ℚ)⁻¹) * e u := by
          rw [← hev]; rfl
        have h2 := val_of_not_mem u (l : 𝓞 ℚ) (hlq u h) (algebraMap ℚ (u.adicCompletion ℚ))
        have h3 : algebraMap (𝓞 ℚ) ℚ (l : 𝓞 ℚ) = (l : ℚ) := by simp
        rw [h3] at h2
        rw [h1, (he u).1 h, mul_one, map_inv₀, map_inv₀]
        exact ((congrArg Inv.inv h2).trans inv_one).le
      · have h1 : a u = algebraMap ℚ (u.adicCompletion ℚ) ((l : ℚ)⁻¹) * e u := by
          rw [← hev]; rfl
        rw [h1, (he u).2 h, mul_zero, map_zero]
        exact zero_le'
    have hv1 := hint v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv1
    have h2 : AfP.eval v (T.ρ a) = algebraMap ℚ (v.1.adicCompletion ℚ) ((l : ℚ)⁻¹) := by
      show AfP.eval v (T.ρ (algebraMap ℚ AfQ ((l : ℚ)⁻¹) * e)) = _
      rw [map_mul, map_mul, hrat, h1, mul_one, AlgHom.commutes]
    have h3 := val_of_mem v.1 l hl (algebraMap ℚ (v.1.adicCompletion ℚ))
    have h4 : algebraMap ℤ ℚ l = (l : ℚ) := by simp
    rw [h4] at h3
    have hl0 : (l : ℚ) ≠ 0 := by
      intro h0
      have hl0' : l = 0 := by exact_mod_cast h0
      obtain ⟨u, hu, -⟩ := exists_place hq hp hqp
      exact hlq u hu (by simp [hl0'])
    have h5 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (l : ℚ)) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero]; exact hl0
    have h6 := (one_lt_inv₀ (zero_lt_iff.2 h5)).2 h3
    have h7 : AfP.eval v (T.ρ a) ∈ v.1.adicCompletionIntegers ℚ := hint v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2, map_inv₀, map_inv₀] at h7
    exact absurd h7 (not_le.2 h6)
  refine ⟨(h01 _).resolve_left fun h0 => ?_, hA⟩
  have hz : T.ρ e = 0 := by
    refine afp_ext fun v => ?_
    by_cases hv : v = placeAway hq hp hqp
    · rw [hv, h0, map_zero]
    · rw [hA v hv, map_zero]
  obtain ⟨u, hu, hpu⟩ := exists_place hq hp hqp
  have := ((T.ker e).1 hz) u hpu
  rw [(he u).1 hu] at this
  exact one_ne_zero this


open Classical in
private def secAdd {p : ℕ} (v₀ : AwayP p) : v₀.1.adicCompletion ℚ →+ AfP p where
  toFun x := ⟨Pi.single v₀ x, by
    have : ({v₀}ᶜ : Set (AwayP p)) ∈ Filter.cofinite := by simp
    refine Filter.mem_of_superset this fun v hv => ?_
    have : v ≠ v₀ := hv
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne this]
    exact zero_mem _⟩
  map_zero' := by
    refine afp_ext fun v => ?_
    show (Pi.single v₀ (0 : v₀.1.adicCompletion ℚ) : ∀ v : AwayP p, v.1.adicCompletion ℚ) v = 0
    simp
  map_add' x y := by
    refine afp_ext fun v => ?_
    show (Pi.single v₀ (x + y) : ∀ v : AwayP p, v.1.adicCompletion ℚ) v =
      (Pi.single v₀ x : ∀ v : AwayP p, v.1.adicCompletion ℚ) v + (Pi.single v₀ y : ∀ v : AwayP p, v.1.adicCompletion ℚ) v
    simp [Pi.single_add]

private theorem eval_secAdd {p : ℕ} (v₀ : AwayP p) (x) : AfP.eval v₀ (secAdd v₀ x) = x := by
  classical
  show (Pi.single v₀ x : ∀ v : AwayP p, v.1.adicCompletion ℚ) v₀ = x
  simp

private theorem secAdd_eval {p : ℕ} (v₀ : AwayP p) (r a : AfP p) (h1 : AfP.eval v₀ r = 1)
    (h0 : ∀ v, v ≠ v₀ → AfP.eval v r = 0) : secAdd v₀ (AfP.eval v₀ a) = r * a := by
  classical
  refine afp_ext fun v => ?_
  rw [map_mul]
  by_cases hv : v = v₀
  · subst hv
    rw [eval_secAdd, h1, one_mul]
  · rw [h0 v hv, zero_mul]
    show (Pi.single v₀ _ : ∀ v : AwayP p, v.1.adicCompletion ℚ) v = 0
    exact Pi.single_eq_of_ne hv _

private theorem core {E R : Type} [Field E] [NumberField E] [CommRing R] [Algebra ℚ R] {n p : ℕ}
    (Φ : Af E →+* R ⊗[ℚ] E) (Φ_surj : Function.Surjective Φ)
    (Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0)
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (mu : IsMu μ)
    (r : R) (c : Af E) (hc : Φ c = r ⊗ₜ[ℚ] (1 : E)) (Z : Matrix (Fin n) (Fin n) (Af E))
    (hZ : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      pLoc E w c = 0 ∨ (pLoc E w c = 1 ∧ (Z.map (pLoc E w)).charpoly.Separable))
    (M : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (hM : μ M = Z.map Φ) (x y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)
    (hx : (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (x * M - M * x) = 0)
    (hy : (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (y * M - M * y) = 0) :
    (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (x * y - y * x) = 0 := by
  classical
  have lift : ∀ u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E, ∃ U : Matrix (Fin n) (Fin n) (Af E), Φ.mapMatrix U = μ u := fun u =>
    ⟨Matrix.of fun i k => (Φ_surj (μ u i k)).choose, Matrix.ext fun i k => (Φ_surj (μ u i k)).choose_spec⟩
  obtain ⟨X, hX⟩ := lift x
  obtain ⟨Y, hY⟩ := lift y
  have hM' : μ M = Φ.mapMatrix Z := hM
  have hcc : μ (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) = Φ.mapMatrix (c • (1 : Matrix (Fin n) (Fin n) (Af E))) := by
    refine Matrix.ext fun i k => ?_
    rw [mu, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp [hc]
    · simp
  have hzero : ∀ W : Matrix (Fin n) (Fin n) (Af E), Φ.mapMatrix ((c • (1 : Matrix (Fin n) (Fin n) (Af E))) * W) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w c • (pLoc E w).mapMatrix W = 0 := by
    intro W
    constructor
    · intro h w hw
      refine Matrix.ext fun i k => ?_
      have h1 := congrFun (congrFun h i) k
      simp only [smul_mul_assoc, one_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply] at h1
      have h2 := (Φ_ker _).1 h1 w hw
      simpa [map_mul] using h2
    · intro h
      refine Matrix.ext fun i k => ?_
      simp only [smul_mul_assoc, one_mul, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply]
      refine (Φ_ker _).2 fun w hw => ?_
      have h1 := congrFun (congrFun (h w hw) i) k
      simpa [map_mul] using h1
  have hd : ∀ (u v : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (U V : Matrix (Fin n) (Fin n) (Af E)), Φ.mapMatrix U = μ u →
      Φ.mapMatrix V = μ v → μ ((r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (u * v - v * u)) =
        Φ.mapMatrix ((c • (1 : Matrix (Fin n) (Fin n) (Af E))) * (U * V - V * U)) := by
    intro u v U V hU hV
    rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, hU, hV, hcc]
  have hloc : ∀ (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (U : Matrix (Fin n) (Fin n) (Af E)), Φ.mapMatrix U = μ u →
      (r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) * (u * M - M * u) = 0 → ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      pLoc E w c = 1 → (pLoc E w).mapMatrix Z * (pLoc E w).mapMatrix U = (pLoc E w).mapMatrix U * (pLoc E w).mapMatrix Z := by
    intro u U hU h w hw h1
    have h2 := hd u M U Z hU hM'.symm
    rw [h, map_zero] at h2
    have h3 := (hzero _).1 h2.symm w hw
    rw [h1, one_smul, map_sub, map_mul, map_mul] at h3
    exact (sub_eq_zero.1 h3).symm
  apply μ.injective
  rw [map_zero, hd x y X Y hX hY, hzero]
  intro w hw
  rcases hZ w hw with h0 | ⟨h1, hs⟩
  · rw [h0, zero_smul]
  · rw [h1, one_smul, map_sub, map_mul, map_mul]
    exact sub_eq_zero.2 (mat_comm hs (hloc x X hX hx w hw h1) (hloc y Y hY hy w hw h1))

theorem regTr : RegTr := by
  intro E _ _ _ A n p _ S T q hq hqp g hg
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨e, he, heE⟩ := UpperTheory.Gal.W2.Seed.pIdemP q E
  obtain ⟨h1, h0⟩ := rho_idem hq hqp T.toAdQ e he
  refine ⟨placeAway hq Fact.out hqp, fun x y hx hy => ?_⟩
  refine tensor_comm (AfP.eval (placeAway hq Fact.out hqp)) (T.ρ e)
    (secAdd (placeAway hq Fact.out hqp)).toRatLinearMap (eval_secAdd _)
    (fun a => secAdd_eval _ _ a h1 h0) h1 (S.mx (T.j g)) (fun x y hx hy => ?_) x y hx hy
  refine core T.Φ T.Φ_surj T.Φ_ker T.μ T.mu (T.ρ e) (finiteAdeleMap ℚ E e) (T.Φ_Q e)
    (T.a * mat g * T.a⁻¹).val (fun w hw => ?_) _ (T.j_mx g) x y hx hy
  by_cases hqw : (q : 𝓞 E) ∈ w.asIdeal
  · refine Or.inr ⟨(heE w).1 hqw, ?_⟩
    have h2 : ((T.a * mat g * T.a⁻¹).val).map (pLoc E w) =
        (GeneralLinearGroup.map (pLoc E w) T.a).val * (comp w g).val * ((GeneralLinearGroup.map (pLoc E w) T.a)⁻¹).val := by
      have : GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) =
          GeneralLinearGroup.map (pLoc E w) T.a * comp w g * (GeneralLinearGroup.map (pLoc E w) T.a)⁻¹ := by
        rw [map_mul, map_mul, map_inv]; rfl
      exact congrArg Units.val this
    rw [h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hg w hqw
  · exact Or.inl ((heE w).2 hqw)

end UpperTheory.Gal.Spc
end
end

theorem UpperTheory.Gal.Spc.specTopG :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecTopG := by
  intro hW E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq X
  obtain ⟨r, W, hrX, haux⟩ := UpperTheory.Gal.Spc.auxiliary_prime_holds E A n p S x U w₀ Up V hgen X
  refine ⟨r, haux.prime, hrX, haux.ne, ?_⟩
  intro N hrN hst J g θ hseen
  obtain ⟨L, hw, Ty, hTy⟩ := UpperTheory.Gal.Spc.tyEx E A n p S F x U w₀ Up V hoff r W haux N hrN hst
  have hx : UpperTheory.Gal.Spc.Extra S F.j := by
    rw [F.j_tr]
    exact ⟨fun w hp => UpperTheory.Gal.Spc.plTr E A n p S F.tr w hp,
      fun q hq' hqp g hg => UpperTheory.Gal.Spc.regTr E A n p S F.tr q hq' hqp g hg⟩
  exact UpperTheory.Gal.Spc.specData hW E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst
    L hw Ty hTy hx J g θ hseen
