module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes GlobalTheory.LKGeo.MultScale
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.MultiplicativeUnitDivisibility

variable {p : ℕ} [Fact p.Prime]

private theorem exists_dvd_EFA (D : Datum p) (d : ℤ) (hd : ∀ x y : D.La, d ∣ D.EF x y)
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    ∃ c : AfP p, IsIntAf c ∧ EFA D v w = (d : AfP p) * c := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      obtain ⟨k, hk⟩ := hd x x'
      refine ⟨a * a' * (k : AfP p), isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast k), ?_⟩
      rw [EFA_tmul, hk]
      push_cast
      ring
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨c, hc, e⟩ := h
      obtain ⟨c', hc', e'⟩ := h'
      exact ⟨c + c', isIntAf_add hc hc', by rw [map_add (f := _), e, e', mul_add]⟩
    | neg u _ h =>
      obtain ⟨c, hc, e⟩ := h
      exact ⟨-c, isIntAf_neg hc, by rw [map_neg, e, mul_neg]⟩
  | zero => exact ⟨0, isIntAf_zero, by simp⟩
  | add u u' _ _ h h' =>
    obtain ⟨c, hc, e⟩ := h
    obtain ⟨c', hc', e'⟩ := h'
    exact ⟨c + c', isIntAf_add hc hc', by rw [map_add (f := _), LinearMap.add_apply, e, e', mul_add]⟩
  | neg u _ h =>
    obtain ⟨c, hc, e⟩ := h
    exact ⟨-c, isIntAf_neg hc, by rw [map_neg, LinearMap.neg_apply, e, mul_neg]⟩

private theorem exists_ne (D : Datum p) : ∃ x y : D.La, D.EF x y ≠ 0 := by
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hr : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  haveI := Module.nontrivial_of_finrank_pos hr
  obtain ⟨x, hx⟩ := _root_.exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := by
    intro h
    apply hx
    apply D.nondeg
    rw [h, map_zero]
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

private theorem isUnit_intCast {d : ℤ} (hd : d ≠ 0) : IsUnit (d : AfP p) := by
  have h : IsUnit (d : ℚ) := (Int.cast_ne_zero.mpr hd).isUnit
  simpa using h.map (algebraMap ℚ (AfP p))

private theorem isIntAf_sim {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf)
    (hg : ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D) : IsIntAf ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) := by
  let S : Set ℤ := {z | ∃ x y : D.La, D.EF x y = z}
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal (Ideal.span S)).principal
  have hdvd : ∀ x y : D.La, d ∣ D.EF x y := by
    intro x y
    have hm : D.EF x y ∈ Ideal.span S := Ideal.subset_span ⟨x, y, rfl⟩
    rw [hdI] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := exists_ne D
    apply hxy
    obtain ⟨k, hk⟩ := hdvd x y
    rw [hk, zero_mul]
  have key : ∀ z ∈ Ideal.span S, ∃ c : AfP p, IsIntAf c ∧
      ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * (z : AfP p) = (d : AfP p) * c := by
    intro z hz
    change z ∈ Submodule.span ℤ S at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      have h1 := EFA_actG L g (inAf D x) (inAf D y)
      rw [EFA_inAf] at h1
      rw [← h1]
      exact exists_dvd_EFA D d hdvd (hg _ (inAf_mem D x)) (hg _ (inAf_mem D y))
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add a b _ _ h1 h2 =>
      obtain ⟨c1, h1i, h1e⟩ := h1
      obtain ⟨c2, h2i, h2e⟩ := h2
      refine ⟨c1 + c2, isIntAf_add h1i h2i, ?_⟩
      rw [Int.cast_add, mul_add, h1e, h2e, mul_add]
    | smul a b _ h =>
      obtain ⟨c, hi, he⟩ := h
      refine ⟨a * c, isIntAf_mul (isIntAf_intCast a) hi, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨c, hc, hce⟩ := key d (by rw [hdI]; exact Submodule.mem_span_singleton_self d)
  have hsc : ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) = c :=
    (isUnit_intCast (p := p) hd0).mul_left_cancel (by rw [mul_comm]; exact hce)
  rw [hsc]
  exact hc

private theorem pow_dvd_of_isIntAf {q k c c' : ℕ} (hq : q.Prime) (hqp : q ≠ p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) (hd : q ^ k ∣ c') : q ^ k ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  have hm : IsIntAf ((m : AfP p) * t) := by
    have hmi := isIntAf_intCast (p := p) (m : ℤ)
    rw [Int.cast_natCast] at hmi
    exact isIntAf_mul hmi ht
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let v0 : HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime hq0).mpr hqz,
      by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0⟩
  have hv0p : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro heq
    have hmem : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := heq ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hmem
    have hpq : p ∣ q := Int.natCast_dvd_natCast.mp hmem
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpq).symm
  let v : AwayP p := ⟨v0, hv0p⟩
  have hev : (AfP.eval v) (c : AfP p) =
      (q : HeightOneSpectrum.adicCompletion ℚ v0) ^ k * (AfP.eval v) ((m : AfP p) * t) := by
    rw [h, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, map_natCast]
  have hval : ∀ n : ℕ, Valued.v (n : HeightOneSpectrum.adicCompletion ℚ v0) = v0.intValuation (n : ℤ) := by
    intro n
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v0 (n : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [← h1]
    congr 1
    simp
  have hs : Valued.v ((AfP.eval v) ((m : AfP p) * t)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v0).mp (hm v)
  have hle : v0.intValuation (c : ℤ) ≤ WithZero.exp (-(k : ℤ)) := by
    have hc := hval c
    rw [map_natCast] at hev
    rw [← hc, hev, map_mul, map_pow, hval q, HeightOneSpectrum.intValuation_singleton v0 hq0 rfl]
    refine (mul_le_of_le_one_right' hs).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hle
  change Ideal.span {(q : ℤ)} ^ k ∣ Ideal.span {(c : ℤ)} at hle
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at hle
  exact_mod_cast hle

private theorem dvd_of_isIntAf {c c' : ℕ} (hc' : c'.Coprime p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) : c' ∣ c := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd c c']
  intro q k hq hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hqp : q ≠ p := by
      rintro rfl
      have hqc : q ∣ c' := (dvd_pow_self q hk.ne').trans hqk
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqc hc') dvd_rfl)
    exact pow_dvd_of_isIntAf hq hqp ht h hqk

private theorem main : MultUnit := by
  intro p _ D G L
  refine ⟨?_, ?_⟩
  · intro u hu
    have hst : ∀ g ∈ L.KN 1, ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
      intro g hg v hv
      obtain ⟨w, hw, e⟩ := hg.1 v hv
      rw [e, one_smul]
      exact add_mem hv hw
    have h1 := isIntAf_sim L u (hst u hu)
    have h2 := isIntAf_sim L u⁻¹ (hst _ (inv_mem hu))
    refine ⟨((uSimR (AfP p) u⁻¹ : (AfP p)ˣ) : AfP p), h1, h2, ?_⟩
    have h3 : (uSimR (AfP p) u⁻¹ : (AfP p)ˣ) = ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ := rfl
    rw [h3]
    exact Units.mul_inv _
  · intro c c' t t' hc hc' ht ht' htt h
    refine Nat.dvd_antisymm ?_ (dvd_of_isIntAf hc' ht h)
    refine dvd_of_isIntAf hc ht' ?_
    rw [h, mul_assoc, htt, mul_one]

end UpperTheory.MultiplicativeUnitDivisibility

theorem UpperTheory.multiplier_is_unit : MultUnit := UpperTheory.MultiplicativeUnitDivisibility.main
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceSubgroupIsLatticeStatement
open UpperTheory.Gal.Int.Geo
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem UpperTheory.grpLat_half {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {M : ℕ}
    (hM : 0 < M) (hc : M.Coprime p) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (s₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = M • v)
    (e : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG h₂ (inAf D x) = M • v) →
      ∃ v ∈ LaHat D, L.actG h₁ (inAf D x) = M • v) :
    ∀ v ∈ LaHat D, L.actG (h₁ * h₂⁻¹) v ∈ LaHat D := by
  intro v hv
  obtain ⟨v', hv', e₁⟩ := s₂ v hv
  obtain ⟨x, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D M hM hc v' hv'
  obtain ⟨u, hu, e₃⟩ := e x ⟨v - L.actG h₂ w, sub_mem hv (i₂ w hw), by
    have h : L.actG h₂ v' = L.actG h₂ (inAf D x) + M • L.actG h₂ w := by
      rw [e₂, map_add (f := _), map_nsmul]
    rw [smul_sub, ← e₁, h]
    abel⟩
  have e₄ : M • L.actG (h₁ * h₂⁻¹) v = M • (u + L.actG h₁ w) := by
    have h : L.actG h₂⁻¹ (M • v) = v' := by
      rw [← e₁, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [← map_nsmul, map_mul, Module.End.mul_apply, h, e₂, map_add (f := _), map_nsmul, e₃, smul_add]
  have e₅ : L.actG (h₁ * h₂⁻¹) v = u + L.actG h₁ w := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at e₄
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hM.ne' : (M : ℚ) ≠ 0) e₄
  rw [e₅]
  exact add_mem hu (i₁ w hw)

theorem UpperTheory.congruenceSubgroup_isLattice_statement :
    GrpLat := by
  intro p _ D G L M hM hc h₁ h₂ i₁ i₂ s₁ s₂ e
  have a := UpperTheory.grpLat_half L hM hc i₁ i₂ s₂ (fun x => (e x).2)
  have b := UpperTheory.grpLat_half L hM hc i₂ i₁ s₁ (fun x => (e x).1)
  refine ⟨fun v hv => ⟨L.actG (h₁ * h₂⁻¹) v - v, sub_mem (a v hv) hv, by simp⟩,
    fun v hv => ⟨L.actG (h₁ * h₂⁻¹)⁻¹ v - v, sub_mem ?_ hv, by simp⟩⟩
  rw [mul_inv_rev, inv_inv]
  exact b v hv
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerPointCountStatement
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_point_count_statement :
    Count := by
  intro Γ _ K₀ H K hKH hHK₀ hK F κ hF hκ ζ
  classical
  have hmul : K.relIndex H * H.relIndex K₀ = K.relIndex K₀ :=
    Subgroup.relIndex_mul_relIndex K H K₀ hKH hHK₀
  have hKH0 : K.relIndex H ≠ 0 := fun h0 => hK (by rw [← hmul, h0, zero_mul])
  have hH0 : H.relIndex K₀ ≠ 0 := fun h0 => hK (by rw [← hmul, h0, mul_zero])
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hH0)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (↥K₀ ⧸ K.subgroupOf K₀) := Nat.finite_of_card_ne_zero hK
  haveI : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero hKH0
  have bound : ∀ ξ : F, Nat.card {x // κ x = ξ} ≤ K.relIndex H := by
    intro ξ
    by_cases hne : Nonempty {x // κ x = ξ}
    · obtain ⟨⟨q0, hq0⟩⟩ := hne
      have memH : ∀ q : {x // κ x = ξ},
          ((q0.out : ↥K₀) : Γ)⁻¹ * ((q.1.out : ↥K₀) : Γ) ∈ H := by
        intro q
        apply hκ
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq', hq0, q.2]
      let f : {x // κ x = ξ} → ↥H ⧸ K.subgroupOf H := fun q => ((⟨_, memH q⟩ : ↥H) : ↥H ⧸ K.subgroupOf H)
      have hinj : Function.Injective f := by
        intro q1 q2 h12
        have h' := QuotientGroup.eq.mp h12
        rw [Subgroup.mem_subgroupOf] at h'
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' q1.1, ← QuotientGroup.out_eq' q2.1]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using h'
      calc Nat.card {x // κ x = ξ} ≤ Nat.card (↥H ⧸ K.subgroupOf H) :=
            Nat.card_le_card_of_injective f hinj
        _ = K.relIndex H := rfl
    · haveI := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hsum : ∑ ξ : F, Nat.card {x // κ x = ξ} = ∑ ξ : F, K.relIndex H := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv κ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hF, mul_comm, hmul]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le (fun ξ _ => bound ξ)).mp hsum ζ (Finset.mem_univ _)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientInvariantOfTraceUnitCrt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem isIntAf_one' {p : ℕ} [Fact p.Prime] : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] {D : Datum p} (y : D.La) : inAf D y ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, y, isIntAf_one', rfl⟩

set_option maxHeartbeats 200000 in
theorem UpperTheory.quotient_invariant_of_trace_unit_crt :
    NumEx → QComp → QIso → ClsEx → TrEta → TrUnit → CongCRT → BaseInv := by
  intro hNumEx hQComp hQIso hClsEx hTrEta hTrUnit hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N' N t c a hN't hNum C' C u hu W
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have hNum' := (hNumEx p D E gb w q r 𝔴 𝔫 S (N : ℕ) hNpos).2 c a t hNum
  obtain ⟨hNc, hGen⟩ := hNum
  obtain ⟨-, hGen'⟩ := hNum'
  rw [← hN't] at hGen'
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hu1 := ((hLev u).mp hu).1
  have hIu : Integ L u := integ_of_mem hu1
  have hCRTu := hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu
  have hC := hCRTu.1.mp (by have h1 := ((hLev u).mp hu).2; rwa [S.lev] at h1)
  have hEta : ∀ y : D.La, (T.M N').univ.eta ((c * t) • y) ≫ W.ψ = W.o.eta (c • y) := by
    intro y
    obtain ⟨v, hv, ev⟩ := hC.1 _ (inAf_mem' y)
    exact hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans S.N₀ (c * t) c hN'c hNc y y ⟨v, hv, ev⟩
  obtain ⟨hIso, hLB⟩ := hTrUnit p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans hu1
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨n', hn'⟩ := hQIso q _ _ _ _ _ _ _ _ c (c * t) _ _ _ _ (T.M N').univ W.o S.Y.univ _ W.ψ hIso W.trans.1
    W.trans.2.1 hLB hEta qC
  have hov : (W.π ≫ C.j) ≫ S.Y.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, reassoc_of% W.ov]
  have hlv : ∀ y : D.La, ((T.M N').univ.eta ((algebraMap (𝓞 D.F) D.O) (↑t * a) • y)).left ≫ n'.φ =
      (W.π ≫ C.j) ≫ (S.Y.lv y).left := by
    intro y
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y = t • ((algebraMap (𝓞 D.F) D.O) a • y) := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    obtain ⟨v₂, hv₂, e₂⟩ := (hCRTu.2 a N hNpos N.2.2 hGen).mp hC.2 y
    have hTE := hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ ⟨v₂, hv₂, e₂⟩
    rw [one_smul] at hTE
    rw [hsm, hn', hqC, ← Category.assoc, ← Over.comp_left, hTE, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]
  obtain ⟨-, huq⟩ := hClsEx q _ _ _ S.b gb _ S.mat _ _ _ _ _ hN'c hN'pos h3 hcq hGen' S.Y _ _ (T.M N').univ
  obtain ⟨hj, hm⟩ := huq ⟨W.π ≫ C.j, hov, n', hlv⟩ C'
  refine ⟨hj, ?_⟩
  calc Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = n'.φ := by rw [hn', hqC]
    _ = C'.m.φ := hm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ArithmeticGroupCongruenceSubgroupProperty
set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem actOn_comm_mulF (x : 𝓞 D.F) (y : AfP p ⊗[ℚ] G.C) :
    actOn L.rep (AfP p) y * mulF D x = mulF D x * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), add_mul, mul_add, ha, hb]
  | tmul a c =>
    have hc : L.rep c * actQ D (algebraMap (𝓞 D.F) D.O x) = actQ D (algebraMap (𝓞 D.F) D.O x) * L.rep c :=
      (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ _
    have hb : (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) * mulF D x =
        mulF D x * (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) hc
      rw [map_mul, map_mul] at this
      exact this
    have ht : actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = algebraMap (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) a *
        Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c) :=
      Algebra.TensorProduct.lift_tmul _ _ _ a c
    rw [ht, mul_assoc, hb, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D x v) = mulF D x (L.actG g v) :=
  congrArg (fun f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) => f v) (actOn_comm_mulF L x _)

private theorem actG_idHat {g : G.GAf} (hg : Integ L g) (𝔟 : Ideal (𝓞 D.F)) {z : AfP p ⊗[ℚ] VQ D}
    (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    rw [actG_mulF]
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end UpperTheory.Gal.Int.Geo

open UpperTheory.Gal.Int.Geo in
theorem UpperTheory.arithmeticGroup_congruenceSubgroupProperty : UpperTheory.Gal.Int.Geo.GrpCong := by
  intro p _ D G L 𝔫 K₀ hK h u _ hc hu hg
  refine (hK _).2 ⟨hg, fun v hv => ?_⟩
  obtain ⟨huK, huC⟩ := (hK u).1 hu
  have huv : L.actG u v ∈ LaHat D := integ_of_mem huK v hv
  have e1 := hc _ huv
  have e2 := huC v hv
  have e3 := actG_idHat L (integ_of_mem hg) 𝔫 (hc v hv)
  have hcomp : L.actG (h * u * h⁻¹) (L.actG h v) = L.actG h (L.actG u v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  have key : L.actG (h * u * h⁻¹) v - v = (L.actG h (L.actG u v) - L.actG u v) + (L.actG u v - v)
      - L.actG (h * u * h⁻¹) (L.actG h v - v) := by
    rw [map_sub, hcomp]; abel
  rw [key]
  exact sub_mem (add_mem e1 e2) e3

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerFiniteEtaleOfTrivialPowerCartesian
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.Int.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.tower_finiteEtale_of_trivial_powerCartesian :
    PiZero → PowCart → PiFet := by
  intro h0 hpc p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hN C
  obtain ⟨ρ, e0, hop, hcl, htr⟩ := h0 p D G L E gb w q r 𝔴 𝔫 S k T N c a hN C
  have hx : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have hN' : (N : ℕ) = S.N₀ * c := by
    unfold Site.Num at hN
    exact hN.1
  have hsub : ∀ (n m : ℕ) (g : G.GAf), L.CongOne (n * m) g → L.CongOne n g := by
    intro n m g hg
    unfold GlobalTheory.LKGeo.Link.CongOne at hg ⊢
    intro v hv
    obtain ⟨u, hu, huv⟩ := hg v hv
    exact ⟨m • u, AddSubgroup.nsmul_mem _ hu m, by rw [huv, mul_smul]⟩
  obtain ⟨hy, htr'⟩ : ∃ hy, T.X.tr (T.lev N) _ 1 hx hy ≫ ρ = _ := ⟨_, htr hx (by
    intro u hu
    rw [one_mul, inv_one, mul_one]
    rw [T.3] at hu ⊢
    rw [hN'] at hu
    show u ∈ L.KN S.N₀
    unfold GlobalTheory.LKGeo.Link.KN at hu ⊢
    exact ⟨hsub _ _ _ hu.1, hsub _ _ _ hu.2⟩)⟩
  have hG := S.mπ.3
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback at hG
  have hpb := hG.1
  obtain ⟨hP1, hP2, -⟩ := hpc S.Y.X S.M.X S.M.X S.Y.univ.A S.M.univ.A S.M.univ.A S.π (𝟙 _) S.mπ.φ (𝟙 _)
    hpb.w (by simp) k
  have hPB := hP1 hpb
  have hfinP : IsFinite (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hPB.flip S.20
  have hetP : Etale (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @Etale) hPB.flip S.21
  have hcomm : (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [← Category.assoc, hP2, Category.assoc, S.18]
  have eY : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q (T.lev N) ≫ gen (Ow w) E := by
    rw [hcomm, ← Category.assoc, ← htr', Category.assoc, e0, ← Category.assoc, T.X.10]
  refine ⟨eY, ?_⟩
  have h1 : ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) ≫ 𝟙 _ =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [Category.comp_id, hcomm]
  have h2 : gen (Ow w) E ≫ 𝟙 _ = 𝟙 _ ≫ gen (Ow w) E := by
    rw [Category.comp_id, Category.id_comp]
  let hm := pullback.map ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (gen (Ow w) E)
    ((GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s) (gen (Ow w) E)
    (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) (𝟙 _) (𝟙 _) h1 h2
  have h3 : gen (Ow w) E = 𝟙 _ ≫ gen (Ow w) E := (Category.id_comp _).symm
  have hmF : IsFinite hm := MorphismProperty.pullbackMap (P := @IsFinite) hfinP inferInstance hcomm h3
  haveI := hetP
  have hmU : FormallyUnramified hm :=
    MorphismProperty.pullbackMap (P := @FormallyUnramified) inferInstance inferInstance hcomm h3
  have hkey : pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm =
      T.X.tr _ _ 1 hx hy ≫ pullback.lift ρ _ e0 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, htr']
      simp only [hm, pullback.lift_fst_assoc, pullback.map, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, T.X.10]
      simp only [hm, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI := hop
  haveI := hcl
  haveI := T.X.13 _ _ hx hy
  haveI := T.X.14 _ _ hx hy
  have hcomp : IsFinite (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) ∧
      Etale (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) := by
    rw [hkey]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hcomp.1
  haveI := hcomp.2
  exact ⟨IsFinite.of_comp _ hm, Etale.of_comp _ hm⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PowerProjectorExists
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IteratedFiberPowerZeroIsIsoAndSuccIsPullback
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem UpperTheory.power_zero_isIso {S : Scheme.{0}} (A : Over S) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let g : Over.mk (𝟙 S) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let f : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 S) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have hfg : f ≫ g = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨g.left, ?_, ?_⟩⟩
  · have h := congrArg (fun x => x.left) hfg
    simpa [f] using h
  · simpa using Over.w g

private theorem UpperTheory.power_succ_lift {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (a : T ⟶ GlobalTheory.KS.pow A m) (b : T ⟶ A) :
    ∃ l : T ⟶ GlobalTheory.KS.pow A (m + 1),
      l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) = a ∧
      l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) = b := by
  refine ⟨Pi.lift fun j => Fin.lastCases (motive := fun _ => T ⟶ A) b
    (fun i => a ≫ Pi.π (fun _ : Fin m => A) i) j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    simp
  · simp

private theorem UpperTheory.power_succ_lift_unique {S : Scheme.{0}} (A : Over S) (m : ℕ) (T : Over S)
    (l l' : T ⟶ GlobalTheory.KS.pow A (m + 1))
    (h₁ : l ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc) =
      l' ≫ (Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc))
    (h₂ : l ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m) =
      l' ≫ Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)) : l = l' := by
  refine Pi.hom_ext _ _ fun j => ?_
  induction j using Fin.lastCases with
  | last => exact h₂
  | cast i => simpa using congrArg (· ≫ Pi.π (fun _ : Fin m => A) i) h₁

theorem UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback :
    ∀ {S : Scheme.{0}} (A : Over S), IsIso (GlobalTheory.KS.pow A 0).hom ∧ ∀ m : ℕ, ∃ (u : (GlobalTheory.KS.pow A (m + 1)).left ⟶ (GlobalTheory.KS.pow A m).left) (v : (GlobalTheory.KS.pow A (m + 1)).left ⟶ A.left), IsPullback u v (GlobalTheory.KS.pow A m).hom A.hom ∧ u ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A (m + 1)).hom := by
  intro S A
  refine ⟨UpperTheory.power_zero_isIso A, fun m => ?_⟩
  let P : GlobalTheory.KS.pow A (m + 1) ⟶ GlobalTheory.KS.pow A m :=
    Pi.lift fun i : Fin m => Pi.π (fun _ : Fin (m + 1) => A) i.castSucc
  let Q : GlobalTheory.KS.pow A (m + 1) ⟶ A := Pi.π (fun _ : Fin (m + 1) => A) (Fin.last m)
  have w : P.left ≫ (GlobalTheory.KS.pow A m).hom = Q.left ≫ A.hom := (Over.w P).trans (Over.w Q).symm
  have hL := fun s : PullbackCone (GlobalTheory.KS.pow A m).hom A.hom =>
    UpperTheory.power_succ_lift A m (Over.mk (s.snd ≫ A.hom)) (Over.homMk s.fst s.condition)
      (Over.homMk s.snd rfl)
  refine ⟨P.left, Q.left, IsPullback.of_isLimit' ⟨w⟩
    (PullbackCone.IsLimit.mk w (fun s => (hL s).choose.left) ?_ ?_ ?_), Over.w P⟩
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.1]
    rfl
  · intro s
    rw [← Over.comp_left, (hL s).choose_spec.2]
    rfl
  · intro s n hn1 hn2
    have hn : n ≫ (GlobalTheory.KS.pow A (m + 1)).hom = s.snd ≫ A.hom := by
      rw [← Over.w Q, ← Category.assoc, hn2]
    let N : Over.mk (s.snd ≫ A.hom) ⟶ GlobalTheory.KS.pow A (m + 1) := Over.homMk n hn
    have h1 : N ≫ P = (hL s).choose ≫ P := by
      rw [(hL s).choose_spec.1]
      apply (Over.forget S).map_injective
      simpa [N] using hn1
    have h2 : N ≫ Q = (hL s).choose ≫ Q := by
      rw [(hL s).choose_spec.2]
      apply (Over.forget S).map_injective
      simpa [N] using hn2
    exact congrArg (fun x => x.left) (UpperTheory.power_succ_lift_unique A m _ N _ h1 h2)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open UpperTheory.Gal.Int.Geo

private theorem relDim_pow {S : Scheme.{0}} (A : Over S) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (k : ℕ) :
    SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  induction k with
  | zero =>
    obtain ⟨h0, -⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    simp only [zero_mul]
    infer_instance
  | succ m ih =>
    obtain ⟨-, hs⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    obtain ⟨u, v, hpb, hcomp⟩ := hs m
    have hu : SmoothOfRelativeDimension g u :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hpb.flip hg
    rw [← hcomp, Nat.succ_mul, Nat.add_comm]
    infer_instance

theorem UpperTheory.power_projector_exists :
    PowProj := by
  intro q _ D R _ _ b N _ _ X s o k
  letI := o.grp
  haveI := o.comm
  have hT := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle q D R b N X s o
  refine ⟨fun hs => GlobalTheory.KS.isProjOver_pow R X s hs o.A o.ab _ hT.2 o.ample k, ?_⟩
  intro d hd
  haveI := relDim_pow o.A D.g hT.1 k
  exact ⟨k * D.g + d, inferInstance⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerSeparatedOfTrivialPowerCartesian
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem kn_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {k u : G.GAf}
    (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x →
      L.CongOne N (g * x * g⁻¹) := by
    intro g hg hg' x hx
    unfold Link.CongOne at hg hg' hx ⊢
    intro v hv
    obtain ⟨w₁, hw₁, h₁⟩ := hg' v hv
    have hv₁ : L.actG g⁻¹ v ∈ LaHat D := by
      rw [h₁, one_smul]
      exact add_mem hv hw₁
    obtain ⟨w₂, hw₂, h₂⟩ := hx _ hv₁
    obtain ⟨w₃, hw₃, h₃⟩ := hg w₂ hw₂
    refine ⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩
    have hgg : L.actG g (L.actG g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add (f := _), hgg, map_nsmul, h₃,
      one_smul]
  have hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹ := hk
  have hu' : L.CongOne N u ∧ L.CongOne N u⁻¹ := hu
  show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹
  refine ⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩
  have hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [hinv]
  exact key k hk'.1 hk'.2 u⁻¹ hu'.2

private theorem gen_mono {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Mono (gen (Ow w) E) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)
  infer_instance

theorem UpperTheory.tower_separated_of_trivial_powerCartesian :
    PiZero → BaseSep → PowCart → PiSep := by
  intro hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz
  obtain ⟨ρ, e, hopen, -, htr⟩ := hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  have hKM := T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩
  revert hKM
  revert ρ
  generalize T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M
  intro ρ e hopen htr hKM
  have x : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M := fun u hu => by
    have hN : S.N₀ ∣ (N : ℕ) := ⟨c, hNum.1⟩
    have hu' : u ∈ L.KN S.N₀ := KN_anti hN (by rw [← T.K_eq]; exact hu)
    rw [hKM]
    simpa using hu'
  have htr' := htr x y
  have hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ := by
    rw [htr', ← Category.assoc, hz, Category.assoc]
  have hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M := by
    haveI : Mono (gen (Ow w) E) := gen_mono w
    rw [← cancel_mono (gen (Ow w) E)]
    simp only [Category.assoc]
    rw [← e]
    simp only [← Category.assoc] at hzM ⊢
    rw [hzM]
  have hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y := by
    haveI := hopen
    rw [← cancel_mono (pullback.lift ρ (T.X.q M) e)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hzM
    · simp only [Category.assoc, pullback.lift_snd]
      exact hzq
  have hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N) := by
    intro g hg u hu
    rw [hKM] at hg
    rw [T.K_eq] at hu ⊢
    exact kn_conj L (KN_anti (one_dvd _) hg) hu
  obtain ⟨g, hg, a', b', hz'⟩ := T.X.trans (T.lev N) M x y hnorm Ω z z' hzt
  refine ⟨g, ?_, a', b', hz'⟩
  rw [hKM] at hg
  obtain ⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩ := T.tr_eq N N g a' b'
  have hP2 := (hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ)
    (𝟙 _) hw (by simp) k).2.1
  have hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j :=
    (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1
  have h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom =
      z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π := by
    rw [hz', Category.assoc, reassoc_of% heq, hP2]
  have h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j =
      z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j := by
    have hz2 := hz
    unfold Site.pi at hz2
    rw [← hP3]
    simp only [← Category.assoc] at hz2 ⊢
    rw [hz2]
  refine hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_
  show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j =
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j
  simp only [Category.assoc]
  rw [h2, reassoc_of% h1]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerTrivialOfQuotientTracePowerCartesian
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private lemma pullback_lift_clopen_immersion {W X Mη M P B B' Z : Scheme.{0}} (j : X ⟶ Mη) (f₁ : Mη ⟶ M) (f₂ : Mη ⟶ B') (s : M ⟶ B)
    (g : B' ⟶ B) (hp : IsPullback f₁ f₂ s g) (h : P ⟶ M) (w : W ⟶ X) (φ : W ⟶ P)
    (hc : IsPullback φ w h (j ≫ f₁)) (ε : Z ≅ W) (ρ : Z ⟶ P) (hρ : ρ = ε.hom ≫ φ) (t : Z ⟶ B')
    (ht : t = ε.hom ≫ w ≫ j ≫ f₂) (e : ρ ≫ h ≫ s = t ≫ g) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsOpenImmersion (pullback.lift ρ t e) ∧ IsClosedImmersion (pullback.lift ρ t e) := by
  have hQ : IsPullback (pullback.fst (h ≫ s) g) (pullback.snd (h ≫ s) g) (h ≫ s) g :=
    IsPullback.of_hasPullback _ _
  have hu0 : (pullback.fst (h ≫ s) g ≫ h) ≫ s = pullback.snd (h ≫ s) g ≫ g := by
    rw [Category.assoc]; exact pullback.condition
  let u : pullback (h ≫ s) g ⟶ Mη := hp.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) hu0
  have hu1 : u ≫ f₁ = pullback.fst _ _ ≫ h := hp.lift_fst _ _ _
  have hu2 : u ≫ f₂ = pullback.snd _ _ := hp.lift_snd _ _ _
  have A : IsPullback u (pullback.fst (h ≫ s) g) f₁ h :=
    IsPullback.of_right (h₁₂ := f₂) (v₁₃ := g) (h₂₂ := s) (by rw [hu2]; exact hQ.flip) hu1 hp.flip
  have hφ : φ ≫ h ≫ s = (w ≫ j ≫ f₂) ≫ g := by
    rw [← Category.assoc, hc.w]
    simp only [Category.assoc, hp.w]
  let l : W ⟶ pullback (h ≫ s) g := pullback.lift φ (w ≫ j ≫ f₂) hφ
  have hl1 : l ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hl2 : l ≫ pullback.snd _ _ = w ≫ j ≫ f₂ := pullback.lift_snd _ _ _
  have hlu : l ≫ u = w ≫ j := by
    apply hp.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hl1, hc.w, Category.assoc]
    · rw [Category.assoc, hu2, hl2, Category.assoc]
  have B1 : IsPullback l w u j :=
    IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := h) (h₂₂ := f₁) (by rw [hl1]; exact hc) hlu A.flip
  have o1 : IsOpenImmersion l := MorphismProperty.of_isPullback (P := @IsOpenImmersion) B1.flip inferInstance
  have o2 : IsClosedImmersion l := MorphismProperty.of_isPullback (P := @IsClosedImmersion) B1.flip inferInstance
  have hE : pullback.lift ρ t e = ε.hom ≫ l := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hl1, hρ]
    · rw [pullback.lift_snd, Category.assoc, hl2, ht]
  rw [hE]
  exact ⟨inferInstance, inferInstance⟩

private lemma powMap_congr {S' S₁ : Scheme.{0}} {A' : Over S'} {A : Over S₁} {f f' : S' ⟶ S₁} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m = GlobalTheory.KS.powMap f' φ' h' m := by
  subst hf; subst hφ; rfl

theorem UpperTheory.tower_trivial_of_quotient_trace_powerCartesian :
    MIn → QObj → QComp → QIso → QUniq → TrEta → TrUnit → PowCart → PiZero := by
  intro hM hQO hQC hQI hQU hTE hTU hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hNum C
  haveI : IsNoetherianRing (Ow w) := inferInstance
  let N₀' : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  let β : Ow w →+* E := algebraMap (Ow w) E
  obtain ⟨j₀, hop, hcl, hj, φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ :=
    hM.cmp q (datAt S.atq S.sp) (Ow w) S.b E β gb S.mat.1 S.mat.2 S.N₀ S.std.three S.std.cop S.M (T.M N₀')
  let f₀ : (T.M N₀').X ⟶ S.M.X := j₀ ≫ pullback.fst _ _
  let n₀ : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N₀').univ S.M.univ f₀ 1 :=
    { φ := φA, φ₂ := φ₂, cart := hcart, sq := hsq, act := hact, pol := hpol,
      eta := fun y => by rw [one_smul]; exact heta y }
  let pw := GlobalTheory.KS.powMap f₀ n₀.φ n₀.cart.1.w k
  have pc := hPC _ _ _ (T.M N₀').univ.A S.M.univ.A S.M.univ.A f₀ (𝟙 _) n₀.φ (𝟙 _) n₀.cart.1.w (by simp) k
  have hs : f₀ ≫ S.M.s = (T.M N₀').s ≫ spMap β := by
    simp only [f₀, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hj]
  have hq : T.X.q (T.lev N₀') = (T.e N₀').hom ≫ (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom ≫ j₀ ≫ pullback.snd _ _ := by
    rw [hj, T.e_q]
  have e : ((T.e N₀').hom ≫ pw) ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s = T.X.q _ ≫ gen (Ow w) E := by
    rw [← T.e_q N₀']
    simp only [Category.assoc]
    rw [← Category.assoc pw, pc.2.1]
    simp only [Category.assoc]
    rw [hs]
  refine ⟨(T.e N₀').hom ≫ pw, e, ?_⟩
  haveI := hop
  haveI := hcl
  obtain ⟨h1, h2⟩ := pullback_lift_clopen_immersion j₀ (pullback.fst _ _) (pullback.snd _ _) S.M.s (spMap β)
    (IsPullback.of_hasPullback _ _) (GlobalTheory.KS.pow S.M.univ.A k).hom (GlobalTheory.KS.pow (T.M N₀').univ.A k).hom pw
    (pc.1 n₀.cart.1) (T.e N₀') _ rfl _ hq e
  refine ⟨h1, h2, fun x y => ?_⟩
  obtain ⟨π, o, ψ, φ, hw, hπs, htrans, htr⟩ := T.tr_eq N N₀' 1 x y
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans (one_mem _)
  have heta' : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ ψ = o.eta (1 • y') := fun y' =>
    hTE p D G L E gb 1 _ _ N N₀' (T.M N).univ o ψ htrans S.N₀ c 1 hNum.1 (_root_.mul_one _).symm y' y'
      ⟨0, zero_mem _, by simp⟩
  obtain ⟨n₁, hn₁⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ S.N₀ 1 _ _ _ (T.M N₀').s S.M.s S.M.s (T.M N₀').univ
    S.M.univ S.M.univ f₀ (𝟙 _)).2.2.2 _ (T.M N).s o π φ n₀
  obtain ⟨n₂, hn₂⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb S.N₀ N.1 S.N₀ 1 c _ _ (T.M N).s S.M.s (T.M N).univ o
    S.M.univ (π ≫ f₀) ψ hiso htrans.1 htrans.2.1 hlb heta' n₁
  obtain ⟨n₃, hn₃⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s S.Y.s S.M.s (T.M N).univ
    S.Y.univ S.M.univ C.j S.π).1 C.m S.mπ
  obtain ⟨o₀, ⟨n₄⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb β S.mat N.1 S.N₀ c hNum.1 (by have := N.2.1; omega)
    S.std.cop _ (T.M N).s (T.M N).univ
  obtain ⟨f', -, huniq⟩ := S.M.rep _ ((T.M N).s ≫ spMap β) o₀
  have key : ∀ (g : (T.M N).X ⟶ S.M.X), QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ g c →
      g ≫ S.M.s = (T.M N).s ≫ spMap β → g = f' := by
    intro g n hg
    have n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ (𝟙 _ ≫ g) c := by
      rw [Category.id_comp]; exact n
    obtain ⟨m, -⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c _ _ _ (T.M N).s _ S.M.s (T.M N).univ
      o₀ S.M.univ (𝟙 _) g).2.2.1 inferInstance n₄ n'
    exact huniq g ⟨hg, ⟨m⟩⟩
  have hf : C.j ≫ S.π = π ≫ f₀ := by
    rw [key _ n₃ ?_, key _ n₂ ?_]
    · rw [Category.assoc, hs, ← Category.assoc, hπs]
    · rw [Category.assoc, S.ov, C.ov]
  have cast : ∀ {f f' : (T.M N).X ⟶ S.M.X} (_ : f = f')
      (n : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f c),
      ∃ n' : QMap (D := datAt S.atq S.sp) (gb := gb) (T.M N).univ S.M.univ f' c, n'.φ = n.φ := by
    intro f f' hff n
    subst hff
    exact ⟨n, rfl⟩
  obtain ⟨n₅, hn₅⟩ := cast hf n₃
  have hφ : C.m.φ ≫ S.mπ.φ = (ψ.left ≫ φ.φ) ≫ n₀.φ := by
    rw [← hn₃, ← hn₅, hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N.1 S.N₀ c S.std.three S.std.cop _ _ (T.M N).s S.M.s
      (T.M N).univ S.M.univ (π ≫ f₀) n₅ n₂, hn₂, hn₁, Category.assoc]
  have hv1 : ((ψ.left ≫ φ.φ) ≫ n₀.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ π ≫ f₀ := by
    rw [Category.assoc, n₀.cart.1.w, ← Category.assoc, hw, Category.assoc]
  have hv2 : (C.m.φ ≫ S.mπ.φ) ≫ S.M.univ.A.hom = (T.M N).univ.A.hom ≫ C.j ≫ S.π := by
    rw [Category.assoc, S.mπ.cart.1.w, ← Category.assoc, C.m.cart.1.w, Category.assoc]
  have c1 := (hPC _ _ _ (T.M N).univ.A (T.M N₀').univ.A S.M.univ.A π f₀ (ψ.left ≫ φ.φ) n₀.φ hw n₀.cart.1.w k).2.2 hv1
  have c2 := (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.M.univ.A C.j S.π C.m.φ S.mπ.φ C.m.cart.1.w S.mπ.cart.1.w k).2.2 hv2
  change T.X.tr (T.lev N) (T.lev N₀') 1 x y ≫ (T.e N₀').hom ≫ pw =
    ((T.e N).hom ≫ GlobalTheory.KS.powMap C.j C.m.φ C.m.cart.1.w k) ≫ GlobalTheory.KS.powMap S.π S.mπ.φ S.mπ.cart.1.w k
  rw [← Category.assoc, htr, Category.assoc, Category.assoc, c1, c2]
  exact congrArg _ (powMap_congr hf.symm hφ.symm hv1 hv2 k)
end
end
