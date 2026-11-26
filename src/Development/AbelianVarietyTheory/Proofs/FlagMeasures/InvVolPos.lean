module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianRepresents
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.WeightInf

theorem invVol_nn {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem invVol_pos' {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  have h1' := Nat.pos_of_ne_zero h1
  have h2' := Nat.pos_of_ne_zero h2
  positivity

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), (∀ (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → 0 < N.om Λ ∧ ∀ s ∈ N.R, N.om (s • Λ) = N.om Λ) ∧ ∀ (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), 0 ≤ omI F F' 𝔡 Λ ∧ (∀ N : NF H r, Adapt F F' 𝔡 N → omI F F' 𝔡 Λ ≤ N.om Λ) ∧ ∀ a c : ℝ, 0 ≤ c → (∃ N : NF H r, Adapt F F' 𝔡 N) → (∀ N : NF H r, Adapt F F' 𝔡 N → a ≤ c * N.om Λ) → a ≤ c * omI F F' 𝔡 Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r
  refine ⟨?_, ?_⟩
  · intro N g Λ hg hT
    have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
    have href := (GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT).2.2.2.2.1
    have hΛdata := ((isUnimod_iff H Λ).1 hT.1.1).1
    have hΛ : Submodule.IsFullLattice K Λ :=
      { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
    have hrefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
      refine { toIsLattice := href, span_eq_top := ?_ }
      obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
        GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
      have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
      have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        intro x hx
        have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
        obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        apply Submodule.mem_sup_right
        refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
        rw [hUp]
        exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      exact sup_le hW hP
    have h1 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hΛ hrefFull
    have h2 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ Λ hrefFull hΛ
    refine ⟨invVol_pos' _ _ h2.1 h1.1, fun s hs => ?_⟩
    have h3 := (GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hT s hs).2.1.1
    unfold NF.om
    rw [h3]
    exact h1.2 s hs
  · intro F F' 𝔡 Λ
    have hnn : ∀ x ∈ ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N}), (0 : ℝ) ≤ x := by
      rintro _ ⟨N, -, rfl⟩
      exact invVol_nn _ _
    refine ⟨Real.sInf_nonneg hnn, fun N hN => csInf_le ⟨0, hnn⟩ ⟨N, hN, rfl⟩, ?_⟩
    rintro a c hc ⟨N₀, hN₀⟩ h
    rcases hc.eq_or_lt with rfl | hc
    · simpa using h N₀ hN₀
    · rw [← div_le_iff₀' hc]
      refine le_csInf ⟨_, N₀, hN₀, rfl⟩ ?_
      rintro _ ⟨N, hN, rfl⟩
      rw [div_le_iff₀' hc]
      exact h N hN

end GlobalTheory.DegAsm.WeightInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem _root_.GlobalTheory.splitPrime_liesOver_span_iff {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by
  rw [Ideal.liesOver_iff]
  constructor
  · intro h
    have hmem : (p : ℤ) ∈ Ideal.under ℤ P := h ▸ Ideal.subset_span rfl
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  · intro h
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine hmax.eq_of_le (inferInstance : (Ideal.under ℤ P).IsPrime).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using h

theorem _root_.GlobalTheory.unramified_degree_one_of_ncard_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ)
    (hp : p.Prime) (h : (_root_.Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ _root_.Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
      v.asIdeal.inertiaDeg ℤ = 1 := by
  set q : Ideal ℤ := Ideal.span {(p : ℤ)} with hq
  haveI hqmax : q.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hqbot : q ≠ ⊥ := by
    rw [hq, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmemv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    unfold _root_.Formalism.BasicNotions.placesOver at hv
    exact hv
  haveI : v.asIdeal.LiesOver q := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp v.asIdeal).2 hmemv
  have hcard : (IsDedekindDomain.primesOverFinset q (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hqbot]
    have himage : (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) '' _root_.Formalism.BasicNotions.placesOver E p =
        q.primesOver (𝓞 E) := by
      ext P
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
          unfold _root_.Formalism.BasicNotions.placesOver at hw
          exact hw
        exact ⟨w.isPrime, (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp w.asIdeal).2 hw'⟩
      · rintro ⟨hPp, hPl⟩
        have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp P).1 hPl
        have hPbot : P ≠ ⊥ := by
          intro hb
          rw [hb, Ideal.mem_bot] at hPmem
          exact hp.ne_zero (by exact_mod_cast hPmem)
        refine ⟨⟨P, hPp, hPbot⟩, ?_, rfl⟩
        unfold _root_.Formalism.BasicNotions.placesOver
        exact hPmem
    rw [← himage, Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab)]
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := q) hqbot
  rw [← hcard, Finset.card_eq_sum_ones] at hsum
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset q (𝓞 E),
      1 ≤ q.ramificationIdx' P * q.inertiaDeg' P := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot] at hP
    obtain ⟨hPp, hPl⟩ := hP
    haveI := hPp
    haveI := hPl
    have he : q.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hqbot
    have hf : 0 < q.inertiaDeg' P := Ideal.inertiaDeg'_pos' q P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 hsum.symm
  have hvmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset q (𝓞 E) := by
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot]
    exact ⟨v.isPrime, inferInstance⟩
  obtain ⟨he, hf⟩ := mul_eq_one.1 (hall _ hvmem).symm
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  refine ⟨?_, ?_, ?_⟩
  · intro hsq
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ 2 := by
      rw [hq, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using hsq
    unfold Ideal.ramificationIdx' at he
    by_cases hb : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
    · have h2 := le_csSup hb (show 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
        from hle)
      omega
    · rw [Nat.sSup_of_not_bddAbove hb] at he
      exact zero_ne_one he
  · rw [← Ideal.ramificationIdx'_eq_ramificationIdx q v.asIdeal hqbot]
    exact he
  · rw [← Ideal.inertiaDeg'_eq_inertiaDeg q v.asIdeal]
    exact hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotien
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotien
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimPerp

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem equiv_of_gen {D M : Submodule (𝓞 K) V} {w : V} (hw : w ∈ D) (J : Ideal (𝓞 K))
    (h1 : ∀ a : 𝓞 K, a • w ∈ M ↔ a ∈ J) (h2 : ∀ y ∈ D, ∃ a : 𝓞 K, y - a • w ∈ M) :
    Nonempty ((↥D ⧸ M.comap D.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ J)) := by
  let φ : 𝓞 K →ₗ[𝓞 K] (↥D ⧸ M.comap D.subtype) :=
    (M.comap D.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton (𝓞 K) D ⟨w, hw⟩
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := (M.comap D.subtype).mkQ_surjective q
    obtain ⟨a, ha⟩ := h2 y y.2
    exact ⟨a, ((Submodule.Quotient.eq (M.comap D.subtype)).2 (show y - a • (⟨w, hw⟩ : D) ∈ M.comap D.subtype from ha)).symm⟩
  have hk : LinearMap.ker φ = J := by
    ext a
    rw [LinearMap.mem_ker, ← h1]
    exact Submodule.Quotient.mk_eq_zero _
  exact ⟨(φ.quotKerEquivOfSurjective hs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

theorem perp_prim (H : HermSpace K V) [_root_.NumberField.IsTotallyComplex K] {M : Submodule (𝓞 K) V} {S I W : Submodule K V}
    (hIS : I ≤ S) (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {z : V} {T : ℕ} (hT : 1 ≤ T) (hz : H.B z z = -(T : K))
    (hp : ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K))
    (hW : ∀ y, y ∈ W ↔ y ∈ S ∧ H.B y z = 0) :
    del H (M ⊓ rs (𝓞 K) W) = (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ∧
      GenBy (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) 1 ∧ IsLatMod (M ⊓ rs (𝓞 K) W) W I ∧
      Nonempty ((↥(dual H (M ⊓ rs (𝓞 K) W)) ⧸ (M ⊓ rs (𝓞 K) W).comap (dual H (M ⊓ rs (𝓞 K) W)).subtype) ≃ₗ[𝓞 K]
        (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) := by
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hT0 : (T : K) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hzM : z ∈ M := by simpa using (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
  have hzS : z ∈ S := b hzM
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have hint : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H M x).1 (hM.2.symm ▸ hx)).2
  set U : Submodule K V := Submodule.span K {z} ⊔ I with hU
  have hmU : ∀ u, u ∈ U ↔ ∃ t : K, ∃ i ∈ I, u = t • z + i := fun u => by
    rw [hU, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx, i, hi, rfl⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨t, i, hi, rfl⟩
    · rintro ⟨t, i, hi, rfl⟩
      exact ⟨_, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, i, hi, rfl⟩
  have hUS : U ≤ S := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hzS) hIS
  have hWU : S ⊓ perp H U = W := by
    ext y
    rw [hW, Submodule.mem_inf, mem_perp_iff]
    refine and_congr_right fun hy => ⟨fun h => h z ((hmU z).2 ⟨1, 0, I.zero_mem, by simp⟩), fun h x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx
    simp [h, o2 i hi y hy]
  have hWS : W ≤ S := fun y hy => ((hW y).1 hy).1
  have hIW : I ≤ W := fun i hi => (hW i).2 ⟨hIS hi, o1 i hi z hzS⟩
  obtain ⟨k1, k2⟩ := Compl.key H hIS hrad hM (le_sup_right : I ≤ U) hUS
  obtain ⟨k3, -⟩ := Compl.key H hIS hrad hM hIW hWS
  rw [hWU] at k1 k2
  rw [k2] at k3
  rw [← hU] at k1 k3
  have hzU : (T : K)⁻¹ • z ∈ U := (hmU _).2 ⟨_, 0, I.zero_mem, (add_zero _).symm⟩
  have hd : (T : K)⁻¹ • z ∈ dual H (M ⊓ rs (𝓞 K) U) := by
    rw [mem_dual_iff, Compl.span_inf (hM.1.2 ▸ hUS)]
    refine ⟨hzU, fun x hx => ?_⟩
    obtain ⟨t, i, hi, rfl⟩ := (hmU x).1 hx.2
    have ht : t • z ∈ M := by simpa using M.sub_mem hx.1 (a hi)
    have e : H.B ((T : K)⁻¹ • z) (t • z + i) = - star t := by
      simp [hz, o2 i hi z hzS]
      field_simp
      try rfl
    rw [e]
    exact Submodule.neg_mem _ (UnimodQuot.star_mem_one ((hp t).1 ht))
  rw [k1] at hd
  obtain ⟨m, hm, w, hw, e⟩ := Submodule.mem_sup.1 hd.2
  have hw' : w ∈ W := hw
  have hwD : w ∈ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact ⟨hw, Submodule.mem_sup.2 ⟨-m, M.neg_mem hm, _, hzU, by rw [← e]; abel⟩⟩
  have h1 : ∀ c : 𝓞 K, c • w ∈ M ⊓ rs (𝓞 K) W ↔ c ∈ Ideal.span {(T : 𝓞 K)} := by
    intro c
    have e1 : c • w = (algebraMap (𝓞 K) K c * (T : K)⁻¹) • z - c • m := by
      rw [mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [Submodule.mem_inf, and_iff_left (Submodule.smul_mem _ c hw), e1,
      M.sub_mem_iff_left (M.smul_mem c hm), hp, Submodule.mem_one, Ideal.mem_span_singleton']
    refine exists_congr fun d => ?_
    rw [eq_mul_inv_iff_mul_eq₀ hT0, ← map_natCast (algebraMap (𝓞 K) K), ← map_mul]
    exact (IsFractionRing.injective (𝓞 K) K).eq_iff
  have h2 : ∀ y ∈ dual H (M ⊓ rs (𝓞 K) W), ∃ c : 𝓞 K, y - c • w ∈ M ⊓ rs (𝓞 K) W := by
    intro y hy
    rw [k3] at hy
    obtain ⟨m', hm', u, hu, e'⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨t, i, hi, rfl⟩ := (hmU u).1 hu
    have h0 := ((hW y).1 hy.1).2
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hint m' hm' z hzM)
    rw [← e'] at h0
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hz, o1 i hi z hzS, smul_eq_mul, ← hc] at h0
    have ht : t = algebraMap (𝓞 K) K c * (T : K)⁻¹ := by
      field_simp
      linear_combination -h0
    refine ⟨c, ?_, Submodule.sub_mem _ hy.1 (Submodule.smul_mem _ c hw)⟩
    have : y - c • w = m' + c • m + i := by
      rw [← e', ht, mul_smul, algebraMap_smul, ← e, smul_add]; abel
    rw [this]
    exact M.add_mem (M.add_mem hm' (M.smul_mem c hm)) (a hi)
  have hle : M ⊓ rs (𝓞 K) W ≤ dual H (M ⊓ rs (𝓞 K) W) := by
    rw [k3]
    exact le_inf inf_le_right (inf_le_left.trans le_sup_left)
  obtain ⟨E⟩ := equiv_of_gen hwD _ h1 h2
  refine ⟨?_, ⟨{w}, by simp, ?_⟩, ⟨?_, Compl.span_inf (hM.1.2 ▸ hWS)⟩, ⟨E⟩⟩
  · have i1 : idx (M ⊓ rs (𝓞 K) W) (dual H (M ⊓ rs (𝓞 K) W)) = 1 := AddSubgroup.relIndex_eq_one.2 hle
    have i2 : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
      have : idx (dual H (M ⊓ rs (𝓞 K) W)) (M ⊓ rs (𝓞 K) W) = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) :=
        Nat.card_congr E.toEquiv
      rw [this, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    rw [del, gidx, i1, i2, mul_comm, pow_mul]
    simp
  · apply le_antisymm
    · intro y hy
      obtain ⟨c, hc⟩ := h2 y hy
      exact Submodule.mem_sup.2 ⟨_, hc, c • w, Submodule.smul_mem _ c (Submodule.subset_span (by simp)), by abel⟩
    · exact sup_le hle (Submodule.span_le.2 (by simpa using hwD))
  · obtain ⟨N, hN, rfl⟩ := hM.1.1
    refine ⟨N ⊓ rs (𝓞 K) W, hN.of_le inf_le_left, ?_⟩
    rw [sup_comm N, sup_inf_assoc_of_le N (show rs (𝓞 K) I ≤ rs (𝓞 K) W from hIW), sup_comm]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  haveI := hK.1
  obtain ⟨hNF, -, -, -, -, -, -, hww, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hL, hL', hp, hp', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  have hV := hNF.2.2.2.1
  have hc : N.c ≠ 0 := hNF.1.1
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hzS : N.F.z ∈ uPerp N.F N.F' := by
    have := (hp 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [one_smul] at this
    exact this.1
  have hXV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F' := le_sup_left
  have hW : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F.z = 0 := by
    intro y
    rw [wSp, uPerp, mem_perp_iff, mem_perp_iff]
    refine ⟨fun h => ⟨fun x hx => h x (hXV hx), h _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩,
      fun h x hx => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hv
    simp [hzz, h.1 u hu, h.2]
  have hW' : ∀ y, y ∈ wSp N.F N.F' ↔ y ∈ uPerp N.F N.F' ∧ H.B y N.F'.z = 0 := by
    intro y
    rw [hW, hzz]
    simp [hc]
  have hIX : II N.F N.F' ≤ N.F.X ⊔ N.F'.X := inf_le_left.trans le_sup_left
  have hIS : II N.F N.F' ≤ uPerp N.F N.F' := fun i hi =>
    (mem_perp_iff H _ i).2 fun x hx => (hV i (hXV (hIX hi))).2 hi x (hXV hx)
  have hrad : ∀ x ∈ uPerp N.F N.F', (∀ y ∈ uPerp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    intro x hx
    constructor
    · intro h
      have h1 : x ∈ N.F.X ⊔ N.F'.X := UnimodQuot.mem_of_perp_perp H _ fun y hy => by
        rw [← H.herm, h y hy, star_zero]
      exact (hV x (hXV h1)).1 ((mem_perp_iff H _ x).1 ((hW x).2 ⟨hx, h _ hzS⟩))
    · intro h y hy
      rw [← H.herm, (mem_perp_iff H _ y).1 hy x (hIX h), star_zero]
  obtain ⟨a1, a2, a3, a4⟩ := perp_prim H hIS hrad hL hT (N.hT ▸ N.F.zz) hp hW
  obtain ⟨b1, -, b3, -⟩ := perp_prim H hIS hrad hL' hT (N.hT' ▸ N.F'.zz) hp' hW'
  have e : flagPairDefinitePartLattice N.F' N.F Λ = latL N.F' N.F Λ ⊓ rs (𝓞 K) (wSp N.F N.F') := by rw [flagPairDefinitePartLattice, hww]
  rw [e]
  exact ⟨a1, b1, a2, a3, b3, a4⟩

end GlobalTheory.DegCnt.PrimPerp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotienStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → del H (flagPairDefinitePartLattice N.F N.F' Λ) = N.NT ∧ del H (flagPairDefinitePartLattice N.F' N.F Λ) = N.NT ∧ GenBy (dual H (flagPairDefinitePartLattice N.F N.F' Λ)) (flagPairDefinitePartLattice N.F N.F' Λ) 1 ∧ IsLatMod (flagPairDefinitePartLattice N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') ∧ IsLatMod (flagPairDefinitePartLattice N.F' N.F Λ) (wSp N.F N.F') (II N.F N.F') ∧ Nonempty ((↥(dual H (flagPairDefinitePartLattice N.F N.F' Λ)) ⧸ (flagPairDefinitePartLattice N.F N.F' Λ).comap (dual H (flagPairDefinitePartLattice N.F N.F' Λ)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(N.T : 𝓞 K)})) := by
  first | exact @GlobalTheory.DegCnt.PrimPerp.main | exact GlobalTheory.DegCnt.PrimPerp.main | (intros; apply GlobalTheory.DegCnt.PrimPerp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrEqvEquivalence
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameEqv
open AdaptInv
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem map_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) {x : V} (hx : x ∈ G.Xa k) : n x ∈ G'.Xa k := by
  have key : G.Xa k ≤ (G'.Xa k).comap (n : V →ₗ[K] V) := by
    show Submodule.span K _ ≤ _
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.val < k := hb
    have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
    have h2 : n (G.e b.castSucc) =
        (n (G.e b.castSucc) - G'.e b.castSucc) + G'.e b.castSucc := by abel
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [h2]
    exact (G'.Xa k).add_mem (xa_mono G' hb'.le h1) (e_mem_xa G' b hb')
  exact key hx

theorem symm_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) : ∀ x ∈ G'.Xa k, n.symm x ∈ G.Xa k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    have key : G'.Xa k ≤ (G.Xa k).comap (n.symm : V →ₗ[K] V) := by
      show Submodule.span K _ ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < k := hb
      have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
      have h2 := ih b.val hb' _ h1
      have e1 : n.symm (G'.e b.castSucc) =
          G.e b.castSucc - n.symm (n (G.e b.castSucc) - G'.e b.castSucc) := by
        rw [map_sub, LinearEquiv.symm_apply_apply, sub_sub_cancel]
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [e1]
      exact (G.Xa k).sub_mem (e_mem_xa G b hb') (xa_mono G hb'.le h2)
    exact key hx

theorem symm_gr {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (a : Fin (r + 1)) : n.symm (G'.e a) - G.e a ∈ G.Xa a.val := by
  have h1 := symm_xa h a.val _ (h a)
  have e1 : n.symm (G'.e a) - G.e a = -(n.symm (n (G.e a) - G'.e a)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
  rw [e1]
  exact (G.Xa a.val).neg_mem h1

theorem inN_gr {F : FlagD H r} {n : V ≃ₗ[K] V} (h : F.InN (n : V →ₗ[K] V)) (a : Fin (r + 1)) :
    n (F.e a) - F.e a ∈ F.Xa a.val := by
  induction a using Fin.lastCases with
  | last =>
    rw [Fin.val_last]
    exact h.2.2.2 _ F.zperp
  | cast b =>
    rw [Fin.coe_castSucc]
    exact h.2.2.1 b

theorem gr_comp {G G' M : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (hM : SameGr G M) (a : Fin (r + 1)) : n (M.e a) - G'.e a ∈ G'.Xa a.val := by
  have e1 : n (M.e a) - G'.e a = n (M.e a - G.e a) + (n (G.e a) - G'.e a) := by
    rw [map_sub]; abel
  rw [e1]
  exact (G'.Xa a.val).add_mem (map_xa h a.val (hM a)) (h a)
end

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem frEqv_equivalence (F : FlagD H r) (Λ : Submodule (𝓞 K) V) : Equivalence (FrEqv F Λ) := by
  refine ⟨fun G => ⟨1, GlobalTheory.UnipStab.inN_one, one_smul _ _, fun a => by simp⟩, ?_, ?_⟩
  · rintro G G' ⟨n, hn, hΛ, hG⟩
    refine ⟨n⁻¹, GlobalTheory.UnipStab.inN_inv hn, ?_, fun a => symm_gr hG a⟩
    conv_lhs => rw [← hΛ]
    exact inv_smul_smul n Λ
  · rintro G G' G'' ⟨n, hn, hΛ, hG⟩ ⟨m, hm, hΛ', hG'⟩
    refine ⟨m * n, GlobalTheory.UnipStab.inN_mul hm hn, by rw [mul_smul, hΛ, hΛ'], fun a => ?_⟩
    have e1 : (m * n) (G.e a) - G''.e a = m (n (G.e a) - G'.e a) + (m (G'.e a) - G''.e a) := by
      rw [LinearEquiv.mul_apply, map_sub]; abel
    rw [e1]
    exact (G''.Xa a.val).add_mem (map_xa hG' a.val (hG a)) (hG' a)

theorem move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G G' : FlagD H r} {𝔡 : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (h : FrEqv F Λ G G') (N : NF H r) (hN : Adapt F G 𝔡 N) :
    ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧
      ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  obtain ⟨n, hn, hΛ, hG⟩ := h
  have hiso : n ∈ isomGrp H := (mem_isomGrp H n).2 fun x y => hn.1 x y
  obtain ⟨N', he, -, -, -, hd, -, hrest⟩ := GlobalTheory.T.exists_hermFramePairNormalForm_moved_by_isometry K V H hK r N n hiso
  refine ⟨N', ⟨hd.trans hN.1, fun a => ?_, fun a => ?_⟩, ?_, fun g => ?_⟩
  · rw [(he a).1]
    have e1 : n (N.F.e a) - F.e a = n (N.F.e a - F.e a) + (n (F.e a) - F.e a) := by
      rw [map_sub]; abel
    rw [e1]
    exact (F.Xa a.val).add_mem (GlobalTheory.UnipStab.map_Xa hn a.val (hN.2.1 a)) (inN_gr hn a)
  · rw [(he a).2]
    exact gr_comp hG hN.2.2 a
  · have h1 := (hrest 0 Λ).1
    rwa [hΛ] at h1
  · have h1 := hrest g Λ
    rw [hΛ] at h1
    exact ⟨h1.2.1, h1.2.2⟩

end GlobalTheory.DegAsm.FrameEqv

namespace GlobalTheory.DegAsm
open FrameEqv

theorem frEqv_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), Equivalence (FrEqv F Λ) ∧ ∀ G G' : FlagD H r, FrEqv F Λ G G' → omI F G 𝔡 Λ = omI F G' 𝔡 Λ ∧ ∀ N : NF H r, Adapt F G 𝔡 N → ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧ ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r F 𝔡 Λ
  refine ⟨frEqv_equivalence F Λ, fun G G' h => ⟨?_, fun N hN => move hK h N hN⟩⟩
  have sub : ∀ {G G' : FlagD H r}, FrEqv F Λ G G' →
      (fun N : NF H r => N.om Λ) '' {N | Adapt F G 𝔡 N} ⊆
        (fun N : NF H r => N.om Λ) '' {N | Adapt F G' 𝔡 N} := by
    intro G G' h x hx
    obtain ⟨N, hN, rfl⟩ := hx
    obtain ⟨N', hN', hom, -⟩ := move hK h N hN
    exact ⟨N', hN', hom⟩
  unfold omI
  rw [Set.Subset.antisymm (sub h) (sub ((frEqv_equivalence F Λ).symm h))]

end GlobalTheory.DegAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotent
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Cmp (H : HermSpace K V) (p q : V × V) : Prop := H.B p.1 q.1 = H.B p.2 q.2

theorem Cmp.symm {p q : V × V} (h : Cmp H p q) : Cmp H q p := by
  unfold Cmp at *
  rw [← H.herm, h, H.herm]

theorem cmp_span_left {S : Set (V × V)} {q : V × V} (h : ∀ p ∈ S, Cmp H p q) :
    ∀ p ∈ Submodule.span K S, Cmp H p q := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [Cmp]
  | add x y _ _ h1 h2 => simp only [Cmp] at *; simp [h1, h2]
  | smul a x _ h1 => simp only [Cmp] at *; simp [h1]

theorem exists_isometry (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by
  have hG : ∀ p ∈ Submodule.span K S, ∀ q ∈ Submodule.span K S, Cmp H p q := fun p hp q hq =>
    cmp_span_left (fun p hp => (cmp_span_left (fun q hq => h q hq p hp) q hq).symm) p hp
  set G := Submodule.span K S with hGdef
  have s1 : ∀ v : V, ∃ p : G, p.1.1 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h1.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have s2 : ∀ v : V, ∃ p : G, p.1.2 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h2.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have b1 : Function.Bijective ((LinearMap.fst K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s1⟩
    have e1 : p.1.1 = 0 := hp
    refine Subtype.ext (Prod.ext e1 (H.nondeg _ fun y => ?_))
    obtain ⟨q, rfl⟩ := s2 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this.symm
  have b2 : Function.Bijective ((LinearMap.snd K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s2⟩
    have e1 : p.1.2 = 0 := hp
    refine Subtype.ext (Prod.ext (H.nondeg _ fun y => ?_) e1)
    obtain ⟨q, rfl⟩ := s1 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this
  have key : ∀ p : G, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) p.1.1 = p.1.2 := by
    intro p
    have : (LinearEquiv.ofBijective _ b1).symm p.1.1 = p := (LinearEquiv.symm_apply_eq _).2 rfl
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨_, fun x y => ?_, fun p hp => key ⟨p, Submodule.subset_span hp⟩⟩
  obtain ⟨p, rfl⟩ := s1 x
  obtain ⟨q, rfl⟩ := s1 y
  rw [key, key]
  exact Eq.symm (hG _ p.2 _ q.2)

theorem gram_eq {F G : FlagD H r} (hT : F.T = G.T) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = H.B (G.e a) (G.e b) := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [F.zz, G.zz, hT]
  · rw [B_swap0 H (F.zperp b), B_swap0 H (G.zperp b)]
  · rw [F.zperp, G.zperp]
  · rw [F.iso, G.iso]

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_left F F') (fun a => isotropicSpan_le_jointSpan_left _ _ (e_mem_X _ a)) a

theorem hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_right F F') (fun a => isotropicSpan_le_jointSpan_right _ _ (e_mem_X _ a)) a

theorem perp_transfer {F G : FlagD H r} (h : SameGr F G) {w : V} (hw : ∀ a, H.B (F.e a) w = 0) (a : Fin (r + 1)) :
    H.B (G.e a) w = 0 := by
  have h1 := perp_X F (fun b => hw b.castSucc) _ (Xa_le_X F _ (h a))
  simpa [hw a] using h1

variable [NumberField K]

theorem wt_e (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (flag_vector_mem_base_lattice _ _ a))

theorem wt_e' (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F'.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (hermFlag_secondFrame_mem_frameSpan _ _ a))

theorem wt_ist (N : NF H r) {w : V} (hw : w ∈ N.Wt) (b : Fin r) (hb : N.j ≤ b.val) : H.B (N.ist b) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

variable [FiniteDimensional K V]

theorem decomp (N : NF H r) {w : V} (hw : ∀ a, H.B (N.F.e a) w = 0) : ∃ w' ∈ N.Wt, w' - w ∈ N.F.X := by
  obtain ⟨x, hx, hp⟩ := (NFGeom.full N).2.2.2.2.2.2.2.1 w hw
  obtain ⟨u, hu, i, hi, e⟩ := Submodule.mem_sup.1 ((NFGeom.isLift N).2.2 _ hp)
  refine ⟨u, hu, ?_⟩
  have : u - w = -(x + i) := by rw [← sub_eq_zero, ← sub_eq_zero.2 e]; abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.add_mem _ hx hi.1)

theorem eq_top (N : NF H r) (M : Submodule K V) (h1 : ∀ a, N.F.e a ∈ M) (h2 : ∀ a, N.F'.e a ∈ M)
    (h3 : ∀ b : Fin r, N.j ≤ b.val → N.ist b ∈ M) (h4 : N.Wt ≤ M) : M = ⊤ := by
  rw [eq_top_iff, ← (NFGeom.isCompl N).sup_eq_top, NFGeom.Pi_eq]
  refine sup_le h4 (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) <;> refine Submodule.span_le.2 ?_
  · rintro _ ⟨b, -, rfl⟩; exact h1 _
  · rintro _ ⟨b, -, rfl⟩; exact h2 _
  · rintro _ (rfl | rfl)
    · exact h1 _
    · exact h2 _
  · rintro _ ⟨b, hb, rfl⟩; exact h3 b hb

theorem main (N₀ N₁ : NF H r) (h : SameGr N₀.F N₁.F) (hj : N₀.j = N₁.j) (hc : N₀.c = N₁.c) (hT : N₀.T = N₁.T)
    (hM : pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j) :
    ∃ s : V ≃ₗ[K] V, N₀.F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  have hX : N₁.F.X = N₀.F.X := AdaptInv.x_eq h
  have ee := gram_eq (F := N₀.F) (G := N₁.F) (by rw [N₀.hT, N₁.hT, hT])
  have e'e' := gram_eq (F := N₀.F') (G := N₁.F') (by rw [N₀.hT', N₁.hT', hT])
  have ee' : ∀ a b, H.B (N₀.F.e a) (N₀.F'.e b) = H.B (N₁.F.e a) (N₁.F'.e b) := by
    intro a b
    by_cases hb : N₀.j ≤ b.val
    · rw [N₀.same b hb, N₁.same b (hj ▸ hb)]
      simp [ee, hc]
    by_cases ha : N₀.j ≤ a.val
    · rw [NFGeom.e_eq N₀ a ha, NFGeom.e_eq N₁ a (hj ▸ ha)]
      simp [e'e', hc]
    have := congrFun (congrFun hM a) b
    simpa [pairM, ← hj, not_le.1 ha, not_le.1 hb] using this
  have ei : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F.e a) (N₀.ist b) = H.B (N₁.F.e a) (N₁.ist b) := by
    intro a b hb
    refine Fin.lastCases ?_ (fun a => ?_) a
    · exact (N₀.normalForm_dual_orthogonal_last b hb).trans (N₁.normalForm_dual_orthogonal_last b (hj ▸ hb)).symm
    · rw [N₀.ist_e a b hb, N₁.ist_e a b (hj ▸ hb)]
  have e'i : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F'.e a) (N₀.ist b) = H.B (N₁.F'.e a) (N₁.ist b) := by
    intro a b hb
    by_cases ha : N₀.j ≤ a.val
    · rw [N₀.same a ha, N₁.same a (hj ▸ ha)]
      simp [ei a b hb, hc]
    have hl : a.val < r := lt_of_lt_of_le (not_le.1 ha) N₀.j_le
    exact (N₀.ist_e' ⟨a.val, hl⟩ b (not_le.1 ha) hb).trans
      (N₁.ist_e' ⟨a.val, hl⟩ b (hj ▸ not_le.1 ha) (hj ▸ hb)).symm
  have ww : ∀ p q : V × V, p.1 ∈ N₀.Wt → q.1 ∈ N₀.Wt → p.2 - p.1 ∈ N₀.F.X → q.2 - q.1 ∈ N₀.F.X → Cmp H p q := by
    intro p q hp hq hp' hq'
    have a1 := perp_X N₀.F (fun b => wt_e N₀ hq b.castSucc) _ hp'
    have a2 := B_swap0 H (perp_X N₀.F (fun b => wt_e N₀ hp b.castSucc) _ hq')
    have a3 := X_iso N₀.F hp' hq'
    simp only [map_sub, LinearMap.sub_apply] at a1 a2 a3
    unfold Cmp
    linear_combination -a1 - a2 - a3
  obtain ⟨s, hs, hS⟩ := exists_isometry (H := H)
    {p | (∃ a, p = (N₀.F.e a, N₁.F.e a)) ∨ (∃ a, p = (N₀.F'.e a, N₁.F'.e a)) ∨
      (∃ b : Fin r, N₀.j ≤ b.val ∧ p = (N₀.ist b, N₁.ist b)) ∨ (p.1 ∈ N₀.Wt ∧ p.2 ∈ N₁.Wt ∧ p.2 - p.1 ∈ N₀.F.X)}
    (by
      rintro p (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨p0, p1, p2⟩) q (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨q0, q1, q2⟩)
      · exact ee a b
      · exact ee' a b
      · exact ei a b hb
      · exact (wt_e N₀ q0 a).trans (wt_e N₁ q1 a).symm
      · exact Cmp.symm (ee' b a)
      · exact e'e' a b
      · exact e'i a b hb
      · exact (wt_e' N₀ q0 a).trans (wt_e' N₁ q1 a).symm
      · exact Cmp.symm (ei b a ha)
      · exact Cmp.symm (e'i b a ha)
      · exact (N₀.ist_iso a b ha hb).trans (N₁.ist_iso a b (hj ▸ ha) (hj ▸ hb)).symm
      · exact (wt_ist N₀ q0 a ha).trans (wt_ist N₁ q1 a (hj ▸ ha)).symm
      · exact Cmp.symm ((wt_e N₀ p0 b).trans (wt_e N₁ p1 b).symm)
      · exact Cmp.symm ((wt_e' N₀ p0 b).trans (wt_e' N₁ p1 b).symm)
      · exact Cmp.symm ((wt_ist N₀ p0 b hb).trans (wt_ist N₁ p1 b (hj ▸ hb)).symm)
      · exact ww p q p0 q0 p2 q2)
    (by
      refine eq_top N₀ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      exact ⟨(w, u), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), rfl⟩)
    (by
      refine eq_top N₁ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hj ▸ hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₀ (perp_transfer (AdaptInv.sameGr_symm h) (wt_e N₁ hw))
      exact ⟨(u, w), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hu, hw, by
        simpa using Submodule.neg_mem _ hx⟩))), rfl⟩)
  have se : ∀ a, s (N₀.F.e a) = N₁.F.e a := fun a => hS (_, _) (Or.inl ⟨a, rfl⟩)
  refine ⟨s, ⟨hs, s.bijective, fun a => ?_, fun y hy => ?_⟩,
    fun a => ⟨se a, hS (_, _) (Or.inr (Or.inl ⟨a, rfl⟩))⟩⟩
  · rw [LinearEquiv.coe_coe, se]
    exact h a.castSucc
  · let M : Submodule K V := N₀.F.X.comap ((s : V →ₗ[K] V) - LinearMap.id)
    have m1 : ∀ a, N₀.F.e a ∈ M := fun a => by
      change s (N₀.F.e a) - N₀.F.e a ∈ N₀.F.X
      rw [se]
      exact Xa_le_X _ _ (h a)
    have m2 : N₀.F.X ≤ M := Submodule.span_le.2 (by rintro _ ⟨b, -, rfl⟩; exact m1 _)
    have m3 : N₀.Wt ≤ M := fun w hw => by
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      change s w - w ∈ N₀.F.X
      rw [show s w = u from hS (w, u) (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), ← hX]
      exact hx
    obtain ⟨u, hu, hx⟩ := decomp N₀ (w := y + star (H.B N₀.F.z y / N₀.F.T) • N₀.F.z) (fun a => by
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have := N₀.F.hT
        change H.B N₀.F.z _ = 0
        simp only [map_add (f := _), LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, pairing_lastVector_lastVector]
        field_simp
        ring
      · simp [hy a, pairing_isotropicSpan_lastVector N₀.F (e_mem_X _ a)])
    have m4 : y ∈ M := by
      have := M.sub_mem (M.sub_mem (m3 hu) (m2 hx))
        (M.smul_mem (star (H.B N₀.F.z y / N₀.F.T)) (m1 (Fin.last r)))
      simpa [FlagD.z] using this
    exact m4

end GlobalTheory.DegAsm.NFUnique

namespace GlobalTheory.DegAsm

theorem nf_unique : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  intro K V _ _ _ _ _ _ _ _ H _ r F N₀ N₁ h₀ h₁ hj hc hT hM
  have h : SameGr N₀.F N₁.F := fun a => by
    rw [AdaptInv.xa_eq h₀]
    simpa using Submodule.sub_mem _ (h₁ a) (h₀ a)
  obtain ⟨s, hs, he⟩ := NFUnique.main N₀ N₁ h hj hc hT hM
  exact ⟨s, AdaptInv.inN_of (AdaptInv.sameGr_symm h₀) _ hs, he⟩

end GlobalTheory.DegAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotentStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_unique_up_to_unipotent : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  first | exact @GlobalTheory.DegAsm.nf_unique | exact GlobalTheory.DegAsm.nf_unique | (intros; apply GlobalTheory.DegAsm.nf_unique <;> assumption)
end
end
