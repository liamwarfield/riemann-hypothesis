module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponent
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.TotalMass

theorem count_sets (K : Type) [Field K] [NumberField K] (d : ℕ) : 1 ≤ d →
    ∃ T : Finset (Finset (Ideal (𝓞 K))), (T.card : ℝ) ≤ (d : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) ∧
      ∀ S : Finset (Ideal (𝓞 K)), (∀ P ∈ S, P.IsMaximal ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2) →
        ∏ P ∈ S, qIn P = d → S ∈ T := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd
  have hn : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL : 0 ≤ Real.logb 2 (Module.finrank ℚ K) := Real.logb_nonneg (by norm_num) hn
  rcases hd.eq_or_lt with rfl | hd
  · refine ⟨{∅}, by simp, fun S hS h1 => ?_⟩
    rw [Finset.mem_singleton, Finset.eq_empty_iff_forall_notMem]
    intro P hP
    have h2 := Finset.dvd_prod_of_mem (fun P => qIn P) hP
    rw [h1] at h2
    have := Nat.le_of_dvd one_pos h2
    have := (hS P hP).2.1
    omega
  · have hp : (Nat.minFac d).Prime := Nat.minFac_prime (by omega)
    obtain ⟨Ps, hcard, hPs⟩ := Formalism.SLP.P.CountO.primes_card K _ hp
    choose! T hT1 hT2 using ih
    have hlt : ∀ q : ℕ, 2 ≤ q → q ∣ d → d / q < d ∧ 1 ≤ d / q ∧ ((d / q : ℕ) : ℝ) ≤ d / 2 := by
      intro q h2 hq
      refine ⟨Nat.div_lt_self (by omega) h2, Nat.div_pos (Nat.le_of_dvd (by omega) hq) (by omega), ?_⟩
      refine Nat.cast_div_le.trans ?_
      gcongr
      exact_mod_cast h2
    refine ⟨(Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d).biUnion fun P => (T (d / qIn P)).image (insert P), ?_, ?_⟩
    · have h1 : (((Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d).biUnion
          fun P => (T (d / qIn P)).image (insert P)).card : ℝ) ≤
          ∑ P ∈ Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d, (((T (d / qIn P)).image (insert P)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      refine h1.trans ?_
      calc _ ≤ ∑ _P ∈ Ps.filter fun P => 2 ≤ qIn P ∧ qIn P ∣ d,
            ((d : ℝ) / 2) ^ Real.logb 2 (Module.finrank ℚ K) := by
            refine Finset.sum_le_sum fun P hP => ?_
            obtain ⟨-, h2, hq⟩ := Finset.mem_filter.1 hP
            obtain ⟨a, b, c⟩ := hlt _ h2 hq
            refine le_trans ?_ ((hT1 _ a b).trans (Real.rpow_le_rpow (by positivity) c hL))
            exact_mod_cast Finset.card_image_le
        _ ≤ (Module.finrank ℚ K : ℝ) * ((d : ℝ) / 2) ^ Real.logb 2 (Module.finrank ℚ K) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact (Finset.card_filter_le _ _).trans hcard
        _ = _ := by
            rw [Real.div_rpow (by positivity) (by norm_num),
              Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
            field_simp
    · intro S hS hprod
      have hdvd : Nat.minFac d ∣ ∏ P ∈ S, qIn P := hprod ▸ Nat.minFac_dvd d
      obtain ⟨P, hP, hpP⟩ := hp.prime.exists_mem_finset_dvd hdvd
      obtain ⟨hmax, h2, hN⟩ := hS P hP
      have hq : qIn P ∣ d := hprod ▸ Finset.dvd_prod_of_mem (fun P => qIn P) hP
      obtain ⟨a, b, -⟩ := hlt _ h2 hq
      have hmem : ((Nat.minFac d : ℕ) : 𝓞 K) ∈ P := by
        have hP0 : P ≠ ⊥ := by
          intro h0
          have : Ideal.absNorm P = 0 := by rw [h0, Ideal.absNorm_bot]
          rw [hN] at this
          have := pow_eq_zero_iff (two_ne_zero) |>.1 this
          omega
        have hdv : Nat.minFac d ∣ Ideal.absNorm P := hN ▸ hpP.trans (dvd_pow_self _ two_ne_zero)
        obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hdv
        rw [hmax.eq_of_le hQ.ne_top (Ideal.le_of_dvd hQP)]
        have : ((Nat.minFac d : ℕ) : ℤ) ∈ Q.under ℤ := hQu ▸ Ideal.mem_span_singleton_self _
        simpa using Ideal.mem_comap.1 this
      refine Finset.mem_biUnion.2 ⟨P, Finset.mem_filter.2 ⟨hPs P hmax hmem, h2, hq⟩,
        Finset.mem_image.2 ⟨S.erase P, ?_, Finset.insert_erase hP⟩⟩
      refine hT2 _ a b _ (fun Q hQ => hS Q (Finset.mem_of_mem_erase hQ)) ?_
      rw [← hprod, ← Finset.mul_prod_erase S _ hP, Nat.mul_div_cancel_left _ (by omega)]

theorem space_mass (hMM : MaxMass) (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (hj : 1 ≤ Module.finrank K V)
    (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (hs' : h'.IsSymm) (I : Submodule (𝓞 K) V')
    (hI : IsOrthoLattice h' I (Module.finrank K V)) (M₀ : Submodule (𝓞 K) V) (hM₀ : IsMaxLat h M₀)
    (n i : ℕ) (hi0 : i ≠ 0) (hnn : n = discN h M₀ * i ^ 2) :
    orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤
      ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) *
        (mass h' I * (discN h M₀ : ℝ) ^ ((Module.finrank K V : ℝ) / 2))) := by
  have hnd := SpaceMass.nondeg_of_PD h hp
  have hp' := SpaceMass.PD_of_ortho h' hK I _ hI
  have hnd' := SpaceMass.nondeg_of_PD h' hp'
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨c, hc⟩ := hMM K hK _ hj
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hcpos : 0 < c := hcI ▸ (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V' h' hK hs' hp' I hIfull).2.1
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  have hn'0 := (hdisc M₀ hM₀.1).1
  set n' := discN h M₀ with hn'
  have hm₀ : mass h M₀ ≤ c * (n' : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
    rw [hc V h hs hp rfl M₀ hM₀]
    exact mul_le_mul_of_nonneg_left (GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le K V h hK hs hnd hj M₀ hM₀).2 hcpos.le
  have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
    intro g M hM
    have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (SpaceMass.mem_genus_self h M hM.1.1)
    have h2 := (hdisc M hM.1).2.2.2.1 _ h1
    exact ⟨h2.1, h2.2.trans hM.2⟩
  let X : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
    {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
  have hXst : Stable (isom h) X := by
    rintro g p ⟨h1, h2, h3⟩
    exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
  have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
    (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
  have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
    (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) X := by
    rw [f1]
    refine mono _ _ _ _ subset_rfl fun M hM => ?_
    obtain ⟨M', hM', hle⟩ := hex M hM.1
    have hne : (X ∩ Prod.fst ⁻¹' {M}).Nonempty :=
      ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
    have := Set.one_le_encard_iff_nonempty.2 hne
    exact_mod_cast this
  have s2 : orbMass (isom h) X ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) +
      Real.logb 2 (Module.finrank ℚ K))) * orbMass (isom h) (genus h M₀) := by
    rw [f2, ← hconst]
    refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
    refine le_trans ?_ (GlobalTheory.T.encard_sublattices_of_index_le K V h hK hs hnd M' hM'.1.toIsLattice i (Nat.one_le_iff_ne_zero.2 hi0))
    have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
    have : (X ∩ Prod.snd ⁻¹' {M'}).encard ≤
        {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N = i}.encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        refine ⟨h3, ?_⟩
        have h5 := ((hdisc N h1.1).2.2.1 N' hM''.1 h3).2
        rw [h1.2, hM''.2, hnn] at h5
        have h6 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn'0) h5
        exact ((Nat.pow_left_injective (by norm_num)) h6).symm
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine s1.trans (s2.trans ?_)
  rw [← hmass, ← ENNReal.ofReal_mul (by positivity), hcI]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm₀ (by positivity))

theorem real_eq (d i j : ℕ) (L c : ℝ) (hd : d ≠ 0) (hi : i ≠ 0) :
    (i : ℝ) ^ ((j : ℝ) + L) * (c * ((d ^ 2 : ℕ) : ℝ) ^ ((j : ℝ) / 2)) =
      c * ((d * i : ℕ) : ℝ) ^ j * ((d * i : ℕ) : ℝ) ^ L / (d : ℝ) ^ L := by
  have hd' : (0 : ℝ) < d := by positivity
  have hi' : (0 : ℝ) < i := by positivity
  have e : ((d ^ 2 : ℕ) : ℝ) ^ ((j : ℝ) / 2) = (d : ℝ) ^ j := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd'.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hdL : (0 : ℝ) < (d : ℝ) ^ L := by positivity
  rw [e, Real.rpow_add hi', Real.rpow_natCast]
  push_cast
  rw [Real.mul_rpow hd'.le hi'.le]
  field_simp
  ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ de : ℕ, 1 ≤ de → ∃ s : Finset (Submodule K V), (∀ U ∈ s, Module.finrank K U = j) ∧ (∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U) ∧ ∑ U ∈ s, orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) ≤ ENNReal.ofReal (mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hL j hj V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ de hde
  obtain ⟨witt, res⟩ := GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp
  choose! T hT1 hT2 using count_sets K
  have hc : 0 < mass h₁ I₁ := by
    have hp' := SpaceMass.PD_of_ortho h₁ hK I₁ _ hI₁
    obtain ⟨-, -, ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V₁ h₁ hK hs₁ (SpaceMass.nondeg_of_PD h₁ hp')
    have hfull : Submodule.IsFullLattice K I₁ := by
      refine { toIsLattice := (ho' I₁ _ hI₁).1, span_eq_top := ?_ }
      obtain ⟨e, -, hspan, rfl, -⟩ := hI₁
      apply top_unique
      rw [← hspan]
      exact Submodule.span_mono Submodule.subset_span
    exact (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V₁ h₁ hK hs₁ hp' I₁ hfull).2.1
  set L : ℝ := Real.logb 2 (Module.finrank ℚ K) with hLdef
  have hLf : L = 1 + Real.logb 2 (fDeg K) := by
    have := hK.1
    have e : Module.finrank ℚ K = 2 * fDeg K := by
      rw [IsTotallyComplex.finrank, fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hf : (fDeg K : ℝ) ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := K)
      have : fDeg K ≠ 0 := by omega
      exact_mod_cast this
    rw [hLdef, e]
    push_cast
    rw [Real.logb_mul (by norm_num) hf, Real.logb_self_eq_one (by norm_num)]
  let Q : ℕ × Finset (Ideal (𝓞 K)) → Submodule K V → Prop := fun p U => Module.finrank K U = j ∧
    ∃ M : Submodule (𝓞 K) U, IsMaxLat (hRes h U) M ∧ badP (hRes h U) M = p.2 ∧
      discN (hRes h U) M = p.1 ^ 2 ∧ p.1 ∣ de
  let f : ℕ × Finset (Ideal (𝓞 K)) → Submodule K V := fun I => if hI : ∃ U, Q I U then hI.choose else ⊥
  have hf : ∀ I, (∃ U, Q I U) → Q I (f I) := fun I hI => by
    simp only [f, dif_pos hI]
    exact hI.choose_spec
  let A : Finset (ℕ × Finset (Ideal (𝓞 K))) :=
    ((Finset.Icc 1 de).sigma T).map ⟨fun x => (x.1, x.2), by
      rintro ⟨a, b⟩ ⟨c, d⟩ e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rfl⟩
  refine ⟨(A.filter fun I => ∃ U, Q I U).image f, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hU
    exact (hf I (Finset.mem_filter.1 hI).2).1
  · rintro U hU ⟨N, hN, hNn⟩
    obtain ⟨-, hsU, hpU, -⟩ := res U
    have hnU := FewOrbits.nondeg _ hpU
    obtain ⟨M, hM, hNM⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K U (hRes h U) hK hsU hnU).1 N hN
    obtain ⟨hbf, hdisc, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K U (hRes h U) hK hsU hnU M hM
    obtain ⟨hi0, hd⟩ := (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK hsU hnU N hN).2.2.1 M hM.1 hNM
    set S := hbf.toFinset with hS
    set d := ∏ P ∈ S, qIn P with hdd
    have hgood : ∀ P ∈ S, P.IsMaximal ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 := fun P hP =>
      have hP' := hbf.mem_toFinset.1 hP
      ⟨hP'.1, (hloc P hP').2.1, (hloc P hP').2.2.1⟩
    have hnorm : discN (hRes h U) M = d ^ 2 := by
      rw [hdisc, finprod_mem_eq_finite_toFinset_prod _ hbf, hdd, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun P hP => (hgood P hP).2.2
    have hdvd : d ∣ de := by
      rw [hNn, hnorm] at hd
      exact (Nat.pow_dvd_pow_iff two_ne_zero).1 (Dvd.intro _ hd.symm)
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hde
    have hQ : ∃ U, Q (d, S) U := ⟨U, hU, M, hM, by simp [hS], hnorm, hdvd⟩
    have hIS : (d, S) ∈ A.filter fun I => ∃ U, Q I U := by
      refine Finset.mem_filter.2 ⟨Finset.mem_map.2 ⟨⟨d, S⟩, Finset.mem_sigma.2
        ⟨Finset.mem_Icc.2 ⟨hd1, Nat.le_of_dvd hde hdvd⟩, hT2 d hd1 S hgood rfl⟩, rfl⟩, hQ⟩
    obtain ⟨hU0, M0, hM0, hI0, -⟩ := hf _ hQ
    refine ⟨f (d, S), Finset.mem_image_of_mem f hIS, ?_⟩
    generalize f (d, S) = U0 at hU0 M0 hM0 hI0
    obtain ⟨-, hsU0, hpU0, -⟩ := res U0
    have hbad : badP (hRes h U0) M0 = badP (hRes h U) M := by
      rw [hI0]; simp [hS]
    obtain ⟨e, he⟩ := GlobalTheory.T.definite_hermitian_isometric_of_same_bad_primes K U0 (hRes h U0) hK hsU0 hpU0 hL U (hRes h U) hsU hpU
      (hU0.trans hU.symm) M0 M hM0 hM hbad
    obtain ⟨g, hg, hge⟩ := witt U0 U e he
    refine ⟨⟨g, hg⟩, ?_⟩
    change gmap g U0 = U
    ext x
    simp only [gmap, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := hge ⟨y, hy⟩
      simp only at this
      change g y ∈ U
      rw [this]
      exact (e _).2
    · intro hx
      refine ⟨(e.symm ⟨x, hx⟩ : U0), (e.symm ⟨x, hx⟩).2, ?_⟩
      change g _ = x
      rw [hge]
      simp
  · set B : ℝ := mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ L with hB
    have hB0 : 0 ≤ B := by positivity
    have key : ∀ p ∈ A.filter fun I => ∃ U, Q I U,
        orbMass (isom (hRes h (f p))) (latsDisc (R := 𝓞 K) (hRes h (f p)) (de ^ 2)) ≤
          ENNReal.ofReal (B / (p.1 : ℝ) ^ L) := by
      intro p hp'
      obtain ⟨hU0, M0, hM0, -, hd, i, hi⟩ := hf _ (Finset.mem_filter.1 hp').2
      generalize f p = U0 at hU0 M0 hM0 hd
      obtain ⟨-, hsU0, hpU0, -⟩ := res U0
      have hi0 : i ≠ 0 := by rintro rfl; omega
      have hd0 : p.1 ≠ 0 := by intro h0; rw [h0] at hi; omega
      have := space_mass hMM K U0 (hRes h U0) hK hsU0 hpU0 (hU0 ▸ hj) V₁ h₁ hs₁ I₁ (hU0 ▸ hI₁) M0 hM0
        (de ^ 2) i hi0 (by rw [hd, hi]; ring)
      rw [hd, hU0, real_eq _ _ _ _ _ hd0 hi0, ← hi] at this
      exact this
    calc _ ≤ ∑ p ∈ A.filter fun I => ∃ U, Q I U,
          orbMass (isom (hRes h (f p))) (latsDisc (R := 𝓞 K) (hRes h (f p)) (de ^ 2)) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)
      _ ≤ ∑ p ∈ A.filter fun I => ∃ U, Q I U, ENNReal.ofReal (B / (p.1 : ℝ) ^ L) := Finset.sum_le_sum key
      _ ≤ ∑ p ∈ A, ENNReal.ofReal (B / (p.1 : ℝ) ^ L) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal (∑ p ∈ A, B / (p.1 : ℝ) ^ L) :=
          (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.sum_map, Finset.sum_sigma]
          calc _ ≤ ∑ _d ∈ Finset.Icc 1 de, B := by
                refine Finset.sum_le_sum fun d hd => ?_
                have hd1 := (Finset.mem_Icc.1 hd).1
                have hpos : (0 : ℝ) < (d : ℝ) ^ L := by
                  have : (0 : ℝ) < d := by exact_mod_cast hd1
                  positivity
                change ∑ _S ∈ T d, B / (d : ℝ) ^ L ≤ B
                rw [Finset.sum_const, nsmul_eq_mul]
                calc _ ≤ (d : ℝ) ^ L * (B / (d : ℝ) ^ L) :=
                      mul_le_mul_of_nonneg_right (hT1 d hd1) (by positivity)
                  _ = B := by field_simp
            _ = _ := by
                have : (0 : ℝ) < de := by exact_mod_cast hde
                rw [show 2 + Real.logb 2 (fDeg K) = 1 + L by rw [hLf]; ring, Real.rpow_add this,
                  Real.rpow_one, hB]
                simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
                ring

end GlobalTheory.Mass.TotalMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponentStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ de : ℕ, 1 ≤ de → ∃ s : Finset (Submodule K V), (∀ U ∈ s, Module.finrank K U = j) ∧ (∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U) ∧ ∑ U ∈ s, orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) ≤ ENNReal.ofReal (mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.TotalMass.main | exact GlobalTheory.Mass.TotalMass.main | (intros; apply GlobalTheory.Mass.TotalMass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedAlongLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedAlongLine
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineGlue

theorem sup_span_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (B : Submodule R W) {y z : W} (hyz : y - z ∈ B) :
    B ⊔ Submodule.span R {y} = B ⊔ Submodule.span R {z} := by
  have key : ∀ {y z : W}, y - z ∈ B → B ⊔ Submodule.span R {y} ≤ B ⊔ Submodule.span R {z} := by
    intro y z hyz
    refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    have := add_mem (Submodule.mem_sup_left hyz : y - z ∈ B ⊔ Submodule.span R {z})
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    simpa using this
  exact le_antisymm (key hyz) (key (by simpa using B.neg_mem hyz))

section Line

variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem exists_gen (h1 : Module.finrank K W = 1) {B C : Submodule (𝓞 K) W}
    (hB : Submodule.IsFullLattice K B) (hBC : B ≤ C) (hC : C.FG) :
    ∃ y, C = B ⊔ Submodule.span (𝓞 K) {y} := by
  letI : StarRing K := starRingOfComm
  obtain ⟨t, ht, e⟩ := (LatticeGens.gens_and_count K W B C hBC
    (DiscOrder.idxN_ne_zero hB hC)).1 hC
  rw [h1] at ht
  obtain ⟨y, hy⟩ := Finset.card_le_one_iff_subset_singleton.1 ht
  rcases Finset.subset_singleton_iff.1 hy with rfl | rfl
  · exact ⟨0, by simpa using e⟩
  · exact ⟨y, by simpa using e⟩

theorem encard_between (h1 : Module.finrank K W = 1) {B : Submodule (𝓞 K) W}
    (hB : Submodule.IsFullLattice K B) (T : 𝓞 K) (hT : T ≠ 0) :
    {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}.encard ≤
      ((Ideal.absNorm (Ideal.span {T}) : ℕ) : ℕ∞) := by
  set D : Submodule (𝓞 K) W := B.comap (LinearMap.lsmul (𝓞 K) W T) with hD
  have hTK : algebraMap (𝓞 K) K T ≠ 0 := by simpa using hT
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) W T) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : algebraMap (𝓞 K) K T • x = 0 := by rw [algebraMap_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left hTK
  have hDfg : D.FG :=
    Submodule.fg_of_fg_map_injective _ hinj (hB.fg.of_le (Submodule.map_comap_le _ _))
  obtain ⟨y, hy⟩ := exists_gen h1 hB (fun x hx => B.smul_mem T hx : B ≤ D) hDfg
  have hyD : T • y ∈ B := by
    have : y ∈ D := by
      rw [hy]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact this
  let Φ : (𝓞 K ⧸ Ideal.span {T}) → Submodule (𝓞 K) W := fun q =>
    B ⊔ Submodule.span (𝓞 K) {(Quotient.out q : 𝓞 K) • y}
  have hsub : {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B} ⊆ Φ '' Set.univ := by
    rintro C ⟨hBC, hC⟩
    have hCD : C ≤ D := hC
    obtain ⟨c, hc⟩ := exists_gen h1 hB hBC (hDfg.of_le hCD)
    have hcD : c ∈ B ⊔ Submodule.span (𝓞 K) {y} := by
      rw [← hy]
      apply hCD
      rw [hc]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hcD
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨Ideal.Quotient.mk _ r, trivial, ?_⟩
    rw [hc]
    apply sup_span_congr
    have : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) - r ∈ Ideal.span {T} := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 this
    have e : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) • y - (a + r • y) =
        k • (T • y) - a := by
      rw [smul_smul, hk, sub_smul]; abel
    rw [e]
    exact sub_mem (B.smul_mem k hyD) ha
  have hn : Ideal.absNorm (Ideal.span {T}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hT
  have hcard : Nat.card (𝓞 K ⧸ Ideal.span {T}) = Ideal.absNorm (Ideal.span {T}) :=
    (Ideal.absNorm_eq_natCard _).symm
  have : Finite (𝓞 K ⧸ Ideal.span {T}) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (𝓞 K ⧸ Ideal.span {T})).encard := Set.encard_image_le _ _
    _ = _ := by rw [Set.encard_univ, ENat.card_eq_coe_natCard, hcard]

end Line

theorem nondeg_of_pd {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpd : PD h) : h.Nondegenerate := by
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x h0
    simp [hx] at this
  exact ⟨fun x hx => ha x (hx x), fun x hx => ha x (hx x)⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B T hT h1 hA hB
  obtain ⟨hc, hsU, hpU, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 (perp h U)
  have hd0 : discN (hRes h U) A ≠ 0 :=
    (DiscOrder.main K U (hRes h U) hK hsU (nondeg_of_pd _ hpU) A hA).1
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (perp h U) (hRes h (perp h U)) hsW (nondeg_of_pd _ hpW)
    star_algebraMap_ringOfIntegers_mem_range
  have horth : ∀ (u : U) (w : perp h U), h (u : V) (w : V) = 0 :=
    fun u w => (Witt.mem_perp h U w).1 w.2 u u.2
  have hdec : ∀ v : V, ∃ (u : U) (w : perp h U), v = u + w := by
    intro v
    have hv : v ∈ U ⊔ perp h U := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 hv
    exact ⟨⟨u, hu⟩, ⟨w, hw⟩, e.symm⟩

  have hg : ∀ C : Submodule (𝓞 K) (perp h U), ∃ y : perp h U, B ≤ C → C.FG →
      C = B ⊔ Submodule.span (𝓞 K) {y} := by
    intro C
    by_cases hh : B ≤ C ∧ C.FG
    · obtain ⟨y, hy⟩ := exists_gen h1 hB.1 hh.1 hh.2
      exact ⟨y, fun _ _ => hy⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hh⟩
  choose g hg using hg
  set Ad : Submodule (𝓞 K) U := dual (hRes h U) A with hAd
  let M : Submodule (𝓞 K) V := A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
    B.map ((perp h U).subtype.restrictScalars (𝓞 K))
  let Φ : Submodule (𝓞 K) (perp h U) × (Ad ⧸ A.comap Ad.subtype) → Submodule (𝓞 K) V := fun p =>
    M ⊔ Submodule.span (𝓞 K) {(((Quotient.out p.2 : Ad) : U) : V) +
      (g (dual (hRes h (perp h U)) p.1) : V)}
  let S : Set (Submodule (𝓞 K) (perp h U)) := {C | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}
  have hsub : {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
      latIn U L = A ∧ latIn (perp h U) L = B} ⊆ Φ '' (S ×ˢ Set.univ) := by
    rintro L ⟨hL, hTL, hLA, hLB⟩
    have mA : ∀ u : U, u ∈ A ↔ (u : V) ∈ L := fun u => by rw [← hLA]; rfl
    have mB : ∀ w : perp h U, w ∈ B ↔ (w : V) ∈ L := fun w => by rw [← hLB]; rfl
    let π : V →ₗ[𝓞 K] perp h U :=
      (Submodule.projectionOnto (perp h U) U hc.symm).restrictScalars (𝓞 K)
    have hπ : ∀ (u : U) (w : perp h U), π ((u : V) + (w : V)) = w := by
      intro u w
      simp only [π, LinearMap.restrictScalars_apply, map_add (f := _)]
      rw [Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, zero_add]
    set B' := L.map π with hB'
    have mB' : ∀ w : perp h U, w ∈ B' ↔ ∃ u : U, (u : V) + (w : V) ∈ L := by
      intro w
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨u, w, rfl⟩ := hdec v
        exact ⟨u, by rw [hπ]; exact hv⟩
      · rintro ⟨u, hu⟩
        exact ⟨_, hu, hπ u w⟩
    have hBB' : B ≤ B' := fun w hw => (mB' w).2 ⟨0, by simpa using (mB w).1 hw⟩
    have hB'fg : B'.FG := hL.1.fg.map π
    have hB'l : Submodule.IsFullLattice K B' := by
      letI := hB.1
      exact Submodule.IsFullLattice.of_le_of_fg K hBB' hB'fg
    have mC : ∀ x : perp h U, x ∈ dual (hRes h (perp h U)) B' ↔ (x : V) ∈ dual h L := by
      intro x
      rw [dualBasic_mem_dual, dualBasic_mem_dual]
      constructor
      · intro H v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        have := H w ((mB' w).2 ⟨u, hv⟩)
        rw [map_add (f := _), LinearMap.add_apply, horth, zero_add]
        exact this
      · intro H w hw
        obtain ⟨u, hu⟩ := (mB' w).1 hw
        have := H _ hu
        rw [map_add (f := _), LinearMap.add_apply, horth, zero_add] at this
        exact this
    have hgen := hg B' hBB' hB'fg
    obtain ⟨a, ha⟩ := (mB' (g B')).1
      (hgen.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    have haA : a ∈ Ad := by
      rw [hAd, dualBasic_mem_dual]
      intro u hu
      have := hL.2 _ ((mA u).1 hu) _ ha
      rw [map_add (f := _), horth, add_zero] at this
      exact this
    refine ⟨(dual (hRes h (perp h U)) B', Submodule.Quotient.mk ⟨a, haA⟩), ⟨⟨?_, ?_⟩, trivial⟩, ?_⟩
    · intro w hw
      rw [mC, dualBasic_mem_dual]
      exact fun v hv => hL.2 v hv _ ((mB w).1 hw)
    · intro x hx
      rw [mB]
      exact hTL _ ((mC x).1 hx)
    · have hML : M ≤ L := by
        refine sup_le ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩; exact (mA u).1 hu
        · rintro _ ⟨u, hu, rfl⟩; exact (mB u).1 hu
      have e1 : L = M ⊔ Submodule.span (𝓞 K) {(a : V) + (g B' : V)} := by
        refine le_antisymm ?_ (sup_le hML ((Submodule.span_singleton_le_iff_mem _ _).2 ha))
        intro v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 (hgen.le ((mB' w).2 ⟨u, hv⟩))
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
        have e : (u : V) + ((b + r • g B' : perp h U) : V) =
            (((u - r • a : U) : V) + (b : V)) + r • ((a : V) + (g B' : V)) := by
          simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_add]
          abel
        have hu : u - r • a ∈ A := by
          rw [mA]
          have := sub_mem (sub_mem hv (L.smul_mem r ha)) ((mB b).1 hb)
          rw [e] at this
          simpa using this
        rw [e]
        exact add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ⟨_, hu, rfl⟩)
          (Submodule.mem_sup_right ⟨_, hb, rfl⟩)))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      simp only [Φ]
      rw [(dl B' hB'l).2.1, e1]
      apply sup_span_congr
      have hq : Quotient.out (Submodule.Quotient.mk ⟨a, haA⟩ : Ad ⧸ A.comap Ad.subtype) - ⟨a, haA⟩ ∈
          A.comap Ad.subtype := by
        rw [← Submodule.Quotient.eq]
        exact Submodule.Quotient.mk_out _
      rw [add_sub_add_right_eq_sub]
      exact Submodule.mem_sup_left ⟨_, hq, rfl⟩
  have hcard : Nat.card (Ad ⧸ A.comap Ad.subtype) = discN (hRes h U) A := rfl
  have : Finite (Ad ⧸ A.comap Ad.subtype) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' (S ×ˢ Set.univ)).encard := Set.encard_le_encard hsub
    _ ≤ (S ×ˢ (Set.univ : Set (Ad ⧸ A.comap Ad.subtype))).encard := Set.encard_image_le _ _
    _ = S.encard * (discN (hRes h U) A : ℕ) := by
      rw [Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_natCard, hcard]
    _ ≤ _ := by
      rw [Nat.cast_mul]
      gcongr
      exact encard_between h1 hB.1 T hT

end GlobalTheory.Mass.LineGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedAlongLineStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitianLattices_glued_along_line : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.LineGlue.main | exact GlobalTheory.Mass.LineGlue.main | (intros; apply GlobalTheory.Mass.LineGlue.main <;> assumption)
end
end

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanOne

open GlobalTheory.Mass.FixedSub GlobalTheory.Mass.PrimMean

theorem orbMass_stabilizer_le (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (U : Submodule K V) (n N₀ : ℕ) (T : 𝓞 K) (hT : T ≠ 0)
    (dW : Module.finrank K (perp h U) = 1) :
    orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
      (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
      (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} ≤
    orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) *
      (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) *
      ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h5, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ γ.1 • dual h L := dual_smul h γ.1 L ▸ hx
      change T • x ∈ γ.1 • L
      rw [smul_def'] at hx' ⊢
      unfold gmap at hx' ⊢
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨T • y, h5 y hy, map_smul _ _ _⟩
    · rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, -, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    obtain ⟨b1, -, -⟩ := (memB M').1 h2
    have cnt := GlobalTheory.T.card_hermitianLattices_glued_along_line K V h hK hs hp U M M' T hT dW h1.1 b1
    have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
        {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = M ∧
          latIn (perp h U) L = M'} :=
      fun N hN => ⟨hN.1.1, hN.1.2.2.2.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
    have e : discN (hRes h U) M = n := h1.2
    rw [e] at cnt
    have := ENat.toENNReal_le.2 ((Set.encard_le_encard sub).trans cnt)
    rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → j + 1 = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ 1 → ∀ (de t : ℕ) (T : 𝓞 K), 1 ≤ de → 1 ≤ t → T ≠ 0 → Ideal.absNorm (Ideal.span {T}) = t ^ 2 → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ x ∈ dual h L, T • x ∈ L) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (de : ℝ) ^ j * ((de : ℝ) ^ (4 + Real.logb 2 (fDeg K)) * (t : ℝ) ^ 2 * ((de : ℝ) * t) ^ (2 + Real.logb 2 (fDeg K)))) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j hj hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    de t T hde ht hT hN 𝒢 hst h𝒢
  obtain ⟨S, hdim, hcov, hsum⟩ := GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le hM K V h hK hs hp hLand j hj V₁ h₁ I₁ hs₁ hI₁ de hde
  have hnd := pd_nondeg h hp
  set l : ℝ := Real.logb 2 (fDeg K) with hl
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢
    (fun L => primSp h L j (de ^ 2))
    (fun g L U => (GlobalTheory.T.primitive_sublattices_move_with_isometries K V h hK hs hnd g L U j (de ^ 2)).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  have d0 : (0 : ℝ) < de := by exact_mod_cast hde
  have t0 : (0 : ℝ) < t := by exact_mod_cast ht
  set C : ℝ := mass h₂ I₂ * ((de : ℝ) * t) ^ (2 + l) * ((t : ℝ) ^ 2 * (de : ℝ) ^ 2) with hC
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)} ≤
      orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) * ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, -, -, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
    have dW : Module.finrank K (perp h U) = 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
        discN (hRes h U) (latIn U L) = de ^ 2}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2.1, (h𝒢 L hL.1).2.2.2, hL.2.2⟩)
      (fun _ _ => le_rfl)
    refine a1.trans ((orbMass_stabilizer_le K V h hK hs hp U (de ^ 2) (t ^ 2) T hT dW).trans ?_)
    have a3 := GlobalTheory.T.totalMass_integralLattices_bounded_det_line hM K (perp h U) (hRes h (perp h U)) hK (hRes_symm h hs _) (hRes_pd h hp _) dW
      V₂ h₂ I₂ hs₂ hI₂ (de * t) (Nat.mul_pos hde ht)
    rw [mul_pow, Nat.cast_mul] at a3
    rw [mul_assoc, hC, ENNReal.ofReal_mul (by positivity), hN]
    refine mul_le_mul' le_rfl (mul_le_mul' a3 (le_of_eq ?_))
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  refine (mul_le_mul' hsum le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e : (de : ℝ) ^ (4 + l) = (de : ℝ) ^ (2 + l) * (de : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add d0]
    congr 1
    push_cast
    ring
  rw [e, hC]
  ring

end GlobalTheory.Mass.PrimMeanOne
