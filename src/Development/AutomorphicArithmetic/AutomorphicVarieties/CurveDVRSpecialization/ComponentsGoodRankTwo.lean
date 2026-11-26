module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNicePrimeAboveOfLargeDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EnnrealVolumeRatioStepCancel

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ChainedBot
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ringKrullDim_quotient_eq_quotient_comap_of_surjective' {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Surjective p) (Q : Ideal B) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap p) := by
  have hs : Function.Surjective ((Ideal.Quotient.mk Q).comp p) :=
    Ideal.Quotient.mk_surjective.comp hp
  have hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs).symm,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hk)]

private theorem chained_bot_of_chained_ker_of_surjective {A B : Type} [CommRing A] [CommRing B] (p : A →+* B)
    (hp : Function.Surjective p) (D : ℕ) (h : Chained (RingHom.ker p) D) :
    Chained (⊥ : Ideal B) D := by
  have hmin : (RingHom.ker p).minimalPrimes = Ideal.comap p '' (⊥ : Ideal B).minimalPrimes := by
    rw [← Ideal.comap_minimalPrimes_eq_of_surjective hp]
    rfl
  have hc : ∀ Q ∈ (⊥ : Ideal B).minimalPrimes, Q.comap p ∈ (RingHom.ker p).minimalPrimes :=
    fun Q hQ => hmin ▸ ⟨Q, hQ, rfl⟩
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun Q hQ => ?_, fun P hP Q hQ => ?_⟩
  · rw [ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp]
    exact h1 _ (hc Q hQ)
  · have key := h2 _ (hc P hP) _ (hc Q hQ)
    rw [← Ideal.map_comap_of_surjective p hp P, ← Ideal.map_comap_of_surjective p hp Q]
    refine Relation.ReflTransGen.lift (Ideal.map p) (fun a b hab => ?_) _ _ key
    obtain ⟨ha, hb, hd⟩ := hab
    rw [hmin] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    show _ ∈ _ ∧ _ ∈ _ ∧ _
    rw [Ideal.map_comap_of_surjective p hp, Ideal.map_comap_of_surjective p hp]
    refine ⟨ha', hb', ?_⟩
    have hsup : (a' ⊔ b').comap p = a'.comap p ⊔ b'.comap p := by
      conv_lhs => rw [← Ideal.map_comap_of_surjective p hp a', ← Ideal.map_comap_of_surjective p hp b',
        ← Ideal.map_sup, Ideal.comap_map_of_surjective p hp]
      exact sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)
    rw [ringKrullDim_quotient_eq_quotient_comap_of_surjective' p hp, hsup]
    exact hd

theorem UpperTheory.V.Fr.sharp2 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 2, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → Chained (⊥ : Ideal L.R) (2 * F.d + 1) ∧ ∀ P ∈ minimalPrimes L.R, L.ρ.TI P := by
  intro l _ O _ _ _ _ F C₀ hok S x L hbig hx
  obtain ⟨N, N', p, f, hN, hs, hk⟩ := pres hok (Or.inl rfl) S x L
  haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete (l := l)
  haveI : IsCO L.O' (MvPowerSeries (Fin N) L.O') := co_mvps _ _ _
  have hdim := ((UpperTheory.V.CA.cl_cm).1 L.O' N).2
  have hch : Chained (Ideal.span (Set.range f)) (2 * F.d + 1) := by
    apply c1ch _ N' (2 * F.d + 1) f
    · rw [nilradical_eq_zero, Ideal.zero_eq_bot]
      exact Ideal.isPrime_bot
    · exact ⟨L.O', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
    · intro i
      have hi : f i ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨i, rfl⟩
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p) hi
    · rw [hdim]
      exact le_of_eq (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by omega))
  have h1 : Chained (⊥ : Ideal L.R) (2 * F.d + 1) := by
    refine chained_bot_of_chained_ker_of_surjective (p : MvPowerSeries (Fin N) L.O' →+* L.R) hs _ ?_
    rw [← hk] at hch
    exact hch
  refine ⟨h1, fun P hP => ?_⟩
  have hr := (loc_rho hok (Or.inl rfl) S x L).2.2.2 hx
  have hl := (krull_dim_lt_of_not_le_triangular hok (Or.inl rfl) S x L hbig hx).1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
  · rw [hr.1, top_le_iff]
    exact hPp.ne_top
  · intro hle
    have hge := h1.1 P hP
    have hmono : ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (L.R ⧸ L.ρ.triM) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    have hlt : ((2 * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) < ((2 * F.d : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt (hge.trans hmono) hl
    have : 2 * F.d + 1 + 1 < 2 * F.d := by exact_mod_cast hlt
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PreconnectedRankTwo
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem pol2 {Q : Type} [CommRing Q] (x y z : Q) :
    (!![z, 0; y, x] : Matrix (Fin 2) (Fin 2) Q) =
      Jmat (R := Q) 2 * (!![x, 0; y, z])ᵀ * Jmat (R := Q) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

private theorem ord2 {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 2) (Fin 2) Q) (ψ : Fin 2 → H → Q) (γ : Q)
    (h : ∀ s, r s = !![ψ 0 s, 0; (ψ 0 s - ψ 1 s) * γ, ψ 1 s]) (g : Fin 2 → H) : ordProd r ψ g = 0 := by
  have e : ∀ i : Fin 2, List.ofFn (fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin 2) (Fin 2) Q)) =
      [r (g 0) - ψ 0 (g 0) • 1, r (g 1) - ψ 1 (g 1) • 1] := fun _ => by
    simp [List.ofFn_succ]
  unfold ordProd
  rw [e 0, h, h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hom_ex {G Q : Type} [Group G] [CommRing Q] (p q : G →* Q) (a : G → Q) (a0 : a 1 = 0)
    (h : ∀ g g', a (g * g') = a g * p g' + q g * a g') :
    ∃ r : G →* Matrix (Fin 2) (Fin 2) Q, ∀ g, r g = !![p g, 0; a g, q g] := by
  refine ⟨{ toFun := fun g => !![p g, 0; a g, q g],
            map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · simp only [map_one, a0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro g g'
    simp only [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] <;> ring

private theorem isLocallyConstant_psi_restrict_of_isOpen_ker {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}
    (hΨ : IsOpen (F.Ψ.ker : Set F.Γ)) : IsLocallyConstant fun g : F.G0 => F.Ψ (g : F.Γ) := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro g
  have hK : IsOpen ((fun h : F.G0 => ((g⁻¹ * h : F.G0) : F.Γ)) ⁻¹' (F.Ψ.ker : Set F.Γ)) :=
    hΨ.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  convert hK using 1
  ext h
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  constructor
  · intro e
    rw [e, inv_mul_cancel]
  · intro e
    exact (inv_mul_eq_one.mp e).symm

private theorem rep_ex {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}
    (hF : F.Ok C₀) (Q : Type) [CommRing Q] [Algebra k Q] {a : F.G0 → Q} (ha : a ∈ F.strS Q) :
    ∃ ρ : NRep F 2 Q, ρ.IsBar (algebraMap k Q) ∧ ρ.triM = ⊥ ∧ (∀ i j, IsLocallyConstant fun g => ρ.r g i j) ∧
      ∀ g, ρ.r g 1 0 = a g := by
  classical
  obtain ⟨hlc, hmul, hstar, hloc⟩ := ha
  let φ : F.G0 →* kˣ := F.Ψ.comp F.del.ker.subtype
  let p : F.G0 →* Q := (algebraMap k Q).toMonoidHom.comp ((Units.coeHom k).comp φ)
  let q : F.G0 →* Q := (algebraMap k Q).toMonoidHom.comp ((Units.coeHom k).comp φ⁻¹)
  have hp : ∀ g, p g = algebraMap k Q (F.Ψ (g : F.Γ) : k) := fun g => rfl
  have hq : ∀ g, q g = algebraMap k Q ((F.Ψ (g : F.Γ))⁻¹ : kˣ) := fun g => rfl
  have hΨstar : ∀ g : F.G0, F.Ψ ((F.star g : F.G0) : F.Γ) = (F.Ψ (g : F.Γ))⁻¹ := by
    intro g
    simp only [Frame.star, Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply,
      map_mul, map_inv, Subgroup.coe_inv]
    rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have a0 : a 1 = 0 := by
    have h1 := hmul 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul, inv_one] at h1
    simpa using h1
  have hmul' : ∀ g g', a (g * g') = a g * p g' + q g * a g' := by
    intro g g'
    rw [hmul, hp, hq, Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap k Q _) (a g)]
  obtain ⟨r, hr⟩ := hom_ex p q a a0 hmul'
  let χ : (v : F.V) → F.Gv v →* Qˣ := fun v => (Units.map (algebraMap k Q).toMonoidHom).comp (F.Ψ.comp (F.loc v))
  have hpstar : ∀ g, p (F.star g) = q g := fun g => by rw [hp, hq, hΨstar]
  have hqstar : ∀ g, q (F.star g) = p g := fun g => by rw [hp, hq, hΨstar, inv_inv]
  let ρ : NRep F 2 Q :=
    { r := r
      ψ := fun v => ![χ v, (χ v)⁻¹]
      pol := by
        intro g
        rw [hr, hr, hpstar, hqstar, hstar]
        exact pol2 _ _ _
      diag := by
        intro i j hij
        rw [hr, hr]
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · simp
        · simp [hstar]
        · exact absurd rfl hij
      ord := by
        intro v g
        obtain ⟨γ, hγ⟩ := hloc v
        refine ord2 _ _ γ (fun s => ?_) g
        rw [hr, hγ]
        simp [χ, hp, hq, Algebra.smul_def, Frame.loc] }
  refine ⟨ρ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g i
    show r g i i = _
    rw [hr]
    fin_cases i <;> simp [w, hp, hq]
  · intro v i g
    fin_cases i <;> simp [ρ, χ, w]
  · apply Ideal.span_eq_bot.mpr
    rintro _ ⟨g, i, j, hij, rfl⟩
    show r g i j = 0
    rw [hr]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · have hl : IsLocallyConstant fun g : F.G0 => F.Ψ (g : F.Γ) := isLocallyConstant_psi_restrict_of_isOpen_ker hF.Ψ_open
    intro i j
    show IsLocallyConstant fun g => r g i j
    simp only [hr]
    fin_cases i <;> fin_cases j
    · exact hl.comp fun z => algebraMap k Q (z : k)
    · exact IsLocallyConstant.const _
    · exact hlc
    · exact hl.comp fun z => algebraMap k Q ((z⁻¹ : kˣ) : k)
  · intro g
    show r g 1 0 = a g
    rw [hr]
    simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 2)
include hF

private theorem pt_ex (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] {a : F.G0 → Q}
    (h : a ∈ F.strS Q) : ∃ ξ : S.A →+* Q, S.FPt ξ ∧ S.u.triM ≤ RingHom.ker ξ ∧ ∀ g, ξ (S.u.r g 1 0) = a g := by
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨ρ, hbar, htri, hlc, h10⟩ := rep_ex hF Q h
  obtain ⟨ξ, hξ, hmap⟩ := UpperTheory.smoothHom_weight_sum_neg hF (Or.inl rfl) S Q ρ hbar htri hlc
  refine ⟨ξ, hξ, ?_, fun g => ?_⟩
  · rw [NRep.triM, Ideal.span_le]
    rintro _ ⟨g, i, j, hij, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at hm
    rw [← hm, ← hmap, NRep.map_r]
  · rw [← h10, ← hmap, NRep.map_r]

private theorem pt_uniq {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {ξ ξ' : S.A →+* Q}
    (h : S.FPt ξ) (h' : S.FPt ξ') (t : S.u.triM ≤ RingHom.ker ξ) (t' : S.u.triM ≤ RingHom.ker ξ')
    (e : ∀ g, ξ' (S.u.r g 1 0) = ξ (S.u.r g 1 0)) : ξ' = ξ := by
  have H := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ h
  have H' := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ' h'
  refine H.2.2 ξ' h' (fun g i j => ?_)
  have z : ∀ {ζ : S.A →+* Q}, S.u.triM ≤ RingHom.ker ζ → ζ (S.u.r g 0 1) = 0 := fun hz =>
    RingHom.mem_ker.mp (hz (Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩))
  have d : ∀ i : Fin 2, ξ' (S.u.r g i i) = ξ (S.u.r g i i) := by
    intro i
    have d1 := H.1.1 g i
    have d2 := H'.1.1 g i
    rw [NRep.map_r] at d1 d2
    rw [d1, d2]
  fin_cases i <;> fin_cases j
  · exact d 0
  · exact (z t').trans (z t).symm
  · exact e g
  · exact d 1

private theorem pt_mem {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {ξ : S.A →+* Q}
    (h : S.FPt ξ) (t : S.u.triM ≤ RingHom.ker ξ) : (fun g => ξ (S.u.r g 1 0)) ∈ F.strS Q := by
  have H := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inl rfl) S Q ξ h
  haveI : CharP (ResidueField O) l := IsCoef.char
  have htri : (NRep.map ξ S.u).triM = ⊥ := by
    apply Ideal.span_eq_bot.mpr
    rintro _ ⟨g, i, j, hij, rfl⟩
    rw [NRep.map_r]
    exact RingHom.mem_ker.mp (t (Ideal.subset_span ⟨g, i, j, hij, rfl⟩))
  have h2 := framePoint_fiber_nonempty hF Q (NRep.map ξ S.u) H.1 htri H.2.1
  simpa only [NRep.map_r] using h2

private theorem line {K : Type} [Field K] [Algebra (ResidueField O) K] {A : F.G0 → Polynomial K}
    (h : A ∈ F.strS (Polynomial K)) :
    ∃ η : PrimeSpectrum S.A, S.mB ≤ S.π η.asIdeal ∧
      ∀ (c : K) (ξ : S.A →+* K), S.FPt ξ → S.u.triM ≤ RingHom.ker ξ →
        (∀ g, (A g).eval c = ξ (S.u.r g 1 0)) → η.asIdeal ≤ RingHom.ker ξ := by
  obtain ⟨ξA, hA, tA, vA⟩ := pt_ex hF S (Polynomial K) h
  refine ⟨⟨RingHom.ker ξA, RingHom.ker_isPrime ξA⟩, ?_, ?_⟩
  · exact Ideal.le_comap_map.trans (Ideal.comap_mono hA.x0)
  · intro c ξ hξ tξ vξ
    let φ : Polynomial K →ₐ[ResidueField O] K := (Polynomial.aeval c).restrictScalars (ResidueField O)
    have hφ : S.FPt ((φ : Polynomial K →+* K).comp ξA) := hA.comp φ
    have tφ : S.u.triM ≤ RingHom.ker ((φ : Polynomial K →+* K).comp ξA) := fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp (tA hx), map_zero]
    have heq : (φ : Polynomial K →+* K).comp ξA = ξ := pt_uniq hF S hξ hφ tξ tφ (fun g => by
      rw [RingHom.comp_apply, vA g, ← vξ g]
      simp [φ, Polynomial.coe_aeval_eq_eval])
    intro x hx
    rw [RingHom.mem_ker, ← heq, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

end

theorem UpperTheory.V.Fr.preconnected_rank_two :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 2, IsPreconnected S.BB := by
  intro l _ O _ _ _ _ F C₀ hF S
  classical
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨b, hb, hb0⟩ := UpperTheory.exists_mem_strS_ne_zero_of_frameOk hF
  obtain ⟨ξb, hbF, hbt, hbv⟩ := pt_ex hF S (ResidueField O) hb
  let qb : PrimeSpectrum S.A := ⟨RingHom.ker ξb, RingHom.ker_isPrime ξb⟩
  have hnz : ∃ g, b g ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb0 (funext hc)
  obtain ⟨g1, hg1⟩ := hnz
  have hqb : qb ∈ S.BB := by
    refine ⟨Ideal.le_comap_map.trans (Ideal.comap_mono hbF.x0), fun hle => hg1 ?_⟩
    have hm : S.u.r g1 1 0 ∈ S.u.triP := Ideal.subset_span ⟨g1, 1, 0, by decide, rfl⟩
    rw [← hbv g1]
    exact RingHom.mem_ker.mp (hle hm)
  refine isPreconnected_of_forall qb (fun p hp => ?_)
  obtain ⟨K, _, _, ξ, hker, hξ, tξ⟩ := UpperTheory.smoothDual_exact hF (Or.inl rfl) S p hp
  have ha := pt_mem hF S hξ tξ
  let bK : F.G0 → K := fun g => algebraMap (ResidueField O) K (b g)
  have hbK : bK ∈ F.strS K := F.strS_map (Algebra.linearMap (ResidueField O) K) hb
  let Lin : K →ₗ[ResidueField O] Polynomial K :=
    (Algebra.linearMap K (Polynomial K)).restrictScalars (ResidueField O)
  let A : F.G0 → Polynomial K := fun g =>
    (1 - Polynomial.X) * Lin (ξ (S.u.r g 1 0)) + Polynomial.X * Lin (bK g)
  have hAmem : A ∈ F.strS (Polynomial K) :=
    Submodule.add_mem _ (F.strS_mul _ (F.strS_map Lin ha)) (F.strS_mul _ (F.strS_map Lin hbK))
  obtain ⟨η, hηB, hη⟩ := line hF S hAmem
  have hη0 : η.asIdeal ≤ p.asIdeal := by
    rw [← hker]
    exact hη 0 ξ hξ tξ (fun g => by simp [A, Lin])
  let ι : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
  have tb' : S.u.triM ≤ RingHom.ker ((ι : ResidueField O →+* K).comp ξb) := fun x hx => by
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp (hbt hx), map_zero]
  have hη1 : η.asIdeal ≤ qb.asIdeal := by
    have h1 := hη 1 ((ι : ResidueField O →+* K).comp ξb) (hbF.comp ι) tb'
      (fun g => by simp [A, Lin, bK, hbv, ι])
    intro x hx
    have hx1 := h1 hx
    rw [RingHom.mem_ker, RingHom.comp_apply] at hx1
    exact RingHom.mem_ker.mpr ((ι : ResidueField O →+* K).injective (by rw [hx1, map_zero]))
  have hηBB : η ∈ S.BB := ⟨hηB, fun hle => hp.2 (hle.trans hη0)⟩
  refine ⟨{η, p, qb}, ?_, by simp, by simp, ?_⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hηBB
    · exact hp
    · exact hqb
  · refine (isPreconnected_singleton (x := η)).subset_closure (by simp) ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [← PrimeSpectrum.le_iff_mem_closure]
    rcases hz with rfl | rfl | rfl
    · exact le_rfl
    · exact hη0
    · exact hη1
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr UpperTheory.V.Pr

set_option linter.overlappingInstances false

noncomputable section

private theorem comp_min {A : Type} [CommRing A] {Y : Set (PrimeSpectrum A)}
    (hY : Y ∈ irreducibleComponents (PrimeSpectrum A)) : ∃ η ∈ minimalPrimes A, ∀ p, p ∈ Y ↔ η ≤ p.asIdeal := by
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hY
  obtain ⟨η, hη, rfl⟩ := hY
  exact ⟨η, hη, fun _ => Iff.rfl⟩

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ}

private def gd (S : Space O F 2) (M : Ideal S.B) : GlobData (PrimeSpectrum S.A) where
  TI := {p | S.u.TI p.asIdeal}
  Good := {p | M ≤ S.π p.asIdeal}
  Core := S.BB
  Cl := {p | p ∈ S.BB ∧ p.asIdeal.IsMaximal}
  EE := ∅

private def ld {S : Space O F 2} (M : Ideal S.B) {x : Ideal S.A} (L : S.Loc x) : LocData L.R where
  D1 := 2 * F.d + 1
  TI := {p | L.ρ.TI p.asIdeal}
  TE := ∅
  Good := {p | M ≤ L.π p.asIdeal}
  Nice := {p | Nice L.ρ p.asIdeal}
  Thick := ∅
  sharp := ⊥

private theorem ti_down {R : Type} [CommRing R] (ρ : NRep F 2 R) {P Q : Ideal R} (h : P ≤ Q) (hQ : ρ.TI Q) :
    ρ.TI P :=
  ⟨⟨fun a => hQ.1.1 (a.trans h), fun a => hQ.1.2 (a.trans h)⟩, fun a => absurd a (by decide)⟩

private theorem ld_ok (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 2} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) {x : Ideal S.A} (hx : ¬ S.u.triP ≤ x) (L : S.Loc x) : (ld M L).Ok := by
  obtain ⟨hc, ht⟩ := sharp2 hF S x L hB hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q h hP
    exact le_trans hP (Ideal.comap_mono (Ideal.comap_mono h))
  · intro P Q h hQ
    exact ti_down _ h hQ
  · intro p hp
    exact Or.inl ⟨hp.off, fun a => absurd a (by decide)⟩
  · intro I hI hd
    obtain ⟨p, hp, hle⟩ := exists_nice_prime_above_of_large_dim l O F C₀ 2 hF hB (Or.inl rfl) S x L hx M hM I.asIdeal hI hd
    exact ⟨⟨p, hp.prime⟩, hp, hle⟩
  · intro e he
    exact absurd he (Set.notMem_empty _)
  · intro P _ hP
    exact hP
  · intro P Q hP hQ
    have key : ∀ q : Ideal L.R, Relation.ReflTransGen
        (fun P Q => P ∈ (⊥ : Ideal L.R).minimalPrimes ∧ Q ∈ (⊥ : Ideal L.R).minimalPrimes ∧
          ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ (P ⊔ Q))) P.asIdeal q →
        ∀ Q : PrimeSpectrum L.R, Q.asIdeal = q → Relation.ReflTransGen (ld M L).Adj P Q := by
      intro q h
      induction h with
      | refl =>
        intro Q hQ
        rw [PrimeSpectrum.ext hQ]
      | @tail b c _ hbc ih =>
        intro Q hQ
        subst hQ
        exact (ih ⟨b, hbc.1.1.1⟩ rfl).tail hbc
    exact key _ (hc.2 _ hP _ hQ) Q rfl
  · intro P hP
    exact Or.inl (ht _ hP)
  · intro p hp hI hG P hP
    exact h1 x L p.asIdeal hp hI hG P.asIdeal P.2 hP
  · intro p _ he
    exact absurd he (Set.notMem_empty _)

private theorem ti_open (S : Space O F 2) (M : Ideal S.B) : IsOpen (gd S M).TI := by
  have : (gd S M).TI = (PrimeSpectrum.zeroLocus (S.u.triP : Set S.A))ᶜ ∩
      (PrimeSpectrum.zeroLocus (S.u.triM : Set S.A))ᶜ := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, fun a => absurd a (by decide)⟩⟩
  rw [this]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl.inter (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

private theorem good_closed (S : Space O F 2) (M : Ideal S.B) : IsClosed (gd S M).Good := by
  have : (gd S M).Good = PrimeSpectrum.zeroLocus (M.map (S.inc : S.B →+* S.A) : Set S.A) := by
    ext p
    exact Ideal.map_le_iff_le_comap.symm
  rw [this]
  exact PrimeSpectrum.isClosed_zeroLocus _

private theorem at_pt (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 2} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) {x : PrimeSpectrum S.A} (hx : ¬ S.u.triP ≤ x.asIdeal) (L : S.Loc x.asIdeal) :
    (∀ Y Y', (gd S M).CompI Y → (gd S M).CompI Y' → x ∈ Y → x ∈ Y' → Y ⊆ (gd S M).Good → Y' ⊆ (gd S M).Good) ∧
      (∃ Y, (gd S M).CompI Y ∧ x ∈ Y) ∧
      ((∃ I ∈ (ld M L).Good, I ∈ (ld M L).TI ∧ ((ld M L).D1 : WithBot ℕ∞) ≤ qdim I.asIdeal) →
        ∃ Y, (gd S M).CompI Y ∧ Y ⊆ (gd S M).Good) := by
  obtain ⟨hc, ht⟩ := sharp2 hF S x.asIdeal L hB hx
  letI : Algebra S.A L.R := (L.ι : S.A →+* L.R).toAlgebra
  haveI : Module.Flat S.A L.R := (loc_flat hF (Or.inl rfl) S x.asIdeal L).1
  have ch := chartOfFlat (PrimeSpectrum S.A) S.A id Topology.IsOpenEmbedding.id L.R
  have hpt : id (PrimeSpectrum.comap (algebraMap S.A L.R) (closedPoint L.R)) = x := PrimeSpectrum.ext L.lies
  rw [hpt] at ch
  have hr := (loc_rho hF (Or.inl rfl) S x.asIdeal L).2.2.1
  obtain ⟨a, b, c⟩ := globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ ch (ld M L) (by
    ext p
    exact and_congr (and_congr (hr p.asIdeal).1.not (hr p.asIdeal).2.1.not)
      (imp_congr Iff.rfl (hr p.asIdeal).2.2.not)) rfl (locProp _ _ (ld_ok hF hB hM h1 hx L))
  refine ⟨a fun P hP => le_trans ?_ (hc.1 P hP), b fun P hP => ht _ hP, c⟩
  exact Nat.cast_le.2 (Nat.le_succ _)

end

theorem UpperTheory.V.Pr.components_good_rank_two :
    UpperTheory.V.Pr.PropagationTheoremGL2 := by
  intro l _ O _ _ _ _ F C₀ hF hB S M hM h1 hS
  haveI : IsNoetherianRing S.A := (gr_A hF (Or.inl rfl) S).2.2.2.2.2.1
  have hok : (gd S M).Ok := by
    refine ⟨fun p hp => hp.1, preconnected_rank_two hF S, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro C hC ⟨p, hp, hp'⟩
      obtain ⟨x, ⟨⟨a, -⟩, b⟩, c⟩ := jac hF (Or.inl rfl) S C hC Set.univ isOpen_univ ⟨p, ⟨hp, trivial⟩, hp'⟩
      exact ⟨x, a, b, c⟩
    · intro p hp
      rw [mem_closure_iff]
      intro U hU hpU
      obtain ⟨x, ⟨⟨-, a⟩, b⟩, c⟩ := jac hF (Or.inl rfl) S Set.univ isClosed_univ U hU ⟨p, ⟨trivial, hpU⟩, hp⟩
      exact ⟨x, a, ⟨b, c⟩, Set.notMem_empty _⟩
    · rintro Y ⟨hY, p, hp, hpI⟩
      obtain ⟨η, hη, hi⟩ := comp_min hY
      obtain ⟨x, -, b, c⟩ := l41 hF (Or.inl rfl) S η hη.1.1 (min_hom hF (Or.inl rfl) S η hη)
        fun h => hpI.1.1 (h.trans ((hi p).1 hp))
      exact ⟨x, (hi x).2 c, b⟩
    · intro x hx
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1
      exact (at_pt hF hB hM h1 hx.1.2 L).1
    · rintro x ⟨hx, -⟩
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1
      exact (at_pt hF hB hM h1 hx.1.2 L).2.1
    · obtain ⟨ξ, Z, hξ, hI, hZ, hMZ, hZξ, hd⟩ := hS
      obtain ⟨x, hm, hx, H⟩ := seedpt hF (Or.inl rfl) S Z ξ hZ hξ hI hZξ
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hm hx.1
      obtain ⟨P, hP, hPI, hπ, hdim⟩ := H L
      refine (at_pt hF hB hM h1 hx.2 L).2.2 ⟨⟨P, hP⟩, hMZ.trans hπ.ge, hPI, ?_⟩
      show ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ P)
      rw [hdim, show ringKrullDim (S.B ⧸ Z) = _ from hd]
      exact_mod_cast (by omega : 2 * F.d + 1 ≤ 1 + 2 * F.d + 1)
  intro p hp hI
  exact globProp _ (gd S M) hok (a := ⟨p, hp⟩) hI
