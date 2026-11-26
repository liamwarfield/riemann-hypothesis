module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem coeff_chi_smul {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A)
    (y : MonoidAlgebra A G) (i : ℕ) (hi : i ≤ n) :
    (D.chi (a • y)).coeff (n - i) = (-a) ^ i * D.lam i y := by
  have hsum : D.chi (a • y) = ∑ j ∈ Finset.range (n + 1), C (D.lam j y * (-a) ^ j) * X ^ (n - j) := by
    have h := AlgebraTools.Det.expand D y A[X] X (C (-a))
    rw [Polynomial.algebraMap_eq] at h
    unfold GDet.chi
    have harg : MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) (a • y) =
        MonoidAlgebra.single 1 X + C (-a) • (MonoidAlgebra.mapRingHom G C) y := by
      rw [map_neg, neg_smul, ← sub_eq_add_neg]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    rw [harg, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow]
    ring
  rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    ring
  · intro j hj hji
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    apply hji
    have := Finset.mem_range.mp hj
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem UpperTheory.V.Ws.H5.lamSmul :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A) (y : MonoidAlgebra A G) (i : ℕ), D.lam i (a • y) = a ^ min i n * D.lam i y := by
  intro n A G _ _ D a y i
  have hl : ∀ (z : MonoidAlgebra A G) (j : ℕ), D.lam j z = (-1) ^ j * (D.chi z).coeff (n - j) := by
    intro z j
    unfold GDet.lam
    rfl
  rcases le_or_gt i n with hi | hi
  · rw [hl, coeff_chi_smul D a y i hi, min_eq_left hi, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  · have hn : n - i = n - n := by omega
    have h1 := coeff_chi_smul D 1 y n le_rfl
    rw [one_smul] at h1
    rw [hl (a • y), hl y, hn, coeff_chi_smul D a y n le_rfl, h1, min_eq_right hi.le, neg_pow a n]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PrFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.H5.prFacts :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev), Topology.IsQuotientMap V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ ∀ H : Subgroup (G L Ω), H.Normal → IsClosed (H : Set (G L Ω)) → (∀ g g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ → g ∈ H → g' ∈ H) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := L) A ≤ H) → V.pr.ker ≤ H := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(phiKer V).2.1, ?_, ?_⟩
  · intro g
    have hin : s.c * resP L Ω g * s.c⁻¹ ∈ (resP L Ω).range := by
      rw [← V.hη]
      have h1 : V.η (toGS Ω V.S' (resP L Ω g)) = 1 := (V.hη _).mpr ⟨g, rfl⟩
      simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hin
    refine ⟨g', hg', ?_⟩
    have e1 : toGS Ω V.S' (s.c * resP L Ω g * s.c⁻¹) =
        toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      all_goals rfl
    apply Subtype.ext
    show toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ =
      ((V.pr g' : V.η.ker) : GS Ω V.S')
    rw [← e1, ← hg']
    all_goals rfl
  · intro H _ hcl _ hine
    apply (phiKer V).2.2 H hcl
    intro A v hAv hv
    apply hine A
    intro hlt
    apply hv
    apply V.sub
    have hmem := (hAv (l : 𝓞 (Lp L))).mp (by simpa using hlt)
    exact Or.inl (by simpa using hmem)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PairTw
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem pt_prod {R E : Type} [CommRing R] [Ring E] [Algebra R E] :
    ∀ (m : ℕ) (a b : Fin m → E), (∀ i, ∃ c : R, a i = c • b i) → ∃ c : R, (List.ofFn a).prod = c • (List.ofFn b).prod := by
  intro m
  induction m with
  | zero => intro a b _; exact ⟨1, by simp⟩
  | succ m ih =>
    intro a b h
    obtain ⟨c, hc⟩ := h 0
    obtain ⟨d, hd⟩ := ih (fun i => a i.succ) (fun i => b i.succ) fun i => h _
    refine ⟨c * d, ?_⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, hc, hd, smul_mul_smul_comm]

private theorem pt_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem pt_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (k : ℕ) : AdicCont I fun x => f x ^ k := fun N => by
  simp only [map_pow]
  exact (hf N).comp (· ^ k)

private theorem pt_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (γ : G →* Aˣ) (i : ℕ) (g : G) (a : A) :
    (twD D γ).lam i (MonoidAlgebra.single g a) = (γ g : A) ^ min i n * D.lam i (MonoidAlgebra.single g a) := by
  rw [lam_twD, twA_single, ← lamSmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_comm]
  rfl

private theorem pt_id {A G : Type} [CommRing A] [Group G] (γ : G →* Aˣ) (B : Type) [CommRing B] [Algebra A B]
    (h : ∀ g, algebraMap A B (γ g) = 1) (x : MonoidAlgebra B G) : twA γ B x = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => rw [twA_single, h, mul_one]

theorem UpperTheory.V.Ws.H5.pairTw :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) (γ : F.G₀ →* Rˣ), TwCh F γ → ∃ p' : Pair r R, p'.D = twD p.D γ ∧ ∀ v i, p'.ψ v i = p.ψ v i * γ.comp (F.φ v) := by
  intro l _ F O _ _ _ n r R _ _ _ p γ hγ
  have hres : ∀ g, res O R (γ g) = 1 := fun g => by
    have h := (res_eq_zero_iff O R _).mpr (hγ.red g)
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine ⟨
    { D := twD p.D γ
      ψ := fun v i => p.ψ v i * γ.comp (F.φ v)
      cont := fun i => ?_
      red := ?_
      psi := fun v i =>
        { cont := ?_
          red := fun g => ?_
          mu := fun g => ?_ }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pt_single]
    exact pt_mul (pt_pow hγ.cont _) (p.cont i)
  · rw [← p.red]
    refine GDet.ext fun B _ _ x => ?_
    letI : Algebra R B := ((algebraMap (ResidueField O) B).comp (res O R : R →+* ResidueField O)).toAlgebra
    change p.D.D B (twA γ B x) = p.D.D B x
    rw [pt_id γ B fun g => ?_]
    change algebraMap (ResidueField O) B (res O R (γ g)) = 1
    rw [hres, map_one]
  · exact pt_mul (p.psi v i).cont fun N => (hγ.cont N).comp_continuous (F.φ_cont v)
  · change res O R (p.ψ v i g * γ (F.φ v g)) = _
    rw [map_mul, hres, mul_one]
    exact (p.psi v i).red g
  · change (p.ψ v i g : R) * γ (F.φ v g) = _
    rw [hγ.mu v g g.2, Units.val_one, mul_one]
    exact (p.psi v i).mu g
  · have h1 : F.star O R n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op]
    have h2 : γ (F.conj g)⁻¹ = γ g := by
      rw [map_inv]; exact inv_eq_of_mul_eq_one_right (hγ.conj g)
    rw [pt_single, ← p.P, h1, pt_single, h2]
  · obtain ⟨c, hc⟩ : ∃ c : R, twA γ R (F.oEl v (fun i => p.ψ v i * γ.comp (F.φ v)) g) = c • F.oEl v (p.ψ v) g := by
      simp only [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def]
      refine pt_prod n _ _ fun i => ⟨γ (F.φ v (g i)), ?_⟩
      rw [map_sub, twA_single, twA_single, smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]
      simp [mul_comm]
    have h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1 := by
      rw [twA_single, MonoidAlgebra.smul_single]; simp
    rw [GDet.tr, lam_twD, map_mul, hc, h1, smul_mul_smul_comm, lamSmul]
    exact (congrArg _ (p.Ord v g h)).trans (mul_zero _)
  · have hg1 : γ g = 1 := hγ.iu u hg.1
    have h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1 := by
      rw [twA_single, MonoidAlgebra.smul_single]; simp
    have h2 : twA γ R (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
      rw [twA_single, hg1]; simp
    rw [GDet.tr, lam_twD, map_mul, map_sub, map_one, h1, h2, smul_mul_assoc, lamSmul]
    exact (congrArg _ (p.I u g hg h)).trans (mul_zero _)
end

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twMapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f₀ : B.B →ₐ[O] R) (γ : F.G₀ →* Rˣ), TwCh F γ → ∃ f : B.B →ₐ[O] R, TwMap B (f₀ : B.B →+* R) (f : B.B →+* R) γ := by
  intro l _ F O _ _ _ n r B R _ _ _ f₀ γ hγ
  obtain ⟨p, hp, hp'⟩ := exists_determinantPair_map_of_algHom l F O n r B.B R f₀ B.u
  obtain ⟨q, hq, hq'⟩ := pairTw p γ hγ
  obtain ⟨f, ⟨hf, hf'⟩, -⟩ := B.univ R q
  refine ⟨f, fun g i hi => ?_, fun v i g => ?_⟩
  · rw [← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f : B.B →+* R)).2.2.1, hf, hq, lam_twD, twA_single,
      ← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f₀ : B.B →+* R)).2.2.1, hp]
    have h : MonoidAlgebra.single g (1 * algebraMap R R (γ g)) =
        (γ g : R) • (MonoidAlgebra.single g 1 : MonoidAlgebra R F.G₀) := by simp
    rw [h, lamSmul, min_eq_left hi]
  · have h1 := congrArg (fun χ : F.Gv v →* Rˣ => (χ g : R)) ((hf' v i).trans (hq' v i))
    rw [← hp' v i] at h1
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapUniq
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twMapUniq :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f₀ : B.B →+* R) (γ : F.G₀ →* Rˣ) (f f' : B.B →ₐ[O] R), TwMap B f₀ (f : B.B →+* R) γ → TwMap B f₀ (f' : B.B →+* R) γ → f = f' := by
  intro l _ F O _ _ _ n r B R _ _ _ f₀ γ f f' hf hf'
  obtain ⟨p, hp⟩ := exists_determinantPair_map_of_algHom l F O n r B.B R f B.u
  have hs : ∀ (φ : B.B →+* R) (g : F.G₀), MonoidAlgebra.mapRingHom F.G₀ φ (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro φ g
    simp [MonoidAlgebra.mapRingHom]
  have hD : B.u.D.map (f' : B.B →+* R) = B.u.D.map (f : B.B →+* R) := by
    apply CA.d_gext
    intro g i _ hi
    have e1 := ((CA.d_gmap B.u.D).2.2.1 (f : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap B.u.D).2.2.1 (f' : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    rw [hs] at e1 e2
    rw [e1, e2, hf.1 g i hi, hf'.1 g i hi]
  have hψ : ∀ v i, pushCh (f' : B.B →+* R) (B.u.ψ v i) = pushCh (f : B.B →+* R) (B.u.ψ v i) := by
    intro v i
    ext g
    simp only [pushCh, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    exact (hf'.2 v i g).trans (hf.2 v i g).symm
  have hp' : B.u.Maps (f' : B.B →+* R) p.D p.ψ := by
    unfold Pair.Maps at hp ⊢
    exact ⟨hD.trans hp.1, fun v i => (hψ v i).trans (hp.2 v i)⟩
  obtain ⟨h, _, huniq⟩ := B.univ R p
  exact (huniq f hp).trans (huniq f' hp').symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Descend
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem not_lt_of_not_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ¬ A.valuation (l : Ω) < 1 := fun hl => hv ((h _).1 (by simpa using hl))

private theorem not_mem_of_norm {F : Type} [Field F] [NumberField F] {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l)
    {v : HeightOneSpectrum (𝓞 F)} (hn : normV v = p) : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hmem
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = p := hn
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  have h1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ p := hcard ▸ addOrderOf_dvd_natCard (1 : 𝓞 F ⧸ v.asIdeal)
  have h2 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ l := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_one]
    have h0 : Ideal.Quotient.mk v.asIdeal (l : 𝓞 F) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa using h0
  have hne1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ≠ 1 := by
    intro h
    have h3 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ 1 := by rw [h]
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, one_nsmul] at h3
    exact one_ne_zero h3
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact hne1 h
  · rw [h] at h2
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h2)

theorem UpperTheory.V.Ws.H5.descend :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h), ∃ β₀ : K.V.frame.G₀ →* c'.Oˣ, TwCh K.V.frame β₀ ∧ β₀.comp K.V.pr = K.β := by
  intro Ω _ _ _ l _ c D T c' h K
  obtain ⟨hq, hconj, hkerH⟩ := prFacts K.V
  have hsurj : Function.Surjective K.V.pr := hq.surjective
  have hker : K.V.pr.ker ≤ K.β.ker := by
    refine le_trans (hkerH K.t.ker inferInstance ?_ ?_ K.t_unr) K.β_t
    · exact isClosed_singleton.preimage K.t_cont
    · intro g g' hg hmem
      have h1 := (K.conj g g' hg).2.2
      rw [MonoidHom.mem_ker] at hmem ⊢
      rw [hmem, one_mul] at h1
      exact h1
  let β₀ := K.V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨K.β, hker⟩
  have hcomp : β₀.comp K.V.pr = K.β := MonoidHom.liftOfRightInverse_comp _ _ _ _
  have hβ₀ : ∀ g, β₀ (K.V.pr g) = K.β g := fun g => DFunLike.congr_fun hcomp g
  have hβt : ∀ g, K.t g = 1 → β₀ (K.V.pr g) = 1 := by
    intro g hg
    rw [hβ₀]
    exact K.β_t hg
  have hl : l.Prime := Fact.out
  refine ⟨β₀, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hcomp⟩
  · intro x
    obtain ⟨g, rfl⟩ := hsurj x
    obtain ⟨g', hg', hc⟩ := hconj g
    rw [hc]
    have e : β₀ (K.V.pr g') * β₀ (K.V.pr g) = 1 := by
      rw [hβ₀, hβ₀, mul_comm]
      exact (K.conj g g' hg').2.1
    exact e
  · intro u x hx
    obtain ⟨w, hw⟩ := u
    obtain ⟨g, hg, rfl⟩ := hx
    exact hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA w) (K.s.St_l w hw)) hg)
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA K.s.v0) (not_mem_of_norm hl K.s.p_prime K.s.p_ne K.s.norm_v0_eq_one)) hg)
  · intro v g hg
    exact hβt _ (K.mu v g hg).2
  · intro N s
    have hf : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) = (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((K.β g : c'.O))) := funext fun g => by rw [hβ₀]
    have ho : IsOpen (K.V.pr ⁻¹' ((fun x => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ x : c'.O))) ⁻¹' s)) := by
      show IsOpen ((fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) ⁻¹' s)
      rw [hf]
      exact K.β_cont N s
    exact hq.isOpen_preimage.mp ho
  · intro x
    obtain ⟨g, rfl⟩ := hsurj x
    have e : ((β₀ (K.V.pr g) : c'.O)) - 1 ∈ maximalIdeal c'.O := by
      rw [hβ₀, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, K.β_red, sub_self]
    exact e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PhiTw
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.H5.phiTw :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (β₀ : K.V.frame.G₀ →* c'.Oˣ), β₀.comp K.V.pr = K.β → ∀ (n : ℕ) (φ φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X 0 B φ → K.IsPhi X n B φ' → TwMap B (φ : B.B →+* X.B) (φ' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) (β₀ ^ n)) := by
  intro Ω _ _ _ l _ c D T c' h K X B β₀ hb n φ φ' hφ hφ'
  have hβ₀ : ∀ x, β₀ (K.V.pr x) = K.β x := fun x => DFunLike.congr_fun hb x
  rcases subsingleton_or_nontrivial X.B with hs | hs
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  haveI : Nontrivial X.A := ⟨⟨0, 1, fun h0 => zero_ne_one (X.inj (by simpa using h0))⟩⟩
  have hd : ∀ y, (X.cp y).natDegree = 4 := fun y => by
    rw [← natDegree_map_eq_of_injective X.inj, X.cp_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hsurj : Function.Surjective K.V.pr := (prFacts K.V).1.surjective
  have hp : ∀ x, ((W.pushCh (algebraMap c'.O X.B) (β₀ ^ n)) x : X.B) = (algebraMap c'.O X.B (β₀ x : c'.O)) ^ n := by
    intro x
    simp [W.pushCh]
  constructor
  · intro g i hi
    obtain ⟨x, rfl⟩ := hsurj g
    have e0 := hφ.1 x
    have e1 := hφ'.1 x
    simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one]
    rw [← coeff_map, ← coeff_map, e0, e1, coeff_scaleRoots, coeff_scaleRoots, hd, Nat.sub_sub_self hi]
    erw [hp, hβ₀]
    simp only [pow_zero, mul_one, map_mul, map_pow]
    ring
  · intro v i g
    obtain ⟨g, hg⟩ := g
    have e0 := hφ.2 v i ⟨g, hg⟩
    have e1 := hφ'.2 v i ⟨g, hg⟩
    erw [e0, e1, hp]
    have hv : β₀ (K.V.pr g) = K.β g := hβ₀ g
    erw [hv]
    simp only [pow_zero, mul_one, map_mul, map_pow]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LcOfKer
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LevelJ
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistOf
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.isTwistOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] (x x' : B.B →+* R) (γ : F.G₀ →* Rˣ), TwMap B x x' γ → (B.u.D.map x).IsTwist γ (B.u.D.map x') := by
  intro l _ F O _ _ _ n r B R _ x x' γ h
  have hmap (f : B.B →+* R) : ∀ i g, (B.u.D.map f).lam i (MonoidAlgebra.single g 1) =
      f (B.u.D.lam i (MonoidAlgebra.single g 1)) := by
    have hchi : ∀ y, (B.u.D.map f).chi (MonoidAlgebra.mapRingHom F.G₀ f y) = (B.u.D.chi y).map f := by
      intro y
      have he : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C (MonoidAlgebra.mapRingHom F.G₀ f y) =
          MonoidAlgebra.mapRingHom F.G₀ (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (B.u.D.map f).D R[X] _ = _
      rw [he]
      let : Algebra B.B R[X] := ((algebraMap R R[X]).comp f).toAlgebra
      have hc : ∀ a : B.B, Polynomial.mapRingHom f (algebraMap B.B B.B[X] a) = algebraMap B.B R[X] a := by
        intro a
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f
      exact B.u.D.nat B.B[X] R[X] { Polynomial.mapRingHom f with commutes' := hc } _
    have hm : ∀ i y, (B.u.D.map f).lam i (MonoidAlgebra.mapRingHom F.G₀ f y) = f (B.u.D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    intro i g
    simpa using hm i (MonoidAlgebra.single g 1)
  have e : B.u.D.map x' = twD (B.u.D.map x) γ := by
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ hi => ?_
    have s : MonoidAlgebra.single g ((1 : R) * algebraMap R R (γ g)) =
        (γ g : R) • MonoidAlgebra.single g (1 : R) := by
      simp
    rw [lam_twD, twA_single, s, lamSmul, min_eq_left hi, hmap x, hmap x']
    exact h.1 g i hi
  rw [e]
  exact isTwist_twD _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Fourier
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.fourier :
    ∀ (K Q : Type) [Field K] [IsAlgClosed K] [CharZero K] [CommGroup Q] [Finite Q] (a : MonoidAlgebra K Q), (∀ χ : Q →* Kˣ, MonoidAlgebra.lift K K Q ((Units.coeHom K).comp χ) a = 0) → a = 0 := by
  intro K Q _ _ _ _ _ a h
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent Q : ℕ) : K) := ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Q)⟩
  let ev : Q → ((Q →* Kˣ) →* K) := fun q =>
    { toFun := fun χ => (χ q : K), map_one' := by simp, map_mul' := fun x y => by simp }
  have hinj : Function.Injective ev := by
    intro q q' hq
    refine (CommGroup.forall_apply_eq_apply_iff Q (M := K)).1 fun φ => ?_
    exact Units.ext (DFunLike.congr_fun hq φ)
  have hli := (linearIndependent_monoidHom (Q →* Kˣ) K).comp ev hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun q => a.coeff q) (by
    funext χ
    have := h χ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [ev, Finset.sum_apply] using this)
  ext q
  simpa using key q
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem lift_map {A K Q : Type} [CommRing A] [CommRing K] [CommGroup Q] (x : A →+* K) (χ : Q →* K) :
    ∃ e : MonoidAlgebra A Q →+* K, (∀ a, e (algebraMap A _ a) = x a) ∧ (∀ z, e (MonoidAlgebra.single z 1) = χ z) ∧
      ∀ y, e y = MonoidAlgebra.lift K K Q χ (MonoidAlgebra.mapRingHom Q x y) := by
  refine ⟨(MonoidAlgebra.lift K K Q χ).toRingHom.comp (MonoidAlgebra.mapRingHom Q x), ?_, ?_, fun y => rfl⟩
  · intro a
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
  · intro z
    simp [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Ws.H5.levelJ :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), B.Dense J → B.TwistOk J → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∀ q : V.frame.G₀ →* Q, IsOpen (q.ker : Set V.frame.G₀) → Anti V.frame q → ∀ tw : B.B →ₐ[c.O] MonoidAlgebra B.B Q, TwMap B (algebraMap B.B (MonoidAlgebra B.B Q)) (tw : B.B →+* MonoidAlgebra B.B Q) ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) → ∀ b ∈ J, ∀ z : Q, (tw b).coeff z ∈ J := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B J hD hT Q _ _ hQ q hq hA tw htw b hb z
  let h0 : s.Wt n := fun _ j _ => (j : ℤ)
  have hinc : h0.Incr := by
    intro v τ a a' hlt
    show ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ)
    exact_mod_cast hlt
  refine hD h0 hinc _ ?_
  intro x hxJ hxG
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := l) (G := Q)).1 hQ
  have hzero : MonoidAlgebra.mapRingHom Q (x : B.B →+* Qbar l) (tw b) = 0 := by
    apply Ws.H5.fourier (Qbar l) Q
    intro χ
    obtain ⟨e, he1, he2, he3⟩ := lift_map (x : B.B →+* Qbar l) ((Units.coeHom (Qbar l)).comp χ)
    rw [← he3]
    let β : V.frame.G₀ →* (Qbar l)ˣ := χ.comp q
    let x' : B.Pt :=
      { toRingHom := e.comp (tw : B.B →+* MonoidAlgebra B.B Q)
        commutes' := by
          intro o
          show e (tw (algebraMap c.O B.B o)) = algebraMap c.O (Qbar l) o
          rw [tw.commutes, IsScalarTower.algebraMap_apply c.O B.B (MonoidAlgebra B.B Q), he1]
          exact x.commutes o }
    have hker : q.ker ≤ β.ker := by
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      show χ (q g) = 1
      rw [hg, map_one]
    have htw' : TwMap B (x : B.B →+* Qbar l) (x' : B.B →+* Qbar l) β := by
      have h2 := htw.comp e
      have ea : e.comp (algebraMap B.B (MonoidAlgebra B.B Q)) = (x : B.B →+* Qbar l) := by
        ext a
        exact he1 a
      have eb : pushCh e ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) = β := by
        ext g
        exact he2 (q g)
      rw [ea, eb] at h2
      exact h2
    have hx'J : J ≤ RingHom.ker (x' : B.B →+* Qbar l) := by
      refine hT x x' h0 β hxJ hxG (Subgroup.isOpen_mono hker hq) ⟨k, ?_⟩ ?_ ?_ ?_ ?_ ?_
      · ext g
        show (χ (q g) ^ l ^ k : (Qbar l)ˣ).1 = 1
        rw [← map_pow, ← hk, pow_card_eq_one', map_one]
        rfl
      · ext g
        show (χ (q (V.frame.conj g)) : Qbar l) = ((χ (q g))⁻¹ : (Qbar l)ˣ)
        rw [eq_inv_of_mul_eq_one_left (hA.conj g), map_inv]
      · intro u
        exact (hA.iu u).trans hker
      · exact hA.i0.trans hker
      · exact isTwistOf B _ _ β htw'
      · intro v j
        ext g
        show e (tw ((B.u.ψ v j g : (B.B)ˣ) : B.B)) = x ((B.u.ψ v j g : (B.B)ˣ) : B.B) * (χ (q (V.pr (g : G L Ω))) : Qbar l)
        refine (congrArg e (htw.2 v j g)).trans ?_
        rw [map_mul, he1]
        congr 1
        exact he2 _
    exact hx'J hb
  have := congrArg (fun y => y.coeff z) hzero
  simp only [MonoidAlgebra.mapRingHom_apply] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.SingleSubMem
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem comap_max {B Q : Type} [CommRing B] [IsLocalRing B] [CommGroup Q] [Finite Q]
    (M : Ideal (MonoidAlgebra B Q)) [M.IsMaximal] :
    M.comap (algebraMap B (MonoidAlgebra B Q)) = maximalIdeal B :=
  eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) M)

private theorem single_sub_mem {l : ℕ} (hl : l.Prime) {B Q : Type} [CommRing B] [IsLocalRing B]
    [CommGroup Q] [Finite Q] (hB : ((l : ℕ) : B) ∈ maximalIdeal B) (hQ : IsPGroup l Q)
    (M : Ideal (MonoidAlgebra B Q)) [hM : M.IsMaximal] (z : Q) :
    (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨k, hk⟩ := hQ z
  have hlM : ((l : ℕ) : MonoidAlgebra B Q) ∈ M := by
    have h1 : ((l : ℕ) : B) ∈ M.comap (algebraMap B (MonoidAlgebra B Q)) := by
      rw [comap_max M]
      exact hB
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1
  letI : Field (MonoidAlgebra B Q ⧸ M) := Ideal.Quotient.field M
  have hlK : ((l : ℕ) : MonoidAlgebra B Q ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hlM
  haveI : CharP (MonoidAlgebra B Q ⧸ M) l := by
    rcases hl.eq_one_or_self_of_dvd _ (ringChar.dvd hlK) with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · rw [← h1]
      exact ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : (Ideal.Quotient.mk M (MonoidAlgebra.single z 1 - 1)) ^ l ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
      ← MonoidAlgebra.one_def, map_one, sub_self]
  exact (pow_eq_zero_iff (pow_ne_zero k hl.ne_zero)).mp h0

private theorem sub_aug_mem {B Q : Type} [CommRing B] [CommGroup Q]
    (M : Ideal (MonoidAlgebra B Q))
    (h : ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M) (x : MonoidAlgebra B Q) :
    x - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 x) ∈ M := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact M.add_mem hx hy
  | single g b =>
    have e : MonoidAlgebra.single g b - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 (MonoidAlgebra.single g b)) =
        algebraMap B (MonoidAlgebra B Q) b * (MonoidAlgebra.single g 1 - 1) := by
      rw [MonoidAlgebra.lift_single]
      simp [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
    rw [e]
    exact M.mul_mem_left _ (h g)

theorem UpperTheory.V.Ws.H5.grpCO :
    ∀ (l : ℕ) [Fact l.Prime] (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B], ((l : ℕ) : B) ∈ maximalIdeal B → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∃ _ : IsCO O (MonoidAlgebra B Q), ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ maximalIdeal (MonoidAlgebra B Q) := by
  intro l _ O B _ _ _ _ _ hB Q _ _ hQ
  have hl : l.Prime := Fact.out
  let aug : MonoidAlgebra B Q →+* B := (MonoidAlgebra.lift B B Q 1).toRingHom
  let φ : MonoidAlgebra B Q →+* ResidueField B := (residue B).comp aug
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    refine ⟨algebraMap B _ b, ?_⟩
    simp [φ, aug]
  have hM0 := RingHom.ker_isMaximal_of_surjective φ hφ
  have hle : ∀ (M : Ideal (MonoidAlgebra B Q)), M.IsMaximal → RingHom.ker φ ≤ M := by
    intro M hM x hx
    have h1 : aug x ∈ maximalIdeal B := by
      rw [RingHom.mem_ker] at hx
      exact (residue_eq_zero_iff _).mp hx
    have h2 : algebraMap B _ (aug x) ∈ M := by
      have : aug x ∈ M.comap (algebraMap B _) := by
        rw [comap_max M]
        exact h1
      exact this
    have h3 : x - algebraMap B _ (aug x) ∈ M := sub_aug_mem M (single_sub_mem hl hB hQ M) x
    have := M.add_mem h3 h2
    rwa [sub_add_cancel] at this
  haveI : IsLocalRing (MonoidAlgebra B Q) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨RingHom.ker φ, hM0, fun M hM => ?_⟩
    exact (hM0.eq_of_le hM.ne_top (hle M hM)).symm
  have hres : ∀ x : MonoidAlgebra B Q, ∃ a : O, x - algebraMap O _ a ∈ maximalIdeal (MonoidAlgebra B Q) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (aug x)
    refine ⟨a, ?_⟩
    have h3 : x - algebraMap B _ (aug x) ∈ maximalIdeal (MonoidAlgebra B Q) :=
      sub_aug_mem _ (single_sub_mem hl hB hQ _) x
    have h4 : algebraMap B (MonoidAlgebra B Q) (aug x - algebraMap O B a) ∈ maximalIdeal (MonoidAlgebra B Q) := by
      have : aug x - algebraMap O B a ∈ (maximalIdeal (MonoidAlgebra B Q)).comap (algebraMap B _) := by
        rw [comap_max]
        exact ha
      exact this
    have := (maximalIdeal _).add_mem h3 h4
    rw [IsScalarTower.algebraMap_apply O B (MonoidAlgebra B Q)]
    rwa [map_sub, sub_add_sub_cancel] at this
  exact ⟨co_finite O B (MonoidAlgebra B Q) hres, fun z => single_sub_mem hl hB hQ _ z⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.FinQuot
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem pow_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (x : R)
    (hx : x - 1 ∈ I) (k : ℕ) : x ^ (l ^ k) - 1 ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h1 : x ^ (l ^ k) - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
    rw [pow_succ l k, pow_mul, ← mul_geom_sum, pow_succ I (k + 1)]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow (Ideal.Quotient.mk I) (x ^ (l ^ k)), h1, one_pow]
    simpa using hl

theorem UpperTheory.V.Ws.H5.finQuot :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R], ((l : ℕ) : R) ∈ maximalIdeal R → ∀ γ : F.G₀ →* Rˣ, TwCh F γ → ∀ N : ℕ, ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : F.G₀ →* Q) (j : Q →* (R ⧸ maximalIdeal R ^ N)ˣ), IsPGroup l Q ∧ IsOpen (q.ker : Set F.G₀) ∧ Anti F q ∧ j.comp q = pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ := by
  intro l _ F R _ _ hl γ hγ N
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  set χ := pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ with hχ
  have hval : ∀ g, (χ g : R ⧸ maximalIdeal R ^ N) = Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) := fun g => rfl
  have hlc : IsLocallyConstant fun g => (χ g : R ⧸ maximalIdeal R ^ N) := hγ.cont N
  have hlc' : IsLocallyConstant χ := IsLocallyConstant.desc χ Units.val hlc Units.val_injective
  have hfin : Finite χ.range := hlc'.range_finite.to_subtype
  refine ⟨χ.range, inferInstance, hfin, χ.rangeRestrict, χ.range.subtype, ?_, ?_, ?_, rfl⟩
  · rintro ⟨_, g, rfl⟩
    refine ⟨N, Subtype.ext (Units.ext ?_)⟩
    have h := Ideal.pow_le_pow_right (Nat.le_succ N) (pow_pow_sub_one_mem _ l hl _ (hγ.red g) N)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow] at h
    simpa [hval] using h
  · rw [MonoidHom.ker_rangeRestrict]
    exact hlc'.isOpen_fiber 1
  · refine hγ.toAnti.mono fun g hg => ?_
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hg
    exact Units.ext (by rw [hval, hg]; simp)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem lc_of_ker {G Q : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [Group Q]
    (q : G →* Q) (h : IsOpen (q.ker : Set G)) : IsLocallyConstant q := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' q.ker,
    h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have : q (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

private theorem lift_mem {B R Q : Type} [CommRing B] [CommRing R] [Algebra B R] [Monoid Q]
    (j : Q →* R) (J : Ideal B) (x : MonoidAlgebra B Q) (h : ∀ z, x.coeff z ∈ J) :
    MonoidAlgebra.lift B R Q j x ∈ J.map (algebraMap B R) := by
  rw [MonoidAlgebra.lift_apply]
  refine Ideal.sum_mem _ fun z _ => ?_
  beta_reduce
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h z))

theorem UpperTheory.V.Ws.H5.twJN :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), B.Dense J → B.TwistOk J → ((l : ℕ) : B.B) ∈ maximalIdeal B.B → ∀ γ : V.frame.G₀ →* B.Bˣ, TwCh V.frame γ → ∀ τ : B.B →ₐ[c.O] B.B, TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ → ∀ b ∈ J, ∀ N : ℕ, τ b ∈ J ⊔ maximalIdeal B.B ^ (N + 1) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B J hD hT hl γ hγ τ hτ b hb N
  obtain ⟨Q, _, _, q, j, hQ, hq, hA, hj⟩ := finQuot V.frame hl γ hγ (N + 1)
  obtain ⟨_, hz⟩ := grpCO l c.O B.B hl Q hQ
  have hΓ : TwCh V.frame ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) :=
    ⟨hA.mono fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one],
      fun M => (lc_of_ker q hq).comp fun z =>
        Ideal.Quotient.mk (maximalIdeal (MonoidAlgebra B.B Q) ^ M) (MonoidAlgebra.single z 1),
      fun g => hz (q g)⟩
  obtain ⟨tw, htw⟩ := twMapEx B (IsScalarTower.toAlgHom c.O B.B (MonoidAlgebra B.B Q)) _ hΓ
  have hJ := levelJ B J hD hT Q hQ q hq hA tw htw b hb
  haveI : Nontrivial (B.B ⧸ maximalIdeal B.B ^ (N + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (maximalIdeal.isMaximal B.B).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N)))
  haveI : IsCO c.O (B.B ⧸ maximalIdeal B.B ^ (N + 1)) :=
    co_quot c.O B.B _ (Ideal.Quotient.mkₐ c.O (maximalIdeal B.B ^ (N + 1))) (Ideal.Quotient.mkₐ_surjective c.O (maximalIdeal B.B ^ (N + 1)))
  let e : MonoidAlgebra B.B Q →ₐ[B.B] B.B ⧸ maximalIdeal B.B ^ (N + 1) :=
    MonoidAlgebra.lift B.B (B.B ⧸ maximalIdeal B.B ^ (N + 1)) Q ((Units.coeHom _).comp j)
  have h1 := htw.comp (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1))
  have h2 := hτ.comp (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1)))
  have e1 : (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1)).comp
      (IsScalarTower.toAlgHom c.O B.B (MonoidAlgebra B.B Q) : B.B →+* MonoidAlgebra B.B Q) =
      (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1))).comp (RingHom.id B.B) := RingHom.ext fun x => e.commutes x
  have e2 : pushCh (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1)) ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) =
      pushCh (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1))) γ := by
    rw [← hj]
    ext g
    exact MonoidAlgebra.lift_of (R := B.B) ((Units.coeHom _).comp j) (q g)
  rw [e1, e2] at h1
  have h3 := twMapUniq B _ _ ((e.restrictScalars c.O).comp tw) ((Ideal.Quotient.mkₐ c.O (maximalIdeal B.B ^ (N + 1))).comp τ) h1 h2
  have h4 : e (tw b) = Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1)) (τ b) := DFunLike.congr_fun h3 b
  have h5 := lift_mem ((Units.coeHom _).comp j) J (tw b) hJ
  rw [← Ideal.mem_quotient_iff_mem_sup, ← h4]
  exact h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwChOps
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twChOps :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R] (γ : F.G₀ →* Rˣ), TwCh F γ → (∀ m : ℕ, TwCh F (γ ^ m)) ∧ TwCh F γ⁻¹ ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (e : R →+* R'), IsLocalHom e → TwCh F (pushCh e γ) := by
  intro l _ F R _ _ γ hγ
  have hq : ∀ g, Ideal.Quotient.mk (maximalIdeal R) (γ g : R) = 1 := fun g => by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hγ.red g
  refine ⟨fun m => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, ⟨hγ.toAnti.mono ?_, ?_, ?_⟩,
    fun R' _ _ e he => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp (fun x => x ^ m)
    convert hc using 1
    funext g
    simp [Function.comp]
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    simp [hq g]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp Ring.inverse
    convert hc using 1
    funext g
    have hu : Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) =
        ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N) : R →* R ⧸ maximalIdeal R ^ N) (γ g) : _)) := rfl
    simp only [Function.comp_apply]
    rw [hu, Ring.inverse_unit, Units.coe_map_inv]
    rfl
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    have h2 := congrArg (Ideal.Quotient.mk (maximalIdeal R)) (γ g).inv_mul
    rw [map_mul, hq g, mul_one, map_one] at h2
    simpa using h2
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [pushCh, hg]
  · intro N
    have hle : maximalIdeal R ^ N ≤ Ideal.comap e (maximalIdeal R' ^ N) := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (fun x hx => Ideal.mem_comap.mpr (map_nonunit e x hx))) N
    have hc := (hγ.cont N).comp (Ideal.quotientMap _ e hle)
    convert hc using 1
    funext g
    simp [pushCh, Ideal.quotientMap_mk]
  · intro g
    have h3 := map_nonunit e _ (hγ.red g)
    simpa [pushCh] using h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.ClosedJ
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.closedJ :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (b : R), (∀ N : ℕ, b ∈ J ⊔ maximalIdeal R ^ (N + 1)) → b ∈ J := by
  intro R _ _ _ J b hb
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hx : Ideal.Quotient.mk J b ∈ (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | N
    · simp
    · obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.mp (hb N)
      have he : Ideal.Quotient.mk J (j + y) = y • (Ideal.Quotient.mk J 1 : R ⧸ J) := by
        rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, map_one, mul_one]
      rw [he]
      exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open UpperTheory.V.Ws.H5 in
theorem UpperTheory.V.Ws.h5 :
    UIn → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.Modular ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (n : ℕ) (φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ' → J₀.map φ' = J := by
  intro _ Ω _ _ _ l _ c D T _ _ c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ'
  subst hJ
  have hl : ((l : ℕ) : B.B) ∈ maximalIdeal B.B := by
    haveI := (UpperTheory.V.Base.dvrFacts l c'.O).2.2.1
    have h1 : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have h2 := map_nonunit (algebraMap c'.O B.B) _ (map_nonunit (algebraMap ℤ_[l] c'.O) _ h1)
    simpa using h2
  have stab : ∀ γ : K.V.frame.G₀ →* B.Bˣ, TwCh K.V.frame γ → ∃ τ : B.B →ₐ[c'.O] B.B,
      TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ ∧ ∀ b ∈ J₀, τ b ∈ J₀ := fun γ hγ => by
    obtain ⟨τ, hτ⟩ := twMapEx B (AlgHom.id c'.O B.B) γ hγ
    exact ⟨τ, hτ, fun b hb => closedJ _ J₀ _ (twJN B J₀ hM.dense hM.twist hl γ hγ τ hτ b hb)⟩
  have key : ∀ (γ : K.V.frame.G₀ →* c'.Oˣ), TwCh K.V.frame γ → ∀ f f' : B.B →ₐ[c'.O] X.B,
      TwMap B (f : B.B →+* X.B) (f' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) γ) → J₀.map f' ≤ J₀.map f := by
    intro γ hγ f f' hf
    obtain ⟨τ, hτ, hτJ⟩ := stab _ ((twChOps _ γ hγ).2.2 B.B (algebraMap c'.O B.B) inferInstance)
    have h1 := hτ.comp (f : B.B →+* X.B)
    have h2 : W.pushCh (f : B.B →+* X.B) (W.pushCh (algebraMap c'.O B.B) γ) = W.pushCh (algebraMap c'.O X.B) γ :=
      MonoidHom.ext fun g => Units.ext (f.commutes _)
    rw [h2, RingHom.comp_id] at h1
    have h3 : f' = f.comp τ := twMapUniq B _ _ f' (f.comp τ) hf h1
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h3]
    exact Ideal.mem_map_of_mem _ (hτJ b hb)
  obtain ⟨β₀, hβ, hβ'⟩ := descend K
  have hn := (twChOps _ β₀ hβ).1 n
  have hT := phiTw K X B β₀ hβ' n φ φ' hφ hφ'
  refine le_antisymm (key _ hn φ φ' hT) (key _ (twChOps _ _ hn).2.1 φ' φ ?_)
  have hu : ∀ g, algebraMap c'.O X.B (((β₀ ^ n)⁻¹ g : c'.Oˣ) : c'.O) * algebraMap c'.O X.B (((β₀ ^ n) g : c'.Oˣ) : c'.O) = 1 :=
    fun g => by rw [← map_mul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, map_one]
  refine ⟨fun g i hi => ?_, fun v i g => ?_⟩
  · rw [hT.1 g i hi, ← mul_assoc, ← mul_pow]
    erw [hu g]
    rw [one_pow, one_mul]
  · rw [hT.2 v i g, mul_assoc, mul_comm (_ : X.B) ((W.pushCh _ (β₀ ^ n)⁻¹ _ : X.Bˣ) : X.B)]
    erw [hu]
    rw [mul_one]
