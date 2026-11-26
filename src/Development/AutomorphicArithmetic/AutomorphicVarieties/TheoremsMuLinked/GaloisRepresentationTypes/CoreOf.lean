module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CocField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.DetGCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FinDet
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Det.finDet :
    ∀ {K V S ι : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (f : S → ι → V →ₗ[K] K), ∃ T : Finset S, ∀ v : V, (∀ s ∈ T, ∀ i, f s i v = 0) → ∀ s i, f s i v = 0 := by
  intro K V S ι _ _ _ _ f
  classical
  let U : Finset S → Submodule K V := fun T => ⨅ s ∈ T, ⨅ i, LinearMap.ker (f s i)
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range U) ⟨U ∅, ∅, rfl⟩
  refine ⟨T, fun v hv s i => ?_⟩
  have hle : U (insert s T) ≤ U T := by
    intro w hw
    simp only [U, Submodule.mem_iInf, Finset.mem_insert] at hw ⊢
    intro t ht j
    exact hw t (Or.inr ht) j
  have heq : U (insert s T) = U T := by
    by_contra hne
    exact hT _ ⟨_, rfl⟩ (lt_of_le_of_ne hle hne)
  have hvT : v ∈ U T := by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hv
  rw [← heq] at hvT
  simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, Finset.mem_insert] at hvT
  exact hvT s (Or.inl rfl) i
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.EpsDec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Det.epsDec :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → (cycBar L Ω l).comp (Dec (F := L) A).subtype ≠ 1 := by
  intro l _ L Ω _ _ _ _ _ A w hw hl heq
  have hinj := UpperTheory.V.Ws.Eb.psiInj A w hw hl (n := 2)
    (![(cycBar L Ω l).comp (Dec (F := L) A).subtype, 1]) ![1, 0] 1
    (by decide) one_pos (by
      intro i g _
      fin_cases i <;> simp)
  have h01 := hinj (a₁ := 0) (a₂ := 1) (by simp [heq])
  exact absurd h01 (by decide)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesMatrixRepresentationOfPhiCond
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesColRepOfPhiCond
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.ContinuousCocyclesFgIntegralOfPhiCond
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Submodule.mem_top, hy⟩

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      simpa using J.mul_mem_right (n i) hr
    · intro a b ha hb i
      simpa using J.add_mem (ha i) (hb i)
  · intro hx
    have hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin r → R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem lc_iff {R G : Type} [CommRing R] [TopologicalSpace G] (J : Ideal R) {r : ℕ} (f : G → Fin r → R) :
    (IsLocallyConstant fun g => (J • (⊤ : Submodule R (Fin r → R))).mkQ (f g)) ↔
      ∀ i, IsLocallyConstant fun g => Ideal.Quotient.mk J (f g i) := by
  have key : ∀ a b : Fin r → R, (J • (⊤ : Submodule R (Fin r → R))).mkQ a = (J • (⊤ : Submodule R (Fin r → R))).mkQ b ↔
      ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro a b
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_pi]
    rfl
  simp only [IsLocallyConstant.iff_eventually_eq, key]
  constructor
  · intro h i x
    exact (h x).mono fun y hy => hy i
  · intro h x
    exact Filter.eventually_all.mpr fun i => h i x

private theorem cocycles_finitely_generated (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (t : R) (I : Ideal R) (hI : I = Ideal.span {t}) (ht0 : t ≠ 0) (hIne : I ≠ ⊤) [IsPrecomplete I R]
    (hfq : Finite (R ⧸ I)) (hlI : (l : R) ∈ I)
    (ρ : G →* Module.End R M) (Z : Submodule R (G → M)) (hΦ : PhiCond G l)
    (hρ : ∀ (N : ℕ) m, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (ρ g m))
    (hZ : ∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
      ∀ g h, z (g * h) = z g + ρ g (z h)) : Z.FG := by
  subst hI
  have htinj : ∀ x : M, t • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis R M
    apply b.repr.injective
    ext i
    have h := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    simpa using (mul_eq_zero.mp h).resolve_left ht0
  have hcancel : ∀ a b : M, t • a = t • b → a = b := fun a b h =>
    sub_eq_zero.mp (htinj _ (by rw [smul_sub, h, sub_self]))
  have hMh : ∀ x : M, (∀ n : ℕ, ∃ y, t ^ n • y = x) → x = 0 := by
    intro x hx
    have hle : Ideal.span {t} ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hIne
    have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) _ (by simpa only [Ideal.jacobson_bot] using hle)
    have hx' : x ∈ ⨅ i, Ideal.span {t} ^ i • (⊤ : Submodule R M) :=
      (Submodule.mem_iInf _).mpr fun n => (mem_pow_smul t n x).mpr (hx n)
    rw [h] at hx'
    simpa using hx'
  let C : Submodule R (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {t} ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
        ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.add_apply, map_add (f := _)]
          exact (ha1 N).add (hb1 N)
        · simp only [Pi.add_apply, ha2, hb2, map_add (f := _)]
          abel
      zero_mem' := ⟨fun N => by
          simp only [Pi.zero_apply, map_zero]
          exact IsLocallyConstant.const 0,
        fun g h => by simp⟩
      smul_mem' := by
        rintro r a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.smul_apply, map_smul]
          exact (ha1 N).comp (fun q => r • q)
        · simp only [Pi.smul_apply, ha2, smul_add, map_smul] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  haveI : Finite (R ⧸ Ideal.span {t}) := hfq
  haveI hM'fin : Finite (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) := Module.finite_of_finite (R ⧸ Ideal.span {t})
  let ρ' : G →* AddMonoid.End (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    { toFun := fun g => ((Ideal.span {t} • (⊤ : Submodule R M)).mapQ _ (ρ g)
        (Submodule.smul_top_le_comap_smul_top _ _)).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp
          rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp [Module.End.mul_apply]
          rfl }
  have hρ' : ∀ g x, ρ' g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := fun g x => rfl
  have hS := UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi l ρ' hΦ
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]
        exact Submodule.smul_mem_smul hlI Submodule.mem_top)
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        have h1 := hρ 1 x
        rw [pow_one] at h1
        exact h1)
  let Ψ : C →ₗ[R] (G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    LinearMap.pi fun g => (Ideal.span {t} • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.proj g ∘ₗ C.subtype)
  have hΨ : ∀ z g, Ψ z g = Submodule.Quotient.mk (z.1 g) := fun z g => rfl
  have hrange : ∀ z, Ψ z ∈ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
      ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
    intro z
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨?_, fun g h => ?_⟩
    · have h1 := hz1 1
      rw [pow_one] at h1
      exact h1
    · rw [hΨ, hΨ, hΨ, hz2, hρ', Submodule.Quotient.mk_add]
  have hker : LinearMap.ker Ψ = Ideal.span {t} • (⊤ : Submodule R C) := by
    apply le_antisymm
    · intro z hz
      have hz' : ∀ g, ∃ y, t • y = z.1 g := by
        intro g
        have h0 : Ψ z g = 0 := congrFun (LinearMap.mem_ker.mp hz) g
        rw [hΨ, Submodule.Quotient.mk_eq_zero, ← pow_one (Ideal.span {t})] at h0
        obtain ⟨y, hy⟩ := (mem_pow_smul t 1 _).mp h0
        exact ⟨y, by simpa using hy⟩
      choose y hy using hz'
      obtain ⟨hz1, hz2⟩ := z.2
      have hyC : y ∈ C := by
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · rw [IsLocallyConstant.iff_eventually_eq]
          intro x
          filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hz1 (N + 1)) x] with g hg
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg ⊢
          obtain ⟨w, hw⟩ := (mem_pow_smul t (N + 1) _).mp hg
          refine (mem_pow_smul t N _).mpr ⟨w, hcancel _ _ ?_⟩
          rw [smul_sub, hy, hy, ← hw, ← mul_smul, ← pow_succ']
        · apply hcancel
          rw [hy (g * h), smul_add, ← map_smul, hy g, hy h]
          exact hz2 g h
      have hzt : z = t • (⟨y, hyC⟩ : C) := Subtype.ext (funext fun g => (hy g).symm)
      rw [hzt]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top
    · intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        rw [LinearMap.mem_ker, map_smul]
        funext g
        rw [Pi.smul_apply, hΨ, ← Submodule.Quotient.mk_smul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro a b ha hb
        exact add_mem ha hb
  have hfin : Finite (C ⧸ LinearMap.ker Ψ) := by
    have hsub : (LinearMap.range Ψ : Set _) ⊆ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
        ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
      rintro _ ⟨z, rfl⟩
      exact hrange z
    haveI : Finite (LinearMap.range Ψ) := (hS.subset hsub).to_subtype
    exact Finite.of_equiv _ Ψ.quotKerEquivRange.symm.toEquiv
  rw [hker] at hfin
  haveI : IsHausdorff (Ideal.span {t}) C := by
    refine ⟨fun x hx => ?_⟩
    apply Subtype.ext
    funext g
    show x.1 g = 0
    apply hMh
    intro n
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero] at h1
    obtain ⟨y, hy⟩ := (mem_pow_smul t n x).mp h1
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  haveI : Module.Finite R (C ⧸ Ideal.span {t} • (⊤ : Submodule R C)) := Module.Finite.of_finite
  have hCfin : Module.Finite R C := (UpperTheory.V.abelian₂.nakayama R (Ideal.span {t}) C).2 this
  have hCfg : C.FG := Module.Finite.iff_fg.mp hCfin
  haveI := isNoetherian_of_fg_of_noetherian C hCfg
  have hZ'fg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have hZeq : Submodule.map C.subtype (Z.comap C.subtype) = Z :=
    Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])
  rw [← hZeq]
  exact hZ'fg.map _

theorem UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (Z : Submodule c.O (G → Fin m → c.O)), PhiCond G l → (∀ i j, AdicCont (maximalIdeal c.O) fun g => W.mat σ g i j) → (∀ z ∈ Z, (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧ ∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → Z.FG := by
  intro l _ c G _ _ _ _ _ m σ Z hΦ hσ hZ
  obtain ⟨hc, hf, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  haveI : IsPrecomplete (maximalIdeal c.O) c.O := hc.toIsPrecomplete
  let ρ : G →* Module.End c.O (Fin m → c.O) :=
    (Matrix.toLinAlgEquiv' (R := c.O) (n := Fin m)).toAlgHom.toRingHom.toMonoidHom.comp (W.mat σ)
  have hρ : ∀ g x, ρ g x = W.mat σ g *ᵥ x := fun g x => rfl
  refine cocycles_finitely_generated l t (maximalIdeal c.O) ht.maximalIdeal_eq ht.ne_zero (maximalIdeal.isMaximal c.O).ne_top
    hf hl ρ Z hΦ (fun N x => ?_) (fun z hz => ⟨fun N => ?_, fun g h => ?_⟩)
  · rw [lc_iff]
    intro i
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    filter_upwards [Filter.eventually_all.2 fun j => (hσ i j N).eventually_eq g] with g' hg'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hρ, Matrix.mulVec, dotProduct, map_sum, map_mul, hg']
  · rw [lc_iff]
    exact fun i => (hZ z hz).1 i N
  · rw [hρ]; exact (hZ z hz).2 g h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem zc_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val
  have h0 : ‖(x : PadicAlgCl l)‖ = spectralValue (minpoly ℚ_[l] (x : PadicAlgCl l)) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem zc_dvd {l : ℕ} [Fact l.Prime] (c : Coef l) (x y : c.O)
    (h : ‖(x : PadicAlgCl l)‖ < ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  rcases ValuationRing.dvd_total y x with h1 | ⟨u, rfl⟩
  · exact h1
  · exfalso
    rw [Subalgebra.coe_mul, norm_mul] at h
    exact absurd (mul_le_of_le_one_right (norm_nonneg _) (zc_norm c u)) (not_le.2 h)

private theorem zc_ev {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G] (c : Coef l)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) (x : G) :
    ∀ᶠ y in nhds x, (l : c.O) ^ N ∣ f y - f x := by
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  exact zc_dvd c _ _ (by push_cast; exact hy)

private theorem zc_split {l : ℕ} [hl : Fact l.Prime] (c c' : Coef l) (hcc : c.O ≤ c'.O) {G : Type} [Group G]
    [TopologicalSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (z : G → Fin m → PadicAlgCl l) (hz : Continuous z)
    (hm : ∀ g i, z g i ∈ c'.O)
    (hc : ∀ g h, z (g * h) = z g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ) g *ᵥ z h) :
    ∃ (n : ℕ) (b : Fin n → PadicAlgCl l) (w : Fin n → G → Fin m → c.O),
      (∀ k, (∀ i, AdicCont (maximalIdeal c.O) fun g => w k g i) ∧
        ∀ g h, w k (g * h) = w k g + W.mat σ g *ᵥ w k h) ∧
      ∀ g i, z g i = ∑ k, b k * (w k g i : PadicAlgCl l) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  letI : Algebra c.O c'.O := (Subalgebra.inclusion hcc).toRingHom.toAlgebra
  have ha : ∀ (a : c.O) (x : c'.O), ((a • x : c'.O) : PadicAlgCl l) = a * x := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite c.O c'.O := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul c.O c'.O := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective hcc)
  set_option synthInstance.maxHeartbeats 200000 in
  haveI : Module.Free c.O c'.O := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis c.O c'.O
  let f : G → Fin m → c'.O := fun g i => ⟨z g i, hm g i⟩
  refine ⟨_, fun k => b k, fun k g i => b.coord k (f g i), fun k => ⟨fun i N => ?_, fun g h => ?_⟩, fun g i => ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [zc_ev c' (fun g => f g i) ((continuous_apply i).comp hz) N x] with y ⟨u, hu⟩
    have e : (l : c'.O) ^ N * u = ((l : c.O) ^ N) • u := by rw [Algebra.smul_def, map_pow, map_natCast]
    rw [Ideal.Quotient.eq, ← map_sub, hu, e, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)
  · funext i
    have e : f (g * h) i = f g i + ∑ j, W.mat σ g i j • f h j := Subtype.ext (by
      rw [Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum]
      exact congrFun (hc g h) i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_add (f := _), map_sum, map_smul, Pi.add_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  · have e := congrArg Subtype.val (b.sum_repr (f g i))
    rw [AddSubmonoidClass.coe_finsetSum] at e
    refine e.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [ha, mul_comm]
    rfl

theorem UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) (Qbar l)), PhiCond G l → Continuous σ → Module.Finite (Qbar l) (Z1 (Loc.colRep σ)) := by
  intro l _ G _ _ _ _ _ m σ hΦ hσ
  classical
  obtain ⟨c₀, -⟩ := UpperTheory.V.X.So.coefOf l ⊥
  obtain ⟨c, Q, σ₀, -, hQ, hσ₀⟩ := UpperTheory.V.Ws.Eb.intModel c₀ σ hσ
  have hQ' : ∀ g, W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ g = Q⁻¹ * σ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  let Z : Submodule c.O (G → Fin m → c.O) :=
    { carrier := {z | (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧
          ∀ g h, z (g * h) = z g + W.mat σ₀ g *ᵥ z h}
      add_mem' := fun {a b} ha hb => ⟨fun i N => by
          simp only [Pi.add_apply, map_add (f := _)]; exact (ha.1 i N).add (hb.1 i N),
        fun g h => by simp only [Pi.add_apply, Matrix.mulVec_add, ha.2 g h, hb.2 g h]; abel⟩
      zero_mem' := ⟨fun i N => by
          simp only [Pi.zero_apply, map_zero]; exact IsLocallyConstant.const _, fun g h => by simp⟩
      smul_mem' := fun r a ha => ⟨fun i N => by
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          exact (ha.1 i N).comp (fun x => Ideal.Quotient.mk _ r * x),
        fun g h => by simp only [Pi.smul_apply, Matrix.mulVec_smul, ha.2 g h, smul_add]⟩ }
  obtain ⟨s, hs⟩ := UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond c σ₀ Z hΦ hσ₀ fun z hz => hz
  let ι : (G → Fin m → c.O) → G → Fin m → PadicAlgCl l := fun w g i => (w g i : PadicAlgCl l)
  let S : Submodule (PadicAlgCl l) (G → Fin m → PadicAlgCl l) := Submodule.span _ (ι '' s)
  have hS : ∀ w ∈ Z, ι w ∈ S := by
    intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact S.zero_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | smul a y _ hy => exact S.smul_mem (a : PadicAlgCl l) hy
  let T : (G → Fin m → PadicAlgCl l) →ₗ[PadicAlgCl l] (G → Fin m → PadicAlgCl l) :=
    (Matrix.toLin' (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l))).compLeft G
  have hfg : (S.map T).FG := (Submodule.fg_span (s.finite_toSet.image ι)).map T
  refine Module.Finite.iff_fg.2 (Submodule.FG.of_le hfg fun z hz => ?_)
  let z' : G → Fin m → PadicAlgCl l := fun g => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z g
  have hT : ∀ g, (Q : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ z' g = z g := fun g => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hz' : Continuous z' := continuous_const.matrix_mulVec hz.1
  have hc' : ∀ g h, z' (g * h) = z' g + W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g *ᵥ z' h := by
    intro g h
    have e : W.mat (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) g =
        ((Q⁻¹ * σ g * Q : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
      rw [← hQ']; rfl
    rw [e, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    exact congrArg (fun v => ((Q⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) *ᵥ v) (hz.2 g h)
  have hσ₁ : Continuous (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀) := by
    rw [show (W.pushRep (algebraMap c.O (PadicAlgCl l)) σ₀ : G → _) = fun g => Q⁻¹ * σ g * Q from funext hQ']
    exact (continuous_const.mul hσ).mul continuous_const
  obtain ⟨c', a, hcc, ha, hm⟩ := UpperTheory.V.Th.Det.cocField c _ z' hσ₁ hz' hc'
  obtain ⟨n, b, w, hw, e⟩ := zc_split c c' hcc σ₀ (a • z') (hz'.const_smul a) hm fun g h => by
    simp only [Pi.smul_apply, hc', smul_add, Matrix.mulVec_smul]
  refine ⟨z', ?_, funext hT⟩
  have e' : a • z' = ∑ k, b k • ι (w k) := by
    funext g i
    rw [e, Finset.sum_apply, Finset.sum_apply]
    rfl
  rw [SetLike.mem_coe, ← S.smul_mem_iff ha, e']
  exact S.sum_mem fun k _ => S.smul_mem _ (hS _ (hw k))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private def matrixFlattenLinearEquiv (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] (Fin (n * n) → K) where
  toFun X i := X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun v a b := v (finProdFinEquiv (a, b))
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    funext a b
    simp
  right_inv v := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

private theorem continuous_matrix_flatten (K : Type) [Field K] [TopologicalSpace K] (n : ℕ) :
    Continuous (matrixFlattenLinearEquiv K n) := by
  show Continuous fun (X : Matrix (Fin n) (Fin n) K) (i : Fin (n * n)) => X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  exact continuous_pi fun i => (continuous_apply _).comp (continuous_apply _)

private noncomputable def flattenedMatrixRepresentation {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) :
    G →* Matrix (Fin (n * n)) (Fin (n * n)) K where
  toFun g := LinearMap.toMatrix'
    ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap)
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp

private theorem matrix_rep_flatten_apply {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (g : G) (X : Matrix (Fin n) (Fin n) K) :
    Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv K n X) = matrixFlattenLinearEquiv K n (R g X) := by
  show Matrix.toLin' (LinearMap.toMatrix' _) _ = _
  rw [Matrix.toLin'_toMatrix']
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]

private theorem continuous_matrix_rep_flatten {K : Type} [Field K] [TopologicalSpace K] {G : Type} [Group G]
    [TopologicalSpace G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (hR : ∀ X, Continuous fun g => R g X) :
    Continuous (flattenedMatrixRepresentation R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g => LinearMap.toMatrix' ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap) i j
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_matrix_flatten K n).comp (hR _) |>.comp continuous_id |> fun h => (continuous_apply i).comp h

theorem UpperTheory.V.Th.Det.finite_cocycles_matrixRepresentation_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ} (R : Representation (Qbar l) G (Matrix (Fin n) (Fin n) (Qbar l))), PhiCond G l → (∀ X, Continuous fun g => R g X) → Module.Finite (Qbar l) (Z1 R) := by
  intro l _ G _ _ _ _ _ n R hΦ hR
  let σ : G →* GL (Fin (n * n)) (Qbar l) := (flattenedMatrixRepresentation R).toHomUnits
  have hσ : Continuous σ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_matrix_rep_flatten R hR, ?_⟩
    have h : (fun g => (((σ g)⁻¹ : GL (Fin (n * n)) (Qbar l)) : Matrix (Fin (n * n)) (Fin (n * n)) (Qbar l))) = fun g => flattenedMatrixRepresentation R g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [h]
    exact (continuous_matrix_rep_flatten R hR).comp continuous_inv
  have hfin := UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond σ hΦ hσ
  let Φ : (G → Matrix (Fin n) (Fin n) (Qbar l)) →ₗ[Qbar l] (G → Fin (n * n) → Qbar l) :=
    LinearMap.compLeft (matrixFlattenLinearEquiv (Qbar l) n).toLinearMap G
  have hmem : ∀ f ∈ Z1 R, Φ f ∈ Z1 (UpperTheory.V.Loc.colRep σ) := by
    rintro f ⟨hc, hco⟩
    refine ⟨(continuous_matrix_flatten (Qbar l) n).comp hc, fun g h => ?_⟩
    show matrixFlattenLinearEquiv (Qbar l) n (f (g * h)) = matrixFlattenLinearEquiv (Qbar l) n (f g) + Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv (Qbar l) n (f h))
    rw [hco g h, map_add (f := _), matrix_rep_flatten_apply]
  have hinj : Function.Injective (Φ.restrict hmem) := by
    intro x y hxy
    apply Subtype.ext
    funext g
    have e := congrFun (congrArg Subtype.val hxy) g
    exact (matrixFlattenLinearEquiv (Qbar l) n).injective e
  exact Module.Finite.of_injective (Φ.restrict hmem) hinj
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

section aux

variable {G K V : Type} [Group G] [Field K] [CharZero K] [AddCommGroup V] [Module K V]

omit [CharZero K] in
private theorem pn_rmul (R : Representation K G V) (g h : G) (X : V) : R (g * h) X = R g (R h X) := by
  rw [map_mul]; rfl

private theorem pn_norm (R : Representation K G V) (c : G) (hc : c * c = 1) (z : G → V)
    (hz : ∀ g h, z (g * h) = z g + R g (z h)) : ∃ X₀ : V, z c - (R c X₀ - X₀) = 0 := by
  have h1 : z 1 = 0 := by
    have := hz 1 1
    simpa using this
  have h2 : R c (z c) = -z c := by
    have := hz c c
    rw [hc, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  refine ⟨-((2 : K)⁻¹ • z c), ?_⟩
  rw [map_neg, map_smul, h2]
  have h3 : z c = (2 : K)⁻¹ • z c + (2 : K)⁻¹ • z c := by
    rw [← add_smul]; norm_num
  rw [smul_neg, neg_neg, sub_neg_eq_add, ← h3, sub_self]

omit [CharZero K] in
private theorem pn_conj (R : Representation K G V) (c : G) (hc : c * c = 1) (z : G → V)
    (hz : ∀ g h, z (g * h) = z g + R g (z h)) (h0 : z c = 0) (g : G) : z (c * g * c⁻¹) = R c (z g) := by
  rw [inv_eq_of_mul_eq_one_right hc, hz, hz, h0, map_zero, zero_add, add_zero]

private theorem pn_ext (R : Representation K G V) (η : G →* ℤˣ) (c : G) (hc : c * c = 1) (hη : η c = -1)
    (z : G → V) (hz : ∀ g h, z (g * h) = z g + R g (z h)) (h0 : z c = 0) (Y : V)
    (hY : ∀ g, η g = 1 → z g = R g Y - Y) : ∃ X, ∀ g, z g = R g X - X := by
  have hi : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcc : ∀ X, R c (R c X) = X := fun X => by rw [← pn_rmul, hc, map_one]; rfl
  have hY' : ∀ g, η g = 1 → z g = R g (R c Y) - R c Y := fun g hg => by
    have e : g = c * (c * g * c) * c⁻¹ := by
      rw [hi, ← mul_assoc, ← mul_assoc, hc, one_mul, mul_assoc, hc, mul_one]
    have h1 : η (c * g * c) = 1 := by rw [map_mul, map_mul, hη, hg]; simp
    have h2 := pn_conj R c hc z hz h0 (c * g * c)
    rw [← e, hY _ h1, map_sub, pn_rmul, pn_rmul, hcc] at h2
    exact h2
  have hA : ∀ g, η g = 1 → z g = R g ((2 : K)⁻¹ • (Y + R c Y)) - (2 : K)⁻¹ • (Y + R c Y) := fun g hg => by
    have h3 : z g = (2 : K)⁻¹ • (z g + z g) := by
      rw [smul_add, ← add_smul]; norm_num
    rw [map_smul, ← smul_sub, map_add (f := _), h3]
    congr 1
    nth_rewrite 1 [hY g hg]
    rw [hY' g hg]
    abel
  refine ⟨(2 : K)⁻¹ • (Y + R c Y), fun g => ?_⟩
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hA g hg
  · have h1 : η (g * c) = 1 := by rw [map_mul, hg, hη]; simp
    have h2 := hA _ h1
    rw [hz, h0, map_zero, add_zero, pn_rmul] at h2
    rw [h2, map_smul (R c), map_add (R c), hcc, add_comm (R c Y)]

end aux

theorem UpperTheory.V.Th.Det.polNorm :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)) (z : F.Γ → Matrix (Fin n) (Fin n) K), Ws.Eb.IsAdExt F ρ P R → (∀ g h, z (g * h) = z g + R g (z h)) → ∃ X₀ : Matrix (Fin n) (Fin n) K, (∀ g : F.G₀, (P : Matrix (Fin n) (Fin n) K) * (z (F.conj g) - Pa.dY F (W.mat ρ) X₀ (F.conj g)) = -((z g - Pa.dY F (W.mat ρ) X₀ g)ᵀ * P)) ∧ ∀ Y, (∀ g : F.G₀, z g - Pa.dY F (W.mat ρ) X₀ g = Pa.dY F (W.mat ρ) Y g) → ∃ X, ∀ g, z g = R g X - X := by
  intro l _ F K _ _ n ρ P R z hR hz
  obtain ⟨X₀, h0⟩ := pn_norm R F.c F.c_sq z hz
  have hd : ∀ (Y : Matrix (Fin n) (Fin n) K) (g : F.G₀), Pa.dY F (W.mat ρ) Y g = R g Y - Y := fun Y g => by
    rw [hR.ad]
    change (ρ g : Matrix (Fin n) (Fin n) K) * Y * (ρ g⁻¹ : GL (Fin n) K) - Y = _
    rw [map_inv]
    rfl
  have hz' : ∀ g h, (z (g * h) - (R (g * h) X₀ - X₀)) = (z g - (R g X₀ - X₀)) + R g (z h - (R h X₀ - X₀)) :=
    fun g h => by
      rw [hz, pn_rmul, map_sub, map_sub]
      abel
  refine ⟨X₀, fun g => ?_, fun Y hY => ?_⟩
  · rw [hd, hd]
    have h1 := pn_conj R F.c F.c_sq (fun g => z g - (R g X₀ - X₀)) hz' h0 g
    have h2 : ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c⁻¹ := rfl
    rw [h2, h1, hR.c, Matrix.mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K),
      Units.mul_inv, Matrix.one_mul]
  · obtain ⟨X, hX⟩ := pn_ext R F.η F.c F.c_sq F.η_c (fun g => z g - (R g X₀ - X₀)) hz' h0 Y fun g hg => by
      have := hY ⟨g, hg⟩
      rwa [hd, hd] at this
    refine ⟨X₀ + X, fun g => ?_⟩
    have := hX g
    rw [map_add (f := _), add_sub_add_comm, ← this]
    abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RegDet
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.regDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)] [IsScalarTower ℤ_[l] O (Qbar l)] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), 1 ≤ n → PhiCond F.G₀ l → (∃ g : F.G₀, F.ε g ≠ 1) → Continuous ρ → Th.TypeI F ρ → Th.N3 F ρ → Th.RegDet F O ρ P := by
  intro l _ F O _ _ _ _ n ρ P hn hΦ hε hρ hI h3
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  have halg : ∀ x : ℤ_[l], algebraMap ℤ_[l] (Qbar l) x = algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x
  have hχ : ∀ g : F.G₀, ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) (((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [← halg, IsScalarTower.algebraMap_apply ℤ_[l] O (Qbar l)]
    rfl
  have hχc : Continuous fun g : F.G₀ => ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hχ]
    have h1 : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp h1)
  have hm : Continuous fun g => W.mat ρ g := Units.continuous_val.comp hρ
  have hm' : Continuous fun g : F.G₀ => W.mat ρ g⁻¹ := hm.comp continuous_inv
  let R : Representation (Qbar l) F.G₀ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    Loc.twist (F.eps O (Qbar l)) (Loc.adGL ρ)
  have hR : ∀ g X, R g X =
      ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) • (W.mat ρ g * X * W.mat ρ g⁻¹) := fun g X => by
    have e : W.mat ρ g⁻¹ = Units.val (ρ g)⁻¹ := by
      rw [← map_inv ρ g]; rfl
    rw [e]
    rfl
  haveI : Module.Finite (Qbar l) (Z1 R) := Det.finite_cocycles_matrixRepresentation_of_phiCond R hΦ fun X => by
    simp only [hR]
    exact hχc.smul ((hm.mul continuous_const).mul hm')
  let S : Type := {σ : F.G₀ // σ ∈ F.G' ∧ (W.mat ρ σ).charpoly.Separable}
  let f : S → ℕ → Z1 R →ₗ[Qbar l] Qbar l := fun σ k =>
    { toFun := fun z => (z.1 σ.1 * W.mat ρ σ.1 ^ k).trace
      map_add' := fun a b => by
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := Det.finDet f
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.1, fun j => (T.equivFin.symm j).1.2, ?_⟩
  intro z hzc hz _ htr
  have hzZ : z ∈ Z1 R := (mem_Z1_iff_cocycle _ _).2 ⟨hzc, fun g h => by rw [hR]; exact hz g h⟩
  have hall := hT ⟨z, hzZ⟩ fun s hs k =>
    htr s.1 ⟨T.equivFin ⟨s, hs⟩, by simp only [Equiv.symm_apply_apply]⟩ k
  refine Det.detG ρ (F.eps O (Qbar l)) F.G' z hn (Abelianization.commutator_subset_ker _) ?_ ?_ hI hz ?_
  · intro g hg
    have h1 : F.ε g = 1 := hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hχ, h1]
    simp
  · obtain ⟨g, hg⟩ := hε
    intro h
    apply hg
    have h1 := hχ g
    rw [h, MonoidHom.one_apply, Units.val_one, ← map_one (algebraMap ℚ_[l] (Qbar l))] at h1
    have h2 := (algebraMap ℚ_[l] (Qbar l)).injective h1
    exact Units.ext (Subtype.ext h2.symm)
  · intro g hg
    by_contra hne
    have ho : IsOpen {x : F.G₀ | (z x * W.mat ρ x).trace ≠ 0} :=
      isOpen_ne_fun (hzc.mul hm).matrix_trace continuous_const
    obtain ⟨σ, ⟨h1, h2⟩, h4⟩ := h3 _ ho ⟨g, hne, hg⟩
    have h5 : (z σ * W.mat ρ σ ^ 1).trace = 0 := hall ⟨σ, h2, h4⟩ 1
    rw [pow_one] at h5
    exact h1 h5
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (l := l) (L := L) (Ω := Ω) (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 ((l : ℕ) : 𝓞 L)).1 (by simpa only [map_natCast] using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
