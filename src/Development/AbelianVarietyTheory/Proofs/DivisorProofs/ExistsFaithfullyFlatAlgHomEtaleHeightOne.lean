module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem faithfullyFlat_adicCompletion_span (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion (Ideal.span {t}) R) := by
  haveI : Module.Flat R (AdicCompletion (Ideal.span {t}) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hle : Ideal.span {t} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmax := AdicCompletion.isMaximal_map_of_le (Ideal.span {t}) (maximalIdeal R) hle
    (Submodule.fg_span_singleton t)
  intro h
  apply hmax.ne_top
  have e := Ideal.smul_top_eq_map (S := AdicCompletion (Ideal.span {t}) R) (maximalIdeal R)
  rw [h] at e
  apply Submodule.restrictScalars_injective R
  rw [← e]; rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem exists_integral_point (A R C : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [CommRing C] [Algebra R C] (ρ : R →+* A) (hint : Algebra.IsIntegral R C)
    (s : C →+* FractionRing A) (hs : s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) :
    ∃ g : C →+* A, (algebraMap A (FractionRing A)).comp g = s ∧ g.comp (algebraMap R C) = ρ := by
  set K := FractionRing A
  have hmem : ∀ c : C, s c ∈ (algebraMap A K).range := by
    intro c
    obtain ⟨p, hp, hpc⟩ := hint.isIntegral c
    have hi : IsIntegral A (s c) := by
      refine ⟨p.map ρ, hp.map ρ, ?_⟩
      rw [Polynomial.eval₂_map, ← hs, ← Polynomial.hom_eval₂, hpc, map_zero]
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
    exact ⟨a, ha⟩
  let e := RingEquiv.ofBijective (algebraMap A K).rangeRestrict
    ⟨fun x y h => IsFractionRing.injective A K (congrArg Subtype.val h),
     (algebraMap A K).rangeRestrict_surjective⟩
  let g : C →+* A := e.symm.toRingHom.comp (s.codRestrict _ hmem)
  have hg : (algebraMap A K).comp g = s := by
    ext c
    have : e (g c) = s.codRestrict _ hmem c := by simp [g]
    exact congrArg Subtype.val this
  refine ⟨g, hg, ?_⟩
  ext r
  apply IsFractionRing.injective A K
  have := congrArg (fun f => f r) hs
  simp only [RingHom.comp_apply] at this
  change (algebraMap A K) (g (algebraMap R C r)) = _
  rw [← this, ← hg, RingHom.comp_apply]
  rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_pow_of_mul_mem_pow (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R)
    (a : A) (ha : a ≠ 0) : ∀ (n : ℕ) (r : R), algebraMap A R a * r ∈ Ideal.span {t ^ n} →
      r ∈ Ideal.span {t ^ n} := by
  have hρa : ρ (algebraMap A R a) = a := by
    simpa using congrArg (fun f => f a) hρ
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have hr1 : algebraMap A R a * r ∈ RingHom.ker ρ := by
      rw [hker, Ideal.mem_span_singleton]
      exact (dvd_pow_self t (Nat.succ_ne_zero n)).trans (Ideal.mem_span_singleton.1 hr)
    rw [RingHom.mem_ker, map_mul, hρa] at hr1
    have hr0 : r ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker]
      exact (mul_eq_zero.1 hr1).resolve_left ha
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hr0
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
    have h2 : algebraMap A R a * r' = t ^ n * q := by
      have : t * (algebraMap A R a * r') = t * (t ^ n * q) := by
        rw [pow_succ] at hq
        linear_combination hq
      have h3 : t * (algebraMap A R a * r' - t ^ n * q) = 0 := by rw [mul_sub, this, sub_self]
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h3)
    have := ih r' (Ideal.mem_span_singleton.2 ⟨q, h2⟩)
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.1 this
    exact Ideal.mem_span_singleton.2 ⟨q', by ring⟩

theorem torsionFree_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.TorsionFreeOver A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha n r hm

end GlobalTheory.GoodEtaleSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetraction
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem hartRep_one (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (a : A) (r : R)
    (h : ∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t}) :
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have hmem : ρ r ∈ Ideal.span {a} := by
    refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one a (ρ r) fun p hp hp1 => ?_
    obtain ⟨u, hu, m', hm⟩ := h p hp hp1
    refine ⟨u, hu, Ideal.mem_span_singleton.2 ⟨ρ m', ?_⟩⟩
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, hρa, hρa, sub_eq_zero] at hm
    exact hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨algebraMap A R b, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, hρa, hρa, hb, sub_self]

theorem hartRep (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (a : A) (ha : a ≠ 0) :
    ∀ n : ℕ, ∀ r : R, (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t ^ n}) →
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t ^ n} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have ht0 : ρ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  intro n
  induction n with
  | zero => intro r _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x, hx⟩ := hartRep_one A R ρ hρ t hker a r fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      exact ⟨u, hu, m', Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t n.succ_ne_zero) hm⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨y', hy'⟩ := ih y fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
      have key : t * (algebraMap A R u * y) - algebraMap A R a * (m' - algebraMap A R u * x)
          = t ^ (n + 1) * q := by
        linear_combination hq - (algebraMap A R u) * hy
      have h2 : a * ρ (m' - algebraMap A R u * x) = 0 := by
        have := congrArg ρ key
        rw [map_sub] at this
        simp only [map_mul, map_pow, ht0, hρa, zero_mul, zero_sub, zero_pow n.succ_ne_zero,
          neg_eq_zero] at this
        exact this
      have h3 : m' - algebraMap A R u * x ∈ Ideal.span {t} := by
        rw [← hker, RingHom.mem_ker]
        exact (mul_eq_zero.1 h2).resolve_left ha
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h3
      refine ⟨u, hu, z, Ideal.mem_span_singleton.2 ⟨q, ?_⟩⟩
      have h4 : t * (algebraMap A R u * y - algebraMap A R a * z - t ^ n * q) = 0 := by
        rw [hz] at key
        linear_combination key
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h4)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hy'
    refine ⟨x + t * y', Ideal.mem_span_singleton.2 ⟨s, ?_⟩⟩
    linear_combination hy + t * hs

theorem hart_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', hr'⟩ := hartRep A R ρ hρ t hker ht a ha n r fun p hp hp1 => by
    obtain ⟨u, hu, m', hm'⟩ := hm p hp hp1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m'
    refine ⟨u, hu, s, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq, Ideal.span_singleton_pow] at hm'
    exact hm'
  refine ⟨Ideal.Quotient.mk _ r', ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow]
  exact hr'

end GlobalTheory.GoodEtaleSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetractionStatement
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHartogsProperty_quotient_span_pow_retraction : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  first | (exact @GlobalTheory.GoodEtaleSection.hart_quot) | (exact GlobalTheory.GoodEtaleSection.hart_quot) | (intros; apply GlobalTheory.GoodEtaleSection.hart_quot  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPoint
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem lift_of_etaleAt (R C B : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing B]
    [Algebra R B] (P : Ideal R) [P.IsPrime]
    (hE : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C))
    (hu : ∀ s : P.primeCompl, IsUnit (algebraMap R B s)) (I : Ideal B) (hI : IsNilpotent I) :
    (∀ φ : C →ₐ[R] B ⧸ I, ∃ φ' : C →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp φ' = φ) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp φ₁ = (Ideal.Quotient.mkₐ R I).comp φ₂ →
      φ₁ = φ₂) := by
  haveI := hE
  haveI : Algebra.FormallyEtale R (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallySmooth R (Localization.AtPrime P ⊗[R] C) :=
    Algebra.FormallySmooth.comp R (Localization.AtPrime P) _
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime P ⊗[R] C) :=
    Algebra.FormallyUnramified.comp R (Localization.AtPrime P) _
  let e : Localization.AtPrime P →ₐ[R] B :=
    IsLocalization.liftAlgHom (M := P.primeCompl) (f := Algebra.ofId R B) (fun y => hu y)
  constructor
  · intro φ
    let ψ : Localization.AtPrime P ⊗[R] C →ₐ[R] B ⧸ I :=
      Algebra.TensorProduct.productMap ((Ideal.Quotient.mkₐ R I).comp e) φ
    refine ⟨(Algebra.FormallySmooth.lift I hI ψ).comp Algebra.TensorProduct.includeRight, ?_⟩
    ext c
    simp [Algebra.FormallySmooth.mk_lift, ψ]
  · intro φ₁ φ₂ h
    have key : Algebra.TensorProduct.productMap e φ₁ = Algebra.TensorProduct.productMap e φ₂ := by
      refine Algebra.FormallyUnramified.ext I hI (fun x => ?_)
      have h2 : (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₁) =
          (Ideal.Quotient.mkₐ R I).comp (Algebra.TensorProduct.productMap e φ₂) := by
        apply Algebra.TensorProduct.ext'
        intro a c
        have := congrArg (fun f => f c) h
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
        simp [this]
      exact congrArg (fun f => f x) h2
    ext c
    have := congrArg (fun f => f ((1 : Localization.AtPrime P) ⊗ₜ[R] c)) key
    simpa using this

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem sub_retract_dvd (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (ρ : R →+* A)
    (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R) (hker : RingHom.ker ρ = Ideal.span {t})
    (r : R) : t ∣ r - algebraMap A R (ρ r) := by
  have hρa : ρ (algebraMap A R (ρ r)) = ρ r := by simpa using congrArg (fun f => f (ρ r)) hρ
  rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, hρa, sub_self]

theorem isUnit_loc (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (ρ : R →+* A)
    (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R) (hker : RingHom.ker ρ = Ideal.span {t})
    (n : ℕ) (S : Submonoid A) (s : R) (hs : ρ s ∈ S) :
    IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
      (S.map (algebraMap A R)))) s) := by
  obtain ⟨x, hx⟩ := sub_retract_dvd A R ρ hρ t hker s
  have e : s = algebraMap A R (ρ s) + t * x := by linear_combination hx
  rw [e, map_add (f := _)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)
  · refine ⟨n, ?_⟩
    rw [← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq,
      (Ideal.Quotient.eq_zero_iff_mem).2, map_zero]
    rw [mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
  · rw [IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n)]
    exact IsLocalization.map_units _ (⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _ hs)⟩ :
      Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n) (S.map (algebraMap A R)))

theorem local_lift (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R)
    (hker : RingHom.ker ρ = Ideal.span {t}) (hEt : GlobalTheory.GoodEtale.EtaleLow A R C) (g : C →+* A)
    (hg : g.comp (algebraMap R C) = ρ) (n : ℕ) (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    (∃ φ : C →ₐ[R] Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R))),
      ∀ c, algebraMap R _ t ∣ φ c - algebraMap R _ (algebraMap A R (g c))) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R))),
      (∀ c, algebraMap R _ t ∣ φ₁ c - algebraMap R _ (algebraMap A R (g c))) →
      (∀ c, algebraMap R _ t ∣ φ₂ c - algebraMap R _ (algebraMap A R (g c))) → φ₁ = φ₂) := by
  set L := Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {t} ^ n)
        (p.primeCompl.map (algebraMap A R)))
  let P := p.comap ρ
  haveI : P.IsPrime := Ideal.comap_isPrime ρ p
  have hPc : P.comap (algebraMap A R) = p := by
    simp only [P, Ideal.comap_comap, hρ, Ideal.comap_id]
  have hE := hEt P (by rw [hPc]; exact hp)
  have hu : ∀ s : P.primeCompl, IsUnit (algebraMap R L s) := fun s =>
    isUnit_loc A R ρ hρ t hker n p.primeCompl s s.2
  let I : Ideal L := Ideal.span {algebraMap R L t}
  have hI : IsNilpotent I := by
    have h0 : algebraMap R L t ^ n = 0 := by
      rw [← map_pow, IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {t} ^ n), Ideal.Quotient.algebraMap_eq,
        (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero]
    refine ⟨n, ?_⟩
    rw [show I ^ n = Ideal.span {algebraMap R L t ^ n} from Ideal.span_singleton_pow _ n, h0,
      Ideal.span_singleton_zero, Ideal.zero_eq_bot]
  obtain ⟨hex, huniq⟩ := lift_of_etaleAt R C L P hE hu I hI
  let ψ : C →ₐ[R] L ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp ((algebraMap R L).comp ((algebraMap A R).comp g))
      commutes' := fun r => by
        have h1 : g (algebraMap R C r) = ρ r := by simpa using congrArg (fun f => f r) hg
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, h1]
        rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]
        exact map_dvd _ (dvd_sub_comm.1 (sub_retract_dvd A R ρ hρ t hker r)) }
  have key : ∀ φ : C →ₐ[R] L, (∀ c, algebraMap R L t ∣ φ c - algebraMap R L (algebraMap A R (g c))) →
      (Ideal.Quotient.mkₐ R I).comp φ = ψ := by
    intro φ h
    ext c
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp,
      Function.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h c
  refine ⟨?_, fun φ₁ φ₂ h1 h2 => huniq φ₁ φ₂ ((key φ₁ h1).trans (key φ₂ h2).symm)⟩
  obtain ⟨φ, hφ⟩ := hex ψ
  refine ⟨φ, fun c => ?_⟩
  have := congrArg (fun f => f c) hφ
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ψ, AlgHom.coe_mk, RingHom.coe_comp,
      Function.comp_apply] at this
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
  exact this

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_span_of_mul_eq (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A) (t : R)
    (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (n : ℕ) (a : A) (ha : a ≠ 0)
    (z y : R ⧸ Ideal.span {t} ^ n)
    (h : z * Ideal.Quotient.mk _ (algebraMap A R a) = Ideal.Quotient.mk _ t * y) :
    z ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective y
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(Ideal.Quotient.eq_zero_iff_mem).2 (show r ∈ Ideal.span {t} ^ 0 by simp)]
    exact Ideal.zero_mem _
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at h
  have h1 : r * algebraMap A R a - t * r' ∈ Ideal.span {t} := Ideal.pow_le_self hn.ne' h
  have h2 : algebraMap A R a * r ∈ Ideal.span {t ^ 1} := by
    rw [pow_one]
    have := Ideal.add_mem _ h1 (Ideal.mul_mem_right r' _ (Ideal.mem_span_singleton_self t))
    rw [sub_add_cancel, mul_comm] at this
    exact this
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1
    (by simpa using mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha 1 r h2)
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem exists_algHom_quot_pow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ g : C →+* A, g.comp (algebraMap R C) = ρ →
    ∀ n : ℕ, ∃ f : C →ₐ[R] R ⧸ Ideal.span {t} ^ n, ∀ c : C,
      f c - Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c)) ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  intro A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hEt g hg n
  have hbot1 : (⊥ : Ideal A).height ≤ 1 := by simp
  set B := R ⧸ Ideal.span {t} ^ n
  set M0 := Algebra.algebraMapSubmonoid B ((⊥ : Ideal A).primeCompl.map (algebraMap A R))
  set L0 := Localization M0
  obtain ⟨⟨φ₀, hφ₀⟩, huniq⟩ : (∃ φ : C →ₐ[R] L0,
      ∀ c, algebraMap R L0 t ∣ φ c - algebraMap R L0 (algebraMap A R (g c))) ∧
    (∀ φ₁ φ₂ : C →ₐ[R] L0,
      (∀ c, algebraMap R L0 t ∣ φ₁ c - algebraMap R L0 (algebraMap A R (g c))) →
      (∀ c, algebraMap R L0 t ∣ φ₂ c - algebraMap R L0 (algebraMap A R (g c))) → φ₁ = φ₂) :=
    local_lift A R C ρ hρ t hker hEt g hg n ⊥ hbot1
  have hne : ∀ a : A, a ∈ (⊥ : Ideal A).primeCompl → a ≠ 0 := by
    rintro a ha rfl; exact ha (Ideal.zero_mem _)
  have hM0 : M0 ≤ nonZeroDivisors B := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine torsionFree_quot A R ρ hρ t hker ht n a (hne a ha) x ?_
    rw [Algebra.smul_def, mul_comm]
    exact hx
  have hinj : Function.Injective (algebraMap B L0) := IsLocalization.injective L0 hM0
  let ι : B →ₐ[R] L0 := IsScalarTower.toAlgHom R B L0
  have hι : ∀ b, ι b = algebraMap B L0 b := fun b => rfl
  have hRL : ∀ r : R, algebraMap R L0 r = algebraMap B L0 (Ideal.Quotient.mk _ r) := fun r =>
    IsScalarTower.algebraMap_apply R B L0 r
  have hHart := GlobalTheory.T.hasHartogsProperty_quotient_span_pow_retraction A R ρ hρ t hker ht n
  have hmem : ∀ c, φ₀ c ∈ ι.range := by
    intro c
    obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.mk'_surjective M0 (φ₀ c)
    have hspec := IsLocalization.mk'_spec L0 x m
    simp only at hxm
    rw [hxm] at hspec
    obtain ⟨_, ⟨a, ha, rfl⟩, hm⟩ := m.2
    obtain ⟨x', hx'⟩ := hHart a (hne a ha) x (fun p hp hh => by
      haveI := hp
      obtain ⟨⟨φp, hφp⟩, -⟩ := local_lift A R C ρ hρ t hker hEt g hg n p hh
      have hle : Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)) ≤ M0 := by
        rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨_, ⟨u, ?_, rfl⟩, rfl⟩
        rintro (h : u ∈ (⊥ : Ideal A))
        rw [Ideal.mem_bot] at h
        exact hu (h ▸ p.zero_mem)
      let j := IsLocalization.liftAlgHom
        (M := Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))
        (S := Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))))
        (f := ι) (fun y => IsLocalization.map_units L0 (⟨y, hle y.2⟩ : M0))
      have hj : ∀ b, j (algebraMap B _ b) = algebraMap B L0 b := fun b => by
        simp only [j, IsLocalization.liftAlgHom_apply]
        exact IsLocalization.lift_eq _ b
      have hjφ : j.comp φp = φ₀ := huniq _ _ (fun c => by
        have := map_dvd j (hφp c)
        rw [map_sub, j.commutes, j.commutes] at this
        exact this) hφ₀
      obtain ⟨⟨y, m'⟩, hym⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R))) (φp c)
      have hspec' := IsLocalization.mk'_spec
        (Localization (Algebra.algebraMapSubmonoid B (p.primeCompl.map (algebraMap A R)))) y m'
      simp only at hym
      rw [hym] at hspec'
      have hspec'' := congrArg j hspec'
      rw [map_mul, hj, hj, ← AlgHom.comp_apply, hjφ] at hspec''
      obtain ⟨_, ⟨u, hu, rfl⟩, hm'⟩ := m'.2
      refine ⟨u, hu, y, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def]
      apply hinj
      rw [map_mul, map_mul, ← hspec, ← hspec'', Ideal.Quotient.algebraMap_eq]
      rw [← hm, ← hm', Ideal.Quotient.algebraMap_eq]
      ring)
    refine ⟨x', ?_⟩
    show algebraMap B L0 x' = φ₀ c
    have hu := IsLocalization.map_units L0 m
    refine (hu.mul_left_inj).1 ?_
    rw [hspec, hx', Algebra.smul_def, map_mul, hm]
    ring
  let f : C →ₐ[R] B := (AlgEquiv.ofInjective ι hinj).symm.toAlgHom.comp (φ₀.codRestrict ι.range hmem)
  have hf : ∀ c, algebraMap B L0 (f c) = φ₀ c := by
    intro c
    have h1 : (AlgEquiv.ofInjective ι hinj) (f c) = ⟨φ₀ c, hmem c⟩ :=
      (AlgEquiv.ofInjective ι hinj).apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨f, fun c => ?_⟩
  obtain ⟨w, hw⟩ := hφ₀ c
  obtain ⟨⟨y, m⟩, hym⟩ := IsLocalization.mk'_surjective M0 w
  have hspec := IsLocalization.mk'_spec L0 y m
  simp only at hym
  rw [hym] at hspec
  obtain ⟨_, ⟨a, ha, rfl⟩, hm⟩ := m.2
  refine mem_span_of_mul_eq A R ρ hρ t hker ht n a (hne a ha) _ y ?_
  apply hinj
  rw [map_mul, map_mul, map_sub, hf, ← hRL, hw, ← hRL, hRL t, hRL, mul_assoc]
  rw [show Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R a) = (m : B) from hm, hspec]

end GlobalTheory.GoodEtaleSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPointStatement
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_quotient_pow_lifting_point : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ g : C →+* A, g.comp (algebraMap R C) = ρ →
    ∀ n : ℕ, ∃ f : C →ₐ[R] R ⧸ Ideal.span {t} ^ n, ∀ c : C,
      f c - Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c)) ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  first | (exact @GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (exact GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (intros; apply GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLow
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem algHom_quot_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  intro A R C _ _ _ _ _ _ ρ hρ t hker ht hE n f f' hff
  set P₀ : Ideal R := RingHom.ker ρ with hP₀
  haveI hP : P₀.IsPrime := RingHom.ker_isPrime ρ
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => by
    have := congrArg (fun g => g a) hρ
    simpa using this
  have hcomap : P₀.comap (algebraMap A R) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, hP₀, RingHom.mem_ker, Ideal.mem_bot, hρa]
  have hht : (P₀.comap (algebraMap A R)).height ≤ 1 := by
    rw [hcomap, Ideal.height_bot]; exact zero_le_one
  set Rp := Localization.AtPrime P₀
  haveI : Algebra.Etale Rp (Rp ⊗[R] C) := hE P₀ hht
  haveI : Algebra.FormallyUnramified R Rp := Algebra.FormallyUnramified.of_isLocalization P₀.primeCompl
  haveI : Algebra.FormallyUnramified R (Rp ⊗[R] C) := Algebra.FormallyUnramified.comp R Rp (Rp ⊗[R] C)
  set Q := R ⧸ Ideal.span {t} ^ n
  set B := Localization (Algebra.algebraMapSubmonoid Q P₀.primeCompl)
  letI : Algebra Rp B := localizationAlgebra P₀.primeCompl Q

  have hle : Algebra.algebraMapSubmonoid Q P₀.primeCompl ≤ nonZeroDivisors Q := by
    rintro _ ⟨s, hs, rfl⟩
    suffices H : ∀ x : Q, x * algebraMap R Q s = 0 → x = 0 from
      mem_nonZeroDivisors_iff.2 ⟨fun x hx => H x (by rw [mul_comm]; exact hx), H⟩
    intro x hx
    set a := ρ s
    have ha : a ≠ 0 := fun h => hs (RingHom.mem_ker.2 h)
    have hd : s - algebraMap A R a ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker, map_sub, hρa, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hd
    set u : Q := Ideal.Quotient.mk _ s
    set e : Q := Ideal.Quotient.mk _ (s - algebraMap A R a)
    have he : e ^ n = 0 := by
      simp only [e, ← map_pow, ← hr, mul_pow]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
    have hdv : u ∣ (u - e) ^ n := by
      have h1 := sub_dvd_pow_sub_pow (u - e) (-e) n
      rw [neg_pow, he, mul_zero, sub_zero, sub_neg_eq_add, sub_add_cancel] at h1
      exact h1
    obtain ⟨k, hk⟩ := hdv
    have hue : u - e = Ideal.Quotient.mk _ (algebraMap A R a) := by
      simp only [u, e, map_sub, sub_sub_cancel]
    have hzero : algebraMap A R (a ^ n) • x = 0 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow, ← hue, hk]
      calc u * k * x = k * (x * u) := by ring
        _ = 0 := by rw [show x * u = 0 from hx, mul_zero]
    exact torsionFree_quot A R ρ hρ t hker ht n (a ^ n) (pow_ne_zero n ha) x hzero
  have hinj : Function.Injective (algebraMap Q B) := IsLocalization.injective B hle
  let φ : Rp →ₐ[R] B := (Algebra.ofId Rp B).restrictScalars R
  let ι : Q →ₐ[R] B := IsScalarTower.toAlgHom R Q B
  let g₁ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f)
  let g₂ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f')
  set J : Ideal B := Ideal.span {algebraMap R B t}
  have hJ : IsNilpotent J := by
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow (algebraMap R B t) n, ← map_pow, IsScalarTower.algebraMap_apply R Q B,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot]
  have e : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂ := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro x; simp [g₁, g₂]
    · ext c
      simp only [g₁, g₂, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, one_mul, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hff c)
      rw [← hq, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [show ι (Ideal.Quotient.mk _ t) = algebraMap R B t from
        (IsScalarTower.algebraMap_apply R Q B t).symm]
      exact Ideal.mem_span_singleton_self _
  have hg : g₁ = g₂ := Algebra.FormallyUnramified.ext J hJ fun x => by
    simpa using congrArg (fun g => g x) e
  ext c
  apply hinj
  have := congrArg (fun g => g ((1 : Rp) ⊗ₜ[R] c)) hg
  simpa [g₁, g₂, ι] using this

end GlobalTheory.GoodEtaleSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLowStatement
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  first | (exact @GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (exact GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (intros; apply GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOne
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem exists_faithfullyFlat_algHom : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    Algebra.IsIntegral R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    (∃ s : C →+* FractionRing A, s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O), Module.FaithfullyFlat R O ∧ Nonempty (C →ₐ[R] O) := by
  intro A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hint hEt hs
  obtain ⟨s, hs⟩ := hs
  have ht0 : ρ t = 0 := RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self t)
  have htm : t ∈ maximalIdeal R := by
    by_contra h
    have hu : IsUnit (ρ t) := ((IsLocalRing.notMem_maximalIdeal.1 h)).map ρ
    rw [ht0] at hu
    exact not_isUnit_zero hu
  obtain ⟨g, -, hg⟩ := exists_integral_point A R C ρ hint s hs
  choose f hf using GlobalTheory.T.exists_algHom_quotient_pow_lifting_point A R C ρ hρ t hker ht hEt g hg
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)).comp (f n) = f m := by
    intro m n hle
    refine GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow A R C ρ hρ t hker ht hEt m _ _ fun c => ?_
    set φ := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)
    have h1 := hf n c
    have h2 := hf m c
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    have h1' := map_dvd φ h1
    have e1 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) t) = Ideal.Quotient.mk (Ideal.span {t} ^ m) t := rfl
    have e2 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c))) =
        Ideal.Quotient.mk (Ideal.span {t} ^ m) (algebraMap A R (g c)) := rfl
    rw [map_sub, e1, e2] at h1'
    have := dvd_sub h1' h2
    simpa using this
  exact ⟨AdicCompletion (Ideal.span {t}) R, inferInstance, inferInstance,
    faithfullyFlat_adicCompletion_span R t htm, ⟨AdicCompletion.liftAlgHom _ f compat⟩⟩

end GlobalTheory.GoodEtaleSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOneStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    Algebra.IsIntegral R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    (∃ s : C →+* FractionRing A, s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O), Module.FaithfullyFlat R O ∧ Nonempty (C →ₐ[R] O) := by
  first | (exact @GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom) | (exact GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom) | (intros; apply GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom <;> assumption)
end
