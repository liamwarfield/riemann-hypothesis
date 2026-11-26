module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormal
open IsLocalRing Polynomial

namespace GlobalTheory.NormalStrictHens

theorem exists_mem_finset {S : Type} [CommRing S] {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R) (hcov : ∀ x : S, ∃ i, x ∈ R i)
    (s : Finset S) : ∃ i, ∀ x ∈ s, x ∈ R i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hmono hjk hj
    · exact hmono hik (hi y hy)

theorem isDomain_of_directed {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i)) : IsDomain S := by
  classical
  haveI : NoZeroDivisors S := ⟨fun {x y} hxy => by
    obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov {x, y}
    haveI := hdom k
    have hx : x ∈ R k := hk x (by simp)
    have hy : y ∈ R k := hk y (by simp)
    have h : (⟨x, hx⟩ : R k) * ⟨y, hy⟩ = 0 := Subtype.ext hxy
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain S

theorem isIntegrallyClosed_of_directed {S : Type} [CommRing S] [IsDomain S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i))
    (hic : ∀ i, IsIntegrallyClosed (R i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨f, hfm, hf⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) x
  obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov (insert a (insert (b : S) f.coeffs))
  haveI := hdom k
  haveI := hic k
  have ha : a ∈ R k := hk a (by simp)
  have hb : (b : S) ∈ R k := hk b (by simp)
  have hcf : (f.coeffs : Set S) ⊆ R k := fun c hc =>
    hk c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
  have hgm : (f.toSubring (R k) hcf).Monic := (monic_toSubring f (R k) hcf).2 hfm
  have hgf : (f.toSubring (R k) hcf).map (R k).subtype = f := map_toSubring f (R k) hcf
  have hinj : Function.Injective ((algebraMap S (FractionRing S)).comp (R k).subtype) :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (R k) →+* FractionRing S := IsFractionRing.lift hinj
  have hφ : ∀ r : R k, φ (algebraMap (R k) (FractionRing (R k)) r) = algebraMap S (FractionRing S) r :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  have hb0 : (⟨b, hb⟩ : R k) ∈ nonZeroDivisors (R k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero b (congrArg Subtype.val h)
  have hφy : φ (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) =
      IsLocalization.mk' (FractionRing S) a b := by
    rw [IsFractionRing.lift_mk', IsFractionRing.mk'_eq_div]
    rfl
  have hcomp : φ.comp (algebraMap (R k) (FractionRing (R k))) =
      (algebraMap S (FractionRing S)).comp (R k).subtype := by
    ext r
    exact hφ r
  have hy : IsIntegral (R k) (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) := by
    refine ⟨f.toSubring (R k) hcf, hgm, ?_⟩
    apply φ.injective
    rw [map_zero, hom_eval₂, hφy, hcomp, ← eval₂_map, hgf]
    exact hf
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (R k))).1 inferInstance hy
  refine ⟨c, ?_⟩
  rw [← hφ, hc, hφy]

end GlobalTheory.NormalStrictHens

namespace GlobalTheory


open GlobalTheory.NormalStrictHens in
theorem exists_strictlyHenselian_normal_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  intro T _ _ _ hT A _ _ _ _ _ i hi
  haveI := hi
  obtain ⟨hThens, hTac, -⟩ :=
    GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  haveI := hThens
  haveI := hTac
  obtain ⟨S, _, _, _, hloc, hsc, -, hmax, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation A (SeparableClosure (ResidueField A))
  haveI := hsc
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) :=
    GlobalTheory.StrictHensUnion.indEtale_of_directed_union A S ι Si hmono hcov fun k => by
      obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale A B q.primeCompl)
  have hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap A S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  haveI : IsNoetherianRing S := GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt A S hind
  have hdi : ∀ k, IsDomain (Si k).toSubring ∧ IsIntegrallyClosed (Si k).toSubring := fun k => by
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
    obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A B q
    let e' : Localization.AtPrime q ≃+* (Si k).toSubring :=
      e.toRingEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
    exact ⟨e'.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e'⟩
  have hmono' : Monotone fun k => (Si k).toSubring := fun _ _ h => hmono h
  haveI : IsDomain S := isDomain_of_directed _ hmono' hcov fun k => (hdi k).1
  have hic : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_directed _ hmono' hcov (fun k => (hdi k).1) fun k => (hdi k).2
  obtain ⟨α, hα⟩ :=
    GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap A S) hsh i
  have hle : maximalIdeal S ≤ (maximalIdeal T).comap α := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]
    intro a ha
    exact map_nonunit i a ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hsc, inferInstance, hic,
    algebraMap A S, α, hα, ⟨fun s hs => ?_⟩⟩
  by_contra h
  exact (mem_maximalIdeal _).1 (hle ((mem_maximalIdeal s).2 h)) hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormalStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealExtensionPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrdersOfZmodPExtremes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrime
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrimeStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_domain_over_henselian_prime : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S), f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  first | (exact @GlobalTheory.NormalLocal.exists_normal_local) | (exact GlobalTheory.NormalLocal.exists_normal_local) | (intros; apply GlobalTheory.NormalLocal.exists_normal_local  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealUniquePrimeOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleIntersectionSymmetry
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyOrigin

theorem originIdeal_eq_comap (T : Type) [CommRing T] [IsLocalRing T] :
    GlobalTheory.KeyOriginCut.originIdeal T = (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
  ext g
  rw [GlobalTheory.LocalStage.mem_originIdeal_iff, Ideal.mem_comap, Polynomial.constantCoeff_apply]

theorem originIdeal_isMaximal (T : Type) [CommRing T] [IsLocalRing T] :
    (GlobalTheory.KeyOriginCut.originIdeal T).IsMaximal := by
  rw [originIdeal_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨Polynomial.C a, by simp⟩)

theorem mapRingHom_isIntegral {A S : Type} [CommRing A] [CommRing S] (f : A →+* S) (hf : f.IsIntegral) :
    (Polynomial.mapRingHom f).IsIntegral := by
  letI : Algebra (Polynomial A) (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  have hC : ∀ s : S, IsIntegral (Polynomial A) (Polynomial.C s) := by
    intro s
    obtain ⟨P, hPm, hP⟩ := hf s
    refine ⟨P.map Polynomial.C, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Polynomial A) (Polynomial S)).comp Polynomial.C = Polynomial.C.comp f := by
      refine RingHom.ext fun a => ?_
      change Polynomial.map f (Polynomial.C a) = _
      simp
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hX : IsIntegral (Polynomial A) (Polynomial.X : Polynomial S) := by
    have : algebraMap (Polynomial A) (Polynomial S) Polynomial.X = Polynomial.X := Polynomial.map_X f
    rw [← this]
    exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact hp.add hq
  | monomial n a _ => exact (hC a).mul (hX.pow _)

theorem polyOrigin : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  intro A S _ _ _ _ f hf

  have hmA : (maximalIdeal S).comap f = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (maximalIdeal S)
    exact IsLocalRing.eq_maximalIdeal this
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal S).comap f := by
      rw [hmA]; exact (mem_maximalIdeal a).mpr hna
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨mapRingHom_isIntegral f hf, (originIdeal_isMaximal S).isPrime,
    GlobalTheory.LocalStage.comap_originIdeal f, ?_⟩
  intro 𝔔 h𝔔 hc
  have hXmem : (Polynomial.X : Polynomial S) ∈ 𝔔 := by
    have : (Polynomial.X : Polynomial A) ∈ 𝔔.comap (Polynomial.mapRingHom f) := by
      rw [hc, GlobalTheory.LocalStage.mem_originIdeal_iff]; simp
    simpa using this

  haveI : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsPrime := Ideal.comap_isPrime _ _
  have hcC : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).comap f = maximalIdeal A := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h1 : Polynomial.C (f a) = Polynomial.mapRingHom f (Polynomial.C a) := by simp
    rw [h1, ← Ideal.mem_comap, hc, GlobalTheory.LocalStage.mem_originIdeal_iff, Polynomial.coeff_C_zero]
  have hmax : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf _ (by rw [hcC]; infer_instance)
  have hP : 𝔔.comap (Polynomial.C : S →+* Polynomial S) = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hmax
  have hle : GlobalTheory.KeyOriginCut.originIdeal S ≤ 𝔔 := by
    intro g hg
    rw [GlobalTheory.LocalStage.mem_originIdeal_iff] at hg
    rw [← Polynomial.X_mul_divX_add g]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hXmem) ?_
    have : g.coeff 0 ∈ 𝔔.comap (Polynomial.C : S →+* Polynomial S) := by rw [hP]; exact hg
    exact this
  exact ((originIdeal_isMaximal S).eq_of_le h𝔔.ne_top hle).symm

end GlobalTheory.PolyOrigin
end
end

open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOrigin
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OriginResidue

theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] :
    IsSepClosed L := by
  refine ⟨fun p hp => ?_⟩
  have h := IsSepClosed.splits_domain (f := e.toRingHom) (p.map e.symm.toRingHom) hp.map
  rwa [Polynomial.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by
    ext; simp, Polynomial.map_id] at h

variable {A : Type} [CommRing A] [IsLocalRing A]

def constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    A →+* (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField :=
  (algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField).comp Polynomial.C

theorem constToResidue_eq_zero [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] {a : A}
    (ha : a ∈ maximalIdeal A) : constToResidue a = 0 := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]
  simpa using ha

instance [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] : IsLocalHom (constToResidue (A := A)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have := constToResidue_eq_zero ((mem_maximalIdeal a).2 h)
  rw [this] at ha
  exact not_isUnit_zero ha

theorem algebraMap_eq_constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] (f : Polynomial A) :
    algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField f =
      constToResidue (f.coeff 0) := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero,
    GlobalTheory.LocalStage.mem_originIdeal_iff]
  simp

theorem lift_surjective [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    Function.Surjective (ResidueField.lift (constToResidue (A := A))) := by
  set p := GlobalTheory.KeyOriginCut.originIdeal A
  intro x
  obtain ⟨z, rfl⟩ := residue_surjective x
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : algebraMap (Polynomial A) p.ResidueField s ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  have key : residue _ (IsLocalization.mk' (Localization.AtPrime p) f s) *
      algebraMap (Polynomial A) p.ResidueField s = algebraMap (Polynomial A) p.ResidueField f := by
    rw [IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField f,
      ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
  refine ⟨residue A (f.coeff 0) / residue A ((s : Polynomial A).coeff 0), ?_⟩
  rw [map_div₀, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply,
    ← algebraMap_eq_constToResidue, ← algebraMap_eq_constToResidue, ← key, mul_div_cancel_right₀ _ hs]

theorem residue_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  intro A _ _ _ E _ _ _ Q _ hQ y
  set p := GlobalTheory.KeyOriginCut.originIdeal A with hp
  haveI : p.IsPrime := hQ ▸ Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨hQ.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsSepClosed p.ResidueField := isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ ⟨(ResidueField.lift (constToResidue (A := A))).injective, lift_surjective⟩)
  obtain ⟨x, hx⟩ := IsSepClosed.algebraMap_surjective p.ResidueField Q.ResidueField
    (residue (Localization.AtPrime Q) y)
  obtain ⟨c, rfl⟩ := lift_surjective x
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨Polynomial.C c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.lift_residue_apply]
  simp only [constToResidue, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime Q) Q.ResidueField, ResidueField.algebraMap_eq, sub_self]

end GlobalTheory.OriginResidue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOriginStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.OriginResidue.residue_origin) | (exact GlobalTheory.OriginResidue.residue_origin) | (intros; apply GlobalTheory.OriginResidue.residue_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorKernelMemMapIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleModelDegree
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem flat_one_tmul_eq_zero_mem_map (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P) :
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  intro hI y hy
  subst hI
  set K := RingHom.ker (algebraMap P T)
  let f : (P ⧸ K) →ₗ[P] T := (Ideal.Quotient.liftₐ K (Algebra.ofId P T) (fun a ha => RingHom.mem_ker.mp ha)).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [f] using hab
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f hf
  have h0 : (1 : P ⧸ K) ⊗ₜ[P] y = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, map_zero]
    simpa [f] using hy
  have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L K) h0
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

end GlobalTheory
end

open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_kernel_mem_map_ideal : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P),
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  first | (exact @GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (exact GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (intros; apply GlobalTheory.flat_one_tmul_eq_zero_mem_map  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_isLocalRing_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  intro P T L _ _ _ _ _ _ _ 𝔐 _ hM huniq hres

  let fκ : P →ₐ[P] L ⧸ maximalIdeal L := Algebra.ofId P _
  have hfκ : ∀ a, fκ a = Ideal.Quotient.mk (maximalIdeal L) (algebraMap P L a) := fun a => rfl
  have hsurj : Function.Surjective fκ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hres y
    exact ⟨a, by rw [hfκ]; exact (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : RingHom.ker fκ = (maximalIdeal L).comap (algebraMap P L) := by
    ext a
    rw [RingHom.mem_ker, hfκ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e : (P ⧸ RingHom.ker fκ) ≃ₐ[P] L ⧸ maximalIdeal L := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let q : (P ⧸ RingHom.ker fκ) →ₐ[P] T ⧸ 𝔐 :=
    Ideal.quotientMapₐ 𝔐 (Algebra.ofId P T) (le_of_eq (by rw [hker, ← hM]; rfl))
  let g : L →ₐ[P] T ⧸ 𝔐 := (q.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ P (maximalIdeal L))
  have hg : ∀ a : P, ∀ y : L, y - algebraMap P L a ∈ maximalIdeal L →
      g y = Ideal.Quotient.mk 𝔐 (algebraMap P T a) := by
    intro a y hy
    have h1 : Ideal.Quotient.mkₐ P (maximalIdeal L) y = Ideal.Quotient.mkₐ P (maximalIdeal L) (algebraMap P L a) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq.mpr hy
    have h2 : g y = g (algebraMap P L a) := by
      simp only [g, AlgHom.comp_apply]; rw [h1]
    rw [h2, AlgHom.commutes]; rfl
  let ψ : TensorProduct P T L →ₐ[P] T ⧸ 𝔐 :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P 𝔐) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ t y, ψ (t ⊗ₜ[P] y) = Ideal.Quotient.mk 𝔐 t * g y := by
    intro t y; simp [ψ, Algebra.TensorProduct.lift_tmul]
  haveI : Nontrivial (T ⧸ 𝔐) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨t ⊗ₜ[P] 1, by rw [hψ, map_one, mul_one]⟩
  haveI : Nontrivial (TensorProduct P T L) := hψs.nontrivial

  letI : Algebra L (TensorProduct P T L) := Algebra.TensorProduct.rightAlgebra
  have hmap : ∀ x, algebraMap L (TensorProduct P T L) x = (1 : T) ⊗ₜ[P] x := fun _ => rfl
  have hint : Algebra.IsIntegral L (TensorProduct P T L) := by
    constructor
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | add a b ha hb => exact ha.add hb
    | tmul a b =>
      have h1 : a ⊗ₜ[P] b = (a ⊗ₜ[P] (1 : L)) * algebraMap L (TensorProduct P T L) b := by
        rw [hmap]; simp
      rw [h1]
      refine IsIntegral.mul ?_ isIntegral_algebraMap
      have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
      have h2 : IsIntegral P (a ⊗ₜ[P] (1 : L)) :=
        ha.map (Algebra.TensorProduct.includeLeft : T →ₐ[P] TensorProduct P T L)
      obtain ⟨p, hp, hp0⟩ := h2
      refine ⟨p.map (algebraMap P L), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) = algebraMap P _ := by
        ext x
        exact (Algebra.TensorProduct.includeRight : L →ₐ[P] TensorProduct P T L).commutes x
      rw [this]; exact hp0
  have hPB : ∀ a : P, (algebraMap P T a) ⊗ₜ[P] (1 : L) = (1 : T) ⊗ₜ[P] (algebraMap P L a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have key : ∀ 𝔫 : Ideal (TensorProduct P T L), 𝔫.IsMaximal → 𝔫 = RingHom.ker ψ := by
    intro 𝔫 h𝔫
    have hLmax : (𝔫.comap (algebraMap L (TensorProduct P T L))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap L (TensorProduct P T L)) (by
          intro x
          exact hint.isIntegral x) 𝔫
    have hL : 𝔫.comap (algebraMap L (TensorProduct P T L)) = maximalIdeal L :=
      IsLocalRing.eq_maximalIdeal hLmax
    let iT : T →+* TensorProduct P T L := Algebra.TensorProduct.includeLeftRingHom
    have hiT : ∀ t, iT t = t ⊗ₜ[P] (1 : L) := fun _ => rfl
    have hcomp : iT.comp (algebraMap P T) = (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) := by
      ext a; simp only [RingHom.comp_apply, hiT, hmap]; exact hPB a
    have hT : 𝔫.comap iT = 𝔐 := by
      apply huniq
      · exact Ideal.comap_isPrime iT 𝔫
      · rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hL]
    let j : T ⧸ 𝔐 →+* TensorProduct P T L ⧸ 𝔫 := Ideal.quotientMap 𝔫 iT hT.ge
    have hj : Function.Injective j := Ideal.quotientMap_injective' hT.le
    have hφ : ∀ b, Ideal.Quotient.mk 𝔫 b = j (ψ b) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
      | tmul t y =>
        obtain ⟨a, ha⟩ := hres y
        have hy1 : (1 : T) ⊗ₜ[P] (y - algebraMap P L a) ∈ 𝔫 := by
          rw [← hmap, ← Ideal.mem_comap, hL]; exact ha
        have hsplit : t ⊗ₜ[P] y - (t * algebraMap P T a) ⊗ₜ[P] (1 : L) = (t ⊗ₜ[P] (1 : L)) * ((1 : T) ⊗ₜ[P] (y - algebraMap P L a)) := by
          rw [TensorProduct.tmul_sub, mul_sub, ← hPB]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hψ, hg a y ha, ← map_mul]
        show _ = Ideal.quotientMap 𝔫 iT hT.ge (Ideal.Quotient.mk 𝔐 (t * algebraMap P T a))
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hiT, hsplit]
        exact 𝔫.mul_mem_left _ hy1
    ext b
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, RingHom.mem_ker, map_eq_zero_iff j hj]
  obtain ⟨𝔫₀, h0⟩ := Ideal.exists_maximal (TensorProduct P T L)
  exact IsLocalRing.of_unique_max_ideal ⟨𝔫₀, h0, fun 𝔫 h => (key 𝔫 h).trans (key 𝔫₀ h0).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOverStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  first | (exact @GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (exact GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (intros; apply GlobalTheory.tensor_isLocalRing_of_unique_prime_over  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEt
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEtStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale : ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R] [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
    IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) → IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (exact GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (intros; apply GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale <;> assumption)
end
end

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
end

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_extension_prime : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  first | (exact @GlobalTheory.OriginPrimes.origin_primes) | (exact GlobalTheory.OriginPrimes.origin_primes) | (intros; apply GlobalTheory.OriginPrimes.origin_primes <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOrigin
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GoodStageOrigin

theorem local_props (A' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (E : Type) [CommRing E] [Algebra (Polynomial A') E] [Algebra.Etale (Polynomial A') E]
    (Q : Ideal E) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q) ∧
      (letI : Algebra A' (Localization.AtPrime Q) :=
        ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
       Module.Flat A' (Localization.AtPrime Q)) := by
  haveI : IsIntegrallyClosed (Polynomial A') := by
    haveI := GlobalTheory.isIntegrallyClosed_mvPolynomial_fin A' 1
    exact IsIntegrallyClosed.of_equiv
      (MvPolynomial.uniqueAlgEquiv A' (Fin 1)).toRingEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A') E Q
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing (Polynomial A') E
  refine ⟨h1, IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance, h2, ?_⟩
  letI : Algebra A' (Localization.AtPrime Q) :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower A' (Polynomial A') (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat (Polynomial A') E := inferInstance
  haveI : Module.Flat E (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E _
  exact Module.Flat.trans A' (Polynomial A') _

theorem good_stage : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA sA hsA
  have hO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T := by
    haveI : IsLocalHom φ := hsh.2.2.1
    rw [← hφ, ← Ideal.comap_comap, GlobalTheory.comap_maximalIdeal_of_localHom_strictHens φ, ← hP]
    first
      | exact Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      | exact Localization.AtPrime.under_maximalIdeal
      | simpa [Ideal.under] using Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
  obtain ⟨A', _, _, _, _, _, _, ι, α, hια, hα⟩ := GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal T hT A i hil
  obtain ⟨E', _, _, _, Q', _, hQ', β, γ, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_localStage_tensor_polynomial_origin T O hO A i hil EA QA hQA jA hjA A' ι α hια hα
  obtain ⟨hd, hn, hic, hfl⟩ := local_props A' E' Q'
  letI alg : Algebra A' (Localization.AtPrime Q') :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, Localization.AtPrime Q',
    inferInstance, hd, inferInstance, hn, hic, alg, hfl, ι, α, β, γ, ?_, h2, h3, ?_, ?_⟩
  · have e : algebraMap A (Localization.AtPrime QA) =
        (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C := by
      rw [IsScalarTower.algebraMap_eq A EA (Localization.AtPrime QA),
        IsScalarTower.algebraMap_eq A (Polynomial A) EA, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_eq (Polynomial A) EA (Localization.AtPrime QA)]
      rfl
    rw [e]
    exact h1
  · intro h
    apply hsA
    apply hi
    rw [map_zero, ← hια, RingHom.comp_apply, h, map_zero]
  · intro 𝔭 _ _ _
    exact GlobalTheory.T.origin_ideal_extension_prime A' 𝔭 E' Q' hQ'

end GlobalTheory.GoodStageOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end
