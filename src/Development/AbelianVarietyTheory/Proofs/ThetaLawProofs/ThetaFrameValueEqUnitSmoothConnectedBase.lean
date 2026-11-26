module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitude
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.RootConst

open GlobalTheory.AffinePoints

theorem preconnectedSpace_algHom (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra.FiniteType ℂ S] : PreconnectedSpace (S →ₐ[ℂ] ℂ) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) S 1 one_ne_zero
  refine ⟨(isEmbedding_coe (R := ℂ) (A := S) (C := ℂ)).isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨φ, trivial, rfl⟩

theorem exists_chart (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (p : S →ₐ[ℂ] ℂ) :
    ∃ (d : ℕ) (e : OpenPartialHomeomorph (S →ₐ[ℂ] ℂ) (Fin d → ℂ)),
      IsAlgebraicChart e ∧ p ∈ e.source := by
  have := RingHom.ker_isPrime p
  obtain ⟨s, hs, J, K, _, _, ⟨Q⟩⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  have H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension ℂ (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  exact ⟨Q.dimension, exists_isAlgebraicChart_of_away s (Localization.Away s) p hs⟩

theorem continuous_of_holomorphic_families (S : Type) [CommRing S] [Algebra ℂ S]
    [Algebra.Smooth ℂ S] (t : (S →ₐ[ℂ] ℂ) → ℂ)
    (h : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)), IsOpen B →
      (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → ContinuousOn (fun p => t (s p)) B) :
    Continuous t := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨d, e, he, hp⟩ := exists_chart S p
  have h1 := h d e.target e.symm e.open_target fun a => (he.analyticOnNhd a).differentiableOn
  have h2 : ContinuousOn t e.source :=
    (h1.comp e.continuousOn e.mapsTo).congr fun q hq => by
      simp only [Function.comp_apply, e.left_inv hq]
  exact h2.continuousAt (e.open_source.mem_nhds hp)

theorem eq_of_pow_eq_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {u : X → ℂ}
    (hu : Continuous u) {N : ℕ} (hN : 1 ≤ N) (h : ∀ x, u x ^ N = 1) (x y : X) : u x = u y := by
  have hfin : {z : ℂ | z ^ N = 1}.Finite := by
    refine (Polynomial.nthRootsFinset N (1 : ℂ)).finite_toSet.subset fun z hz => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset hN 1).2 hz)
  exact isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete hu.continuousOn
    (fun z _ => h z) trivial trivial

theorem value_eq_unit_of_pow_eq : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (y : KeyIn S) (N : ℕ) (r : Sˣ) (t : (S →ₐ[ℂ] ℂ) → ℂ) (s₀ : S →ₐ[ℂ] ℂ), 1 ≤ N → (∀ s, ∃ x : KeyIn ℂ, KeyPB x y s.toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t s = M.det ^ 4 / c ^ 8)) → (∀ s, t s ^ N = s r ^ N) → t s₀ = s₀ r → ∀ s, t s = s r := by
  intro hL hT hI S _ _ _ _ y N r t s₀ hN hx hpow h0 s
  have := preconnectedSpace_algHom S
  have ht : Continuous t := continuous_of_holomorphic_families S t fun m B σ hB hσ =>
    GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily hL hT hI S y m B σ (fun p => t (σ p)) hB hσ fun p _ => hx (σ p)
  have hr : ∀ q : S →ₐ[ℂ] ℂ, q r ≠ 0 := fun q => (r.isUnit.map q).ne_zero
  have hu : Continuous fun q : S →ₐ[ℂ] ℂ => t q / q r := ht.div (continuous_eval _) hr
  have h1 := eq_of_pow_eq_one hu hN
    (fun q => by rw [div_pow, hpow, div_self (pow_ne_zero N (hr q))]) s s₀
  rw [h0, div_self (hr s₀)] at h1
  exact (div_eq_one_iff_eq (hr s)).1 h1

end GlobalTheory.RootConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrame_value_eq_unit_smooth_connected_base : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S] (y : KeyIn S) (N : ℕ) (r : Sˣ) (t : (S →ₐ[ℂ] ℂ) → ℂ) (s₀ : S →ₐ[ℂ] ℂ), 1 ≤ N → (∀ s, ∃ x : KeyIn ℂ, KeyPB x y s.toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t s = M.det ^ 4 / c ^ 8)) → (∀ s, t s ^ N = s r ^ N) → t s₀ = s₀ r → ∀ s, t s = s r := by
  first | exact @GlobalTheory.RootConst.value_eq_unit_of_pow_eq | exact GlobalTheory.RootConst.value_eq_unit_of_pow_eq | (intros; apply GlobalTheory.RootConst.value_eq_unit_of_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam
open GlobalTheory.ZM.SiegPull

theorem LamIs.comp {S S' S'' : Scheme.{0}} {A' : Over S''} [GrpObj A'] {A : Over S'} [GrpObj A] {B : Over S}
    {L' : LB A'.left} {L : LB A.left} {Pb : LB (B ⊗ B).left} {ψ : A'.left ⟶ A.left} {φ : A.left ⟶ B.left}
    (hL' : L'.IsLB) (hL : L.IsLB) (hP : Pb.IsLB) (h' : LamIs A' L' A (abelian₂ A L) ψ) (h : LamIs A L B Pb φ) :
    LamIs A' L' B Pb (ψ ≫ φ) := by
  obtain ⟨ψ₂, sψ, iψ⟩ := h'
  obtain ⟨φ₂, sφ, iφ⟩ := h
  exact ⟨ψ₂ ≫ φ₂, isSquare_comp sψ sφ, LBIso.trans (DVR.linComb_isLB _ hL' _ _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (pull_isLB hP _) iψ (SiegPull.lbIso_pull_comp iφ ψ₂)⟩

theorem PolPB.lamIs {S S' : Scheme.{0}} {P' : Out.PolAV S'} {P : Out.PolAV S} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (h : PolPB P' P f φ) : LamIs P'.A P'.L P.A (abelian₂ P.A P.L) φ := by
  letI := P.isAb.comm
  letI := P'.isAb.comm
  obtain ⟨φ₂, s⟩ := exists_isSquare h.1.1.w
  exact ⟨φ₂, s, lbIso_lam_pull h.1 h.2.2 s⟩

theorem sqOf_calculus : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : S' ⟶ S), (∀ (g : S'' ⟶ S') (P : Out.PolAV S') (P' : Out.PolAV S'') (φ : P.A.left ⟶ c.A.left) (ψ : P'.A.left ⟶ P.A.left), SqOf P c f φ → PolPB P' P g ψ → SqOf P' c (g ≫ f) (ψ ≫ φ)) ∧ (∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (φ' : P'.A.left ⟶ c.A.left), SqOf P c f φ → SqOf P' c f φ' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ e.hom.left ≫ φ = φ' ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left) ∧ ∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (e : P'.A ≅ P.A), IsMonHom e.hom → P'.g = P.g → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → SqOf P c f φ → SqOf P' c f (e.hom.left ≫ φ) := by
  intro h k o _ ζ S S' S'' s c f
  refine ⟨fun g P P' φ ψ H H' => ⟨H'.1.comp H.1, H'.2.1.trans H.2.1,
      LamIs.comp P'.isLB P.isLB c.isLB H'.lamIs H.2.2⟩, fun P P' φ φ' H H' => ?_,
    fun P P' φ e he hg hl H => ⟨((isGrpPullback_of_iso e).comp H.1).congr (Category.id_comp _) rfl,
      hg.trans H.2.1, LamIs.comp P'.isLB P.isLB c.isLB hl H.2.2⟩⟩
  obtain ⟨e, he, hφ⟩ := grpPullback_iso H'.1 H.1
  obtain ⟨φ₂, s₂, i₂⟩ := H.2.2
  obtain ⟨φ₂', s₂', i₂'⟩ := H'.2.2
  refine ⟨e, he, hφ, _, isSquare_tensor e.hom, ?_⟩
  have k₁ := SiegPull.lbIso_pull_comp i₂ (e.hom ⊗ₘ e.hom).left
  rw [isSquare_unique (isSquare_comp (isSquare_tensor e.hom) s₂) s₂' hφ] at k₁
  exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (pull_isLB c.isLB _)
    (pull_isLB (DVR.linComb_isLB _ P.isLB _ _) _) i₂' k₁.symm

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem isPreirreducible_connectedComponent_of_smooth {K : Type} [Field K] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] (z : Z) : IsPreirreducible (connectedComponent z) := by
  have hK : GlobalTheory.IsNormalScheme (Spec (.of K)) := inferInstance
  have : GlobalTheory.IsNormalScheme Z := (GlobalTheory.isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((GlobalTheory.isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  rw [GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent]
  exact isIrreducible_irreducibleComponent.2

theorem apply_eq_of_isPreirreducible {T F : Type} [CommRing T] [Field F] (f g : T →+* F)
    (C : Set (PrimeSpectrum T)) (hC : IsPreirreducible C) (z : PrimeSpectrum F)
    (hf : PrimeSpectrum.comap f z ∈ C) (hg : PrimeSpectrum.comap g z ∈ C)
    (e : T) (he : IsIdempotentElem e) : f e = g e := by
  have hz : ∀ a : F, a ∈ z.asIdeal ↔ a = 0 := by
    intro a
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
    rw [this, Ideal.mem_bot]
  have key : ∀ (f g : T →+* F), PrimeSpectrum.comap f z ∈ C → PrimeSpectrum.comap g z ∈ C →
      f e = 0 → g e = 1 → False := by
    intro f g hf hg h0 h1
    obtain ⟨x, -, hx1, hx2⟩ := hC (PrimeSpectrum.basicOpen (1 - e)) (PrimeSpectrum.basicOpen e)
      (PrimeSpectrum.basicOpen _).2 (PrimeSpectrum.basicOpen _).2
      ⟨_, hf, by simp [hz, h0]⟩ ⟨_, hg, by simp [hz, h1]⟩
    have h : (1 - e) * e ∈ x.asIdeal := by
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]; exact x.asIdeal.zero_mem
    exact (x.2.mem_or_mem h).elim hx1 hx2
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map f) with h | h <;>
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map g) with h' | h'
  · rw [h, h']
  · exact (key f g hf hg h h').elim
  · exact (key g f hg hf h' h).elim
  · rw [h, h']

theorem lift_eq_of_sameComp_of_isIdempotentElem :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  intro K _ _ X s R _ _ i p q hs hi his ⟨hp, hq, hpq⟩ e he
  let T := ℂ ⊗[K] R
  let j : Sp T ⟶ pullback s (spMap (algebraMap K ℂ)) :=
    (pullbackSpecIso K ℂ R).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap (algebraMap K R)) (spMap (algebraMap K ℂ)) s (spMap (algebraMap K ℂ)) i (𝟙 _) (𝟙 _)
      (by rw [his, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : ℂ →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* T := (Algebra.TensorProduct.includeRight (R := K) (A := ℂ) (B := R) : R →+* T)
  have hj1 : j ≫ pullback.fst _ _ = spMap iR ≫ i := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd _ _ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  have hl : ∀ (r : R →ₐ[K] ℂ) (hr : (spMap r.toRingHom ≫ i) ≫ s = 𝟙 _ ≫ spMap (algebraMap K ℂ)),
      pullback.lift (spMap r.toRingHom ≫ i) (𝟙 _) hr =
        spMap (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _)).toRingHom ≫ j := by
    intro r hr
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hj1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      change r x = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) (1 ⊗ₜ[K] x)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    · rw [pullback.lift_snd, Category.assoc, hj2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      change (x : ℂ) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) ((x : ℂ) ⊗ₜ[K] 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl
  let z : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := hpq z
  have hC := isPreirreducible_connectedComponent_of_smooth (pullback.snd s (spMap (algebraMap K ℂ)))
    (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  have h2 := mem_connectedComponent (x := pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  generalize connectedComponent (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z) = C at h1 h2 hC
  rw [hl] at h1 h2
  exact apply_eq_of_isPreirreducible _ _ (j ⁻¹' C) (hC.preimage j.isOpenEmbedding) z h1 h2 e he

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent : ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  first | exact @GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | exact GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | (intros; apply GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaBaseChange

theorem torsSq_diag {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R)
    (ga : Ix → Rˣ) (t : R) (H : TorsSq deg D t) :
    TorsSq deg (Matrix.diagonal (fun p => (ga p : R)) * D * Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)))
      (t * ((∏ p : {p // Even (deg p)}, (ga p.1 : R)) * ∏ p : {p // ¬ Even (deg p)}, (((ga p.1)⁻¹ : Rˣ) : R)) ^ 2) := by
  obtain ⟨h, h₁, h₂, e, rfl⟩ := H
  set G := Matrix.diagonal (fun p => (ga p : R)) with hG
  set G' := Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)) with hG'
  have hGG : G * G' = 1 := by
    rw [hG, hG', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    simp
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  refine ⟨G * h * G', fun p q hpq => ?_, ?_, e, ?_⟩
  · rw [hG, hG', Matrix.mul_diagonal, Matrix.diagonal_mul, h₁ p q hpq, mul_zero, zero_mul]
  · calc G * D * G' * (G * h * G') + G * h * G' * (G * D * G')
        = G * (D * (G' * G) * h + h * (G' * G) * D) * G' := by noncomm_ring
      _ = 1 := by rw [hGG', Matrix.mul_one, Matrix.mul_one, h₂, Matrix.mul_one, hGG]
  · have e₁ : G * D * G' + G * h * G' = G * (D + h) * G' := by noncomm_ring
    have e₂ : (G * (D + h) * G').submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) =
        Matrix.diagonal (fun p : {p // Even (deg p)} => (ga p.1 : R)) *
          (D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) *
          Matrix.diagonal (fun p : {p // Even (deg p)} => (((ga (e p).1)⁻¹ : Rˣ) : R)) := by
      ext p q
      simp only [hG, hG', Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [e₁, e₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Equiv.prod_comp e (fun p => (((ga p.1)⁻¹ : Rˣ) : R))]
    ring

theorem torsSq_kosD_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R') (c : Fin d → R'ˣ) (t : R)
    (hev : ∀ a k, ev' 0 a k * (c a : R') = f (ev 0 a k)) (H : TorsSq kdeg (kosD m ev) t) :
    TorsSq kdeg (kosD (fun i j j' => (m i j j').map f) ev') (f t * (((∏ a, c a)⁻¹ : R'ˣ) : R') ^ 2) := by
  have H' := torsSq_diag _ _ (Sum.elim (fun _ => 1) (fun a => (c a)⁻¹)) _ (torsSq_map R _ kdeg _ R' f t H)
  convert H' using 2
  · ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    rcases p with p | a <;> rcases q with ⟨I, k⟩ | b
    · simp [kosD, apply_ite f]
    · simp [kosD]
    · by_cases hI : I = ∅
      · subst hI
        have e := hev a k
        simp only [kosD, if_true, Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, _root_.mul_one]
        exact ((Units.eq_mul_inv_iff_mul_eq _).2 e).trans (_root_.mul_comm _ _)
      · simp [kosD, hI]
    · simp [kosD]
  · congr 1
    rw [← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => Even (kdeg p)) (by simp)
        (fun p => ((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ) : R')),
      ← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => ¬ Even (kdeg p)) (by simp)
        (fun p => (((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ)⁻¹ : R'ˣ) : R')),
      Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, ite_self, Finset.prod_const_one, _root_.one_mul]
    simp [kdeg, ← Finset.prod_inv_distrib]

theorem kaForm_map {R R' : Type} [CommRing R] [CommRing R'] (F : Rˣ →* R'ˣ) (g n l l' : ℕ) (t t' J : Rˣ)
    (lam lam' : ℕ → Rˣ) : F (kaForm g n l l' t t' lam lam' J) =
      kaForm g n l l' (F t) (F t') (fun j => F (lam j)) (fun j => F (lam' j)) (F J) := by
  simp only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem kaVal_baseChange : Out.Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (κ : Rˣ), admitted x.P.g n l l' al → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → KaVal x n l l' al s κ → KaVal x' n l l' al s' (Units.map f.toMonoidHom κ) := by
  intro laws R R' _ _ _ _ _ x x' f φ w n l l' al hg s s' κ hadm hx hs hκ
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  obtain ⟨z, ch, b, b₂, t, t₂, J, lam, lam₂, hz, hJ, hb, hb₂, ht, ht₂, rfl⟩ := hκ
  obtain ⟨z', ch', u, hz', hjac, hval⟩ := etZ_baseChange R R' x x' f φ w n _ rfl s s' z ch hx hs hz
  have hex := ((KeyVia.main R R' x x' f).2 φ w hx).1
  have key : ∀ (l : ℕ) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (lam : ℕ → Rˣ) (t : Rˣ),
      x.P.g * n < l →
      (∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j)) → KosVal x l s z ch b t →
      ∃ b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x' (l - j * n),
        (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧
          IsSquareDeterminantComparison x' (l - j * n) (al (l - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧
        KosVal x' l s' z' ch' b' (Units.map f.toMonoidHom t * (∏ a, u a) ^ (-2 * (l : ℤ)) : R'ˣ) := by
    intro l b lam t hl hb ⟨m, hm, ht⟩
    choose b' hb' using fun j k => (hex _ (b j k)).exists
    refine ⟨b', fun j hj => ⟨?_, ?_⟩, fun i j j' => (m i j j').map f, fun i j hj k => ?_, ?_⟩
    · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      exact (GlobalTheory.KeyBasis.main laws R x (l - j * n) (by omega)).2 (b j) (hb j hj).1 R' f x' φ w (b' j) hx (hb' j)
    · exact GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude R R' x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2
    · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      have h₂ : n + (l - (j + 1) * n) = l - j * n := by
        rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
        omega
      exact coords_mul hx h₂ (hs i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
    · have H := torsSq_kosD_map f m
        (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))
        (fun j => Matrix.of fun a k => valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((b' j k).f (ch' a)))
        (fun a => u a ^ (l - 0 * n)) t
        (fun a k => (congrArg _ (Units.val_pow_eq_pow_val _ _)).trans (hval _ (b 0 k) (b' 0 k) a (hb' 0 k))) ht
      have e : (∏ a, u a) ^ (-2 * (l : ℤ)) = (∏ a, u a ^ (l - 0 * n))⁻¹ ^ 2 := by
        rw [Finset.prod_pow, Nat.zero_mul, Nat.sub_zero]
        group
      rw [e]
      exact H
  obtain ⟨c, hc, hct⟩ := key l b lam t hadm.2.1 hb ht
  obtain ⟨c₂, hc₂, hct₂⟩ := key l' b₂ lam₂ t₂ (hadm.2.1.trans hadm.2.2.1) hb₂ ht₂
  refine ⟨z', ch', c, c₂, _, _, Units.map f.toMonoidHom J * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)), _, _,
    hz', ?_, hc, hc₂, hct, hct₂, ?_⟩
  · rw [zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val,
      Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine (Finset.prod_congr rfl fun a _ => hjac a).trans ?_
    rw [← map_prod, ← hJ]
    rfl
  · have H := kaForm_homogeneous R' x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom t₂)
      (Units.map f.toMonoidHom J) (∏ a, u a) 1 1 (fun j => Units.map f.toMonoidHom (lam j))
      (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H
    exact (kaForm_map _ _ _ _ _ _ _ _ _ _).trans H.symm

end GlobalTheory.KaBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariant_baseChange : Out.Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (κ : Rˣ), admitted x.P.g n l l' al → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → KaVal x n l l' al s κ → KaVal x' n l l' al s' (Units.map f.toMonoidHom κ) := by
  first | exact @GlobalTheory.KaBaseChange.kaVal_baseChange | exact GlobalTheory.KaBaseChange.kaVal_baseChange | (intros; apply GlobalTheory.KaBaseChange.kaVal_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.GeomComp

theorem exists_idempotent {A : Type} [CommRing A] [IsNoetherianRing A]
    (h : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q)) (P : Ideal A) [P.IsPrime] :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ P ∧ ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0 := by
  classical
  let z : ∀ (q : Ideal A) [q.IsPrime], Ideal A := fun q _ =>
    RingHom.ker (algebraMap A (Localization.AtPrime q))
  have zp : ∀ (q : Ideal A) [q.IsPrime], (z q).IsPrime := fun q _ =>
    haveI := h q
    RingHom.ker_isPrime _
  have zm : ∀ (q : Ideal A) [q.IsPrime] (a : A), a ∈ z q ↔ ∃ s ∉ q, s * a = 0 := fun q _ a => by
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff q.primeCompl]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, s.2, hs⟩, fun ⟨s, hs, hs'⟩ => ⟨⟨s, hs⟩, hs'⟩⟩
  have zle : ∀ (q r : Ideal A) [q.IsPrime] [r.IsPrime], r ≤ q → z q ≤ r := fun q r _ hr hrq a ha => by
    obtain ⟨s, hs, hs'⟩ := (zm q a).1 ha
    exact (hr.mem_or_mem (hs' ▸ r.zero_mem)).resolve_left fun h => hs (hrq h)
  have htop : z P ⊔ (z P).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    haveI := zp P
    haveI := zp m
    have h1 : z m ≤ z P := zle m (z P) (le_sup_left.trans hle)
    have h2 : z P ≤ z m := zle P (z m) (h1.trans (zle P P le_rfl))
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian (z P)
    have h3 : ∀ a : s, ∃ t ∉ m, t * (a : A) = 0 := fun a =>
      (zm m a).1 (h2 (by rw [← hs]; exact Submodule.subset_span a.2))
    choose t ht ht' using h3
    have h4 : ∏ a, t a ∈ (z P).annihilator := by
      rw [← hs, Submodule.mem_annihilator_span]
      intro a
      obtain ⟨r, hr⟩ : t a ∣ ∏ a, t a := Finset.dvd_prod_of_mem t (Finset.mem_univ _)
      rw [hr, smul_eq_mul, mul_right_comm, ht', zero_mul]
    obtain ⟨a, -, ha⟩ := Ideal.IsPrime.prod_mem_iff.1 (le_sup_right.trans hle h4)
    exact ht a ha
  obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : A) ∈ _)
  have hk : ∀ a ∈ z P, e * a = 0 := fun a ha => Submodule.mem_annihilator.1 he a ha
  have hfP : f ∈ P := zle P P le_rfl hf
  have heP : e ∉ P := fun h' =>
    Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 (hfe ▸ P.add_mem hfP h'))
  refine ⟨e, ?_, heP, fun x y hxy => ?_⟩
  · have := hk f hf
    unfold IsIdempotentElem
    linear_combination e * hfe - this
  · exact ((zp P).mem_or_mem ((zm P _).2 ⟨e, heP, hxy⟩)).imp (hk x) (hk y)

theorem isDomain_away {A : Type} [CommRing A] {e : A} (he : IsIdempotentElem e) (h0 : e ≠ 0)
    (h : ∀ x y : A, e * (x * y) = 0 → e * x = 0 ∨ e * y = 0)
    (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away e S] : IsDomain S := by
  have hz : ∀ a : A, algebraMap A S a = 0 ↔ e * a = 0 := fun a => by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers e)]
    refine ⟨fun ⟨⟨_, n, rfl⟩, hn⟩ => ?_, fun h => ⟨⟨e, Submonoid.mem_powers e⟩, h⟩⟩
    have h1 : e ^ (n + 1) * a = 0 := by
      rw [pow_succ', _root_.mul_assoc]
      exact (congrArg (e * ·) hn).trans (mul_zero _)
    rwa [he.pow_succ_eq] at h1
  have hs := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he (S := S)
  haveI : Nontrivial S := ⟨1, 0, fun h1 => h0 (by simpa using (hz 1).1 (by rw [map_one, h1]))⟩
  haveI : NoZeroDivisors S := ⟨fun {a b} hab => by
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    rw [← map_mul, hz] at hab
    rw [hz, hz]
    exact h x y hab⟩
  exact NoZeroDivisors.to_isDomain S

theorem isDomain_tensor_of_isAlgClosed (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (F : Type) [Field F] [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let f : Spec (.of A) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hi : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral (Spec (.of A)))
  have hg : GeometricallyIntegral f :=
    GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed K (Over.mk f) hf
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := IsIntegral.of_isIso (pullbackSpecIso K F A).hom
  exact (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsDomain (Ω ⊗[k] S)]
    (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem geomInt_away (k Ω B : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing B] [Algebra k B] [Algebra.Smooth k B] (e : B)
    (he : IsIdempotentElem e) (h0 : ((1 : Ω) ⊗ₜ[k] e) ≠ 0)
    (h : ∀ x y : Ω ⊗[k] B, ((1 : Ω) ⊗ₜ[k] e) * (x * y) = 0 →
      ((1 : Ω) ⊗ₜ[k] e) * x = 0 ∨ ((1 : Ω) ⊗ₜ[k] e) * y = 0) :
    GeomInt k (Localization.Away e) := by
  haveI : Algebra.Smooth B (Localization.Away e) := Algebra.Smooth.of_isLocalization_Away e
  haveI : Algebra.Smooth k (Localization.Away e) := Algebra.Smooth.comp k B _
  refine ⟨this, fun F _ _ => ?_⟩
  letI : Algebra (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      (IsScalarTower.toAlgHom k B (Localization.Away e))).toAlgebra
  haveI : IsScalarTower Ω (Ω ⊗[k] B) (Ω ⊗[k] Localization.Away e) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k Ω (Submonoid.powers e)
    (Localization.Away e) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hloc
  have he' : IsIdempotentElem ((1 : Ω) ⊗ₜ[k] e) :=
    he.map (Algebra.TensorProduct.includeRight (R := k) (A := Ω) (B := B))
  haveI : IsLocalization.Away ((1 : Ω) ⊗ₜ[k] e) (Ω ⊗[k] Localization.Away e) := hloc
  haveI := isDomain_away he' h0 h (Ω ⊗[k] Localization.Away e)
  exact isDomain_tensor_of_closure k Ω _ F

theorem geomInt_away_baseChange (K k Ω R : Type) [Field K] [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra K k]
    [Algebra k Ω] [Algebra K Ω] [IsScalarTower K k Ω] [Algebra.IsAlgebraic k Ω] [CommRing R] [Algebra K R]
    [Algebra.Smooth K R] (e : k ⊗[K] R) (he : IsIdempotentElem e)
    (h0 : Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e ≠ 0)
    (h : ∀ x y : Ω ⊗[K] R,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * (x * y) = 0 →
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * x = 0 ∨
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) e * y = 0) :
    GeomInt k (Localization.Away e) := by
  let φ := Algebra.TensorProduct.cancelBaseChange K k Ω Ω R
  have hφ : ∀ x : k ⊗[K] R, φ ((1 : Ω) ⊗ₜ[k] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K k Ω) (AlgHom.id K R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [φ, Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add (f := _), hx, hy]
  refine geomInt_away k Ω (k ⊗[K] R) e he (fun h => h0 ?_) (fun x y hxy => ?_)
  · rw [← hφ, h, map_zero]
  · have h1 := congrArg φ hxy
    rw [map_mul, map_mul, map_zero, hφ] at h1
    refine (h _ _ h1).imp (fun h => φ.injective ?_) (fun h => φ.injective ?_) <;>
      rw [map_mul, map_zero, hφ, h]

theorem exists_finite_level (K C R : Type) [Field K] [Field C] [Algebra K C] [CommRing R] [Algebra K R]
    (Ω : IntermediateField K C) [Algebra.IsAlgebraic K Ω] (x : Ω ⊗[K] R) :
    ∃ (k : IntermediateField K C) (hk : k ≤ Ω) (e : k ⊗[K] R), FiniteDimensional K k ∧
      Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R) e = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, bot_le, 0, inferInstance, map_zero _⟩
  | tmul a r =>
    have ha : _root_.IsIntegral K (a : C) :=
      (Algebra.IsAlgebraic.isAlgebraic a).isIntegral.map Ω.val
    refine ⟨IntermediateField.adjoin K {(a : C)}, by simp,
      ⟨a, IntermediateField.mem_adjoin_simple_self K _⟩ ⊗ₜ r,
      IntermediateField.adjoin.finiteDimensional ha, ?_⟩
    rfl
  | add x y hx hy =>
    obtain ⟨k₁, h₁, e₁, f₁, rfl⟩ := hx
    obtain ⟨k₂, h₂, e₂, f₂, rfl⟩ := hy
    have key : ∀ (a b : IntermediateField K C) (hab : a ≤ b) (hb : b ≤ Ω) (e : a ⊗[K] R),
        Algebra.TensorProduct.map (IntermediateField.inclusion hb) (AlgHom.id K R)
          (Algebra.TensorProduct.map (IntermediateField.inclusion hab) (AlgHom.id K R) e) =
        Algebra.TensorProduct.map (IntermediateField.inclusion (hab.trans hb)) (AlgHom.id K R) e := by
      intro a b hab hb e
      induction e using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine ⟨k₁ ⊔ k₂, sup_le h₁ h₂,
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_left : k₁ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₁ ⊗[K] R →ₐ[K] _) e₁ +
      (Algebra.TensorProduct.map (IntermediateField.inclusion (le_sup_right : k₂ ≤ k₁ ⊔ k₂))
        (AlgHom.id K R) : k₂ ⊗[K] R →ₐ[K] _) e₂,
      inferInstance, ?_⟩
    rw [map_add (f := _), key, key]

theorem exists_geomInt_component : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  intro K _ _ _ R _ _ _ p
  let Ω : IntermediateField K ℂ := algebraicClosure K ℂ
  haveI : IsAlgClosed Ω := (algebraicClosure.isAlgClosure K ℂ).isAlgClosed
  haveI : Algebra.IsAlgebraic K Ω := algebraicClosure.isAlgebraic K ℂ
  haveI hreg : IsRegularRing (Ω ⊗[K] R) := GlobalTheory.isRegularRing_of_smooth Ω _
  let π : Ω ⊗[K] R →ₐ[K] ℂ := Algebra.TensorProduct.lift Ω.val p (fun _ _ => Commute.all _ _)
  haveI : (RingHom.ker π).IsPrime := RingHom.ker_isPrime _
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨e', he', hP, hpr⟩ := exists_idempotent (A := Ω ⊗[K] R)
    (fun q _ => GlobalTheory.isDomain_of_isRegularLocalRing _) (RingHom.ker π)
  obtain ⟨k, hk, e, hfin, rfl⟩ := exists_finite_level K ℂ R Ω e'
  let inc := Algebra.TensorProduct.map (IntermediateField.inclusion hk) (AlgHom.id K R)
  have hinc : Function.Injective inc :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R)
      (IntermediateField.inclusion hk).toLinearMap (IntermediateField.inclusion_injective hk)
  have he : IsIdempotentElem e := hinc (by rw [map_mul]; exact he')
  have hπ : ∀ x, π (inc x) = Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨k, e, hfin, he, ?_, ?_⟩
  · rw [← hπ]
    exact (IsIdempotentElem.iff_eq_zero_or_one.1 (he'.map π)).resolve_left hP
  · letI : Algebra k Ω := (IntermediateField.inclusion hk).toRingHom.toAlgebra
    haveI : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.tower_top (K := K) k
    exact geomInt_away_baseChange K k Ω R e he (fun h => hP (by
      rw [RingHom.mem_ker]
      exact (congrArg π h).trans (map_zero π))) hpr

end GlobalTheory.GeomComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_geom_integral_localization : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  first | exact @GlobalTheory.GeomComp.exists_geomInt_component | exact GlobalTheory.GeomComp.exists_geomInt_component | (intros; apply GlobalTheory.GeomComp.exists_geomInt_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPerLev
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_perLev : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g k : ℕ), P.g = g → ∃ (τ : Matrix (Fin g) (Fin g) ℂ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  rintro hU P g k rfl
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hb, hW⟩ := hU P rig hrig
  let Q : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hrange : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Subtype.range_coe
  have hQ : Function.Injective Q ∧ DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
      Hm.IsHermitian ∧ (∀ z : Fin P.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (Q x) (Q y)).im = Ef x y := by
    refine ⟨Subtype.val_injective, ?_, hrange ▸ u.full, hAH.1, hAH.2.1, fun x y => (hE x y).symm⟩
    have h := u.discrete
    change DiscreteTopology (Set.range Q)
    rw [hrange]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 _ Ef _ Q Hm hQ
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ Ef _ hb h4 h3
  obtain ⟨h, τ, hh, -, -, hs, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ Ef _ bas Q Hm hbas hQ
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = (bas a : Fin P.g → ℂ) := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u ψ.symm (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  refine ⟨τ, fun a => u'.ex ((k : ℂ)⁻¹ • per τ a), rfl, hs, hp, u', fun z => ?_, fun n a b c hn hc => ?_,
    fun _ => rfl⟩
  · rw [hΛ]
    constructor
    · intro hz
      refine ⟨bas.symm ⟨_, hz⟩, ψ.symm.injective ?_⟩
      rw [hψ, LinearEquiv.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      rw [hψ]
      exact (bas a).2
  · rw [hex, hex, map_smul, map_smul, hψ, hψ]
    exact hW n (bas a) (bas b) c hn (by rw [hbas]; exact hc)

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SameCompOfIsHolTo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem sameComp_of_isHolTo : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsPreconnected B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b ∈ B, ∀ b' ∈ B, SameComp s σ (y b) (y b') := by
  intro K _ σ X s m B y hB hc hs hy b hb b' hb'
  classical
  have hs' : ∀ w ∈ B, y w ≫ s = 𝟙 _ ≫ spMap σ := fun w hw => by rw [Category.id_comp]; exact hs w hw
  let c : (Fin m → ℂ) → (Sp ℂ ⟶ pullback s (spMap σ)) := fun w =>
    if h : w ∈ B then pullback.lift (y w) (𝟙 _) (hs' w h) else pullback.lift (y b) (𝟙 _) (hs' b hb)
  have hcw : ∀ w (h : w ∈ B), c w = pullback.lift (y w) (𝟙 _) (hs' w h) := fun w h => dif_pos h
  have h1 : ∀ w ∈ B, c w ≫ pullback.fst s (spMap σ) = y w := fun w h => by rw [hcw w h, pullback.lift_fst]
  have h2 : ∀ w, c w ≫ pullback.snd s (spMap σ) = 𝟙 _ := fun w => by
    by_cases h : w ∈ B
    · rw [hcw w h, pullback.lift_snd]
    · rw [show c w = pullback.lift (y b) (𝟙 _) (hs' b hb) from dif_neg h, pullback.lift_snd]
  have hopen : ∀ U : (pullback s (spMap σ)).Opens, IsOpen {w | w ∈ B ∧ ⊤ ≤ c w ⁻¹ᵁ U} := fun U => by
    refine (GlobalTheory.holFamily_of_isPullback GlobalTheory.valAt'_rules B (IsPullback.of_hasPullback s (spMap σ)) c
      (fun U f => ?_) (fun U f => ?_) U 0).1
    · have e : {w | w ∈ B ∧ ⊤ ≤ (c w ≫ pullback.fst s (spMap σ)) ⁻¹ᵁ U} = {w | w ∈ B ∧ ⊤ ≤ y w ⁻¹ᵁ U} := by
        ext w
        simp only [Set.mem_setOf_eq]
        exact and_congr_right fun h => by rw [h1 w h]
      rw [e]
      exact ⟨(hy U f).1, (hy U f).2.congr fun w hw => by rw [h1 w hw.1]⟩
    · simp only [h2]
      refine ⟨?_, differentiableOn_const _⟩
      by_cases h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
      · simpa only [h, and_true, Set.setOf_mem_eq] using hB
      · simp only [h, and_false, Set.setOf_false, isOpen_empty]
  have hcont : ContinuousOn (fun w => c w (default : PrimeSpectrum ℂ)) B := by
    rw [continuousOn_open_iff hB]
    intro t ht
    convert hopen ⟨t, ht⟩ using 1
    ext w
    simp only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_iff_mem]
    rfl
  refine ⟨hs' b hb, hs' b' hb', fun z => ?_⟩
  obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [← hcw b hb, ← hcw b' hb']
  exact (hc.image _ hcont).subset_connectedComponent ⟨b', hb', rfl⟩ ⟨b, hb, rfl⟩

end GlobalTheory.KeyFam
end
