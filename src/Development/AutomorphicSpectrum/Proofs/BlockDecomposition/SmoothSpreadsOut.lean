module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial

namespace GlobalTheory.CompanionTheory.SmoothSpread

section Witness

variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]

theorem exists_witness [Algebra.FormallySmooth T S] (Q : Algebra.Presentation T S ι σ) :
    ∃ h : ι → Q.Ring, (∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation)) ∧
      ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2 := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  obtain ⟨(τ : S →ₐ[T] MvPolynomial _ T ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (Algebra.FormallySmooth.iff_split_surjection f Q.algebraMap_surjective).mp inferInstance
  have hex (i : _) := Ideal.Quotient.mk_surjective (τ <| Q.val i)
  choose h hh using hex
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = τ.comp (aeval Q.val) :=
    algHom_ext (by simp [hh])
  refine ⟨h, fun i ↦ ?_, fun j ↦ ?_⟩
  · have hs : f (h i) = Q.val i := by
      rw [← AlgHom.kerSquareLift_mk]
      exact hh i ▸ congr($hsig (Q.val i))
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero, hs]
    simp [f]
  · have ho : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (Q.relation j)) = 0 := by
      suffices ho : τ (aeval Q.val (Q.relation j)) = 0 by
        convert! ho
        exact congr($hdiag _)
      simp
    rwa [Ideal.Quotient.eq_zero_iff_mem, hkerf] at ho

theorem formallySmooth_of_witness (Q : Algebra.Presentation T S ι σ) (h : ι → Q.Ring)
    (h1 : ∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation))
    (h2 : ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2) :
    Algebra.FormallySmooth T S := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Surjective f := Q.algebraMap_surjective
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  let g₀ : Q.Ring →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ T _).comp (aeval h)
  have hg₀ : ∀ a ∈ RingHom.ker f.toRingHom, g₀ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span (Set.range Q.relation) := hkerf ▸ ha
    have : Ideal.span (Set.range Q.relation) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have := h2 j
      rw [← hkerf] at this
      exact this
    exact this ha'
  let g : S →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) g₀ hg₀).comp
      (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine Algebra.FormallySmooth.of_split f g ?_
  rw [← AlgHom.cancel_right hf]
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have hgf : g (f (X i)) = Ideal.Quotient.mk _ (h i) := by
    have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i)) = Ideal.Quotient.mk _ (X i) := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ _ g₀ hg₀)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i))) = _
    rw [this]
    change Ideal.Quotient.mk _ (aeval h (X i)) = _
    rw [aeval_X]
  have hfx : f (h i) = f (X i) := by
    have := h1 i
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  simp only [AlgHom.comp_apply, hgf, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk, hfx]

end Witness

section Spread

variable {R₀ R B : Type} [CommRing R₀] [CommRing R] [CommRing B] [Algebra R₀ R] [Algebra R₀ B]

theorem span_range_sq {P : Type} [CommRing P] {σ : Type} (g : σ → P) :
    Ideal.span (Set.range g) ^ 2 = Ideal.span (Set.range fun p : σ × σ ↦ g p.1 * g p.2) := by
  rw [pow_two, Ideal.span_mul_span']
  congr 1
  ext x
  simp only [Set.mem_mul, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩

theorem exists_finite_smooth [Algebra.FinitePresentation R₀ B] [Algebra.Smooth R (R ⊗[R₀] B)] :
    ∃ s : Set R, s.Finite ∧ ∀ A : Subalgebra R₀ R, s ⊆ A → Algebra.Smooth A (A ⊗[R₀] B) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R₀ B
  let Q := P.baseChange R
  obtain ⟨h, h1, h2⟩ := exists_witness Q
  simp_rw [span_range_sq] at h2
  simp_rw [Ideal.mem_span_range_iff_exists_fun] at h1 h2
  choose c hc using h1
  choose d hd using h2
  refine ⟨(⋃ i, ((h i).coeffs : Set R)) ∪ (⋃ i, ⋃ j, ((c i j).coeffs : Set R)) ∪
    (⋃ i, ⋃ j, ((d i j).coeffs : Set R)), ?_, fun A hA ↦ ?_⟩
  · refine .union (.union ?_ ?_) ?_
    · exact Set.finite_iUnion fun i ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
    · exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _
  let M {ι : Type} : MvPolynomial ι A →+* MvPolynomial ι R := MvPolynomial.map (algebraMap A R)
  have hM {ι : Type} : Function.Injective (M (ι := ι)) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  have hMX {ι : Type} (i : ι) : M (X i) = (X i : MvPolynomial ι R) := MvPolynomial.map_X _ _
  have lift {ι : Type} (p : MvPolynomial ι R) (hp : (p.coeffs : Set R) ⊆ A) : ∃ q, M q = p := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦ ?_
    exact ⟨⟨x, hp hx⟩, rfl⟩
  have hh' (i) : ∃ q, M q = h i := lift _ fun x hx ↦
    hA (.inl (.inl (Set.mem_iUnion.mpr ⟨i, hx⟩)))
  have hc' (i j) : ∃ q, M q = c i j := lift _ fun x hx ↦
    hA (.inl (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)))
  have hd' (i j) : ∃ q, M q = d i j := lift _ fun x hx ↦
    hA (.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩))
  choose h' hh' using hh'
  choose c' hc' using hc'
  choose d' hd' using hd'
  let Q' := P.baseChange A
  have hrel (j) : M (Q'.relation j) = Q.relation j := by
    simp [Q, Q', M, Algebra.Presentation.baseChange_relation, MvPolynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have : Algebra.FormallySmooth A (A ⊗[R₀] B) := by
    refine formallySmooth_of_witness Q' h' (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [Ideal.mem_span_range_iff_exists_fun]
      refine ⟨c' i, hM ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_sub, hc', hrel, hh', hMX]
      exact hc i
    · rw [span_range_sq, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨d' j, hM ?_⟩
      have hMa (q : MvPolynomial _ A) : M (aeval h' q) = aeval h (M q) := by
        induction q using MvPolynomial.induction_on with
        | C a => simp [M, MvPolynomial.algebraMap_apply]
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p i hp =>
          simp only [map_mul, aeval_X, hp, hh', hMX]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hd', hrel, hMa, hd j]
  exact ⟨inferInstance, inferInstance⟩

end Spread

section Schemes

theorem smooth_iff_of_isPullback {R₀ T B : Type} [CommRing R₀] [CommRing T] [CommRing B] [Algebra R₀ T]
    [Algebra R₀ B] {U W : Scheme.{0}} (g : U ⟶ Spec (CommRingCat.of R₀)) (e : U ≅ Spec (CommRingCat.of B))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = g)
    {p : W ⟶ U} {q : W ⟶ Spec (CommRingCat.of T)}
    (H : IsPullback p q g (Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))) :
    Smooth q ↔ Algebra.Smooth T (T ⊗[R₀] B) := by
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ T B)).flip
  have H' : IsPullback (p ≫ e.hom) q (Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ T))) :=
    H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [he]) (by simp)
  have hq : (H'.isoIsPullback _ _ sq).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[R₀] B)) = q :=
    IsPullback.isoIsPullback_hom_snd ..
  have : MorphismProperty.RespectsIso @Smooth.{0} := by
    exact MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← hq, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth.{0}), HasRingHomProperty.Spec_iff (P := @Smooth.{0})]
  exact RingHom.smooth_algebraMap (R := T) (S := T ⊗[R₀] B)

theorem exists_finite_chart {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R₀ R] {Y Y₀ U : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)} {π : Y ⟶ Y₀}
    (hlfp : LocallyOfFinitePresentation f₀)
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))))
    (hf : Smooth f) [IsAffine U] (j : U ⟶ Y₀) [IsOpenImmersion j] :
    ∃ s : Set R, s.Finite ∧ ∀ (A : Subalgebra R₀ R), s ⊆ A → ∀ {W : Scheme.{0}} {p : W ⟶ U}
      {q : W ⟶ Spec (CommRingCat.of A)},
      IsPullback p q (j ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))) → Smooth q := by
  let B : Type := Γ(U, ⊤)
  let e : U ≅ Spec (CommRingCat.of B) := U.isoSpec
  let α : CommRingCat.of R₀ ⟶ CommRingCat.of B := Spec.preimage (e.inv ≫ j ≫ f₀)
  have hα : Spec.map α = e.inv ≫ j ≫ f₀ := Spec.map_preimage _
  letI : Algebra R₀ B := α.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = e.inv ≫ j ≫ f₀ := hα
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = j ≫ f₀ := by
    rw [hmap, Iso.hom_inv_id_assoc]
  have hfp : Algebra.FinitePresentation R₀ B := by
    have : LocallyOfFinitePresentation (Spec.map α) := by
      rw [hα]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{0})] at this
    exact this
  have hsm : Algebra.Smooth R (R ⊗[R₀] B) := by
    refine (smooth_iff_of_isPullback (j ≫ f₀) e he
      ((IsPullback.of_hasPullback j π).paste_vert hpb)).mp ?_
    infer_instance
  obtain ⟨s, hs, H⟩ := exists_finite_smooth (R₀ := R₀) (R := R) (B := B)
  refine ⟨s, hs, fun A hA W p q hW ↦ ?_⟩
  have := H A hA
  exact (smooth_iff_of_isPullback (j ≫ f₀) e he hW).mpr this

end Schemes

theorem smooth_spreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f ↦ Smooth f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hfg, hlfp, hqc, hqs, hpb⟩ hsm
  letI : Algebra R₀ R := φ.toAlgebra
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have hch (i : 𝒰.I₀) := exists_finite_chart (R := R) (R₀ := R₀) hlfp hpb hsm (𝒰.f i)
  choose s hs H using hch
  have : Finite 𝒰.I₀ := by
    change Finite Y₀.affineCover.finiteSubcover.I₀
    infer_instance
  let A : Subalgebra R₀ R := Algebra.adjoin R₀ (⋃ i, s i)
  have hAfg : A.FG := ⟨(Set.finite_iUnion hs).toFinset, by simp [A]⟩
  have hft : Algebra.FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  refine ⟨A, inferInstance, algebraMap R₀ A, algebraMap A R, rfl, Algebra.FiniteType.trans hfg hft, ?_⟩
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0})
    (𝒰.pullback₁ (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))))) fun i ↦ ?_
  exact H i A (fun x hx ↦ Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, hx⟩))
    ((IsPullback.of_hasPullback _ (𝒰.f i)).flip.paste_vert (IsPullback.of_hasPullback _ _))

end GlobalTheory.CompanionTheory.SmoothSpread
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOutStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
alias GlobalTheory.T.smooth_spreads_out := GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompIdeal

theorem mem_compI_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S,
    x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  intro S _ P hP x
  constructor
  · intro hx
    unfold compI Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨hi, haP⟩ := ha
      refine ⟨1 - a, hi.one_sub, fun h => hP.ne_top ?_, ?_⟩
      · exact (Ideal.eq_top_iff_one P).2 (by simpa using P.add_mem h haP)
      · rw [sub_mul, one_mul, hi.eq, sub_self]
    | zero => exact ⟨1, IsIdempotentElem.one, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h), mul_zero 1⟩
    | add a b _ _ iha ihb =>
      obtain ⟨e, he, heP, hea⟩ := iha
      obtain ⟨f, hf, hfP, hfb⟩ := ihb
      refine ⟨e * f, he.mul hf, fun h => (hP.mem_or_mem h).elim heP hfP, ?_⟩
      calc e * f * (a + b) = f * (e * a) + e * (f * b) := by ring
        _ = 0 := by rw [hea, hfb, mul_zero, mul_zero, add_zero]
    | smul s a _ ih =>
      obtain ⟨e, he, heP, hea⟩ := ih
      refine ⟨e, he, heP, ?_⟩
      calc e * s • a = s * (e * a) := by rw [smul_eq_mul]; ring
        _ = 0 := by rw [hea, mul_zero]
  · rintro ⟨e, he, heP, hex⟩
    have h0 : e * (1 - e) ∈ P := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact P.zero_mem
    have h1 : 1 - e ∈ P := (hP.mem_or_mem h0).resolve_left heP
    have h2 : x = x * (1 - e) := by
      rw [mul_sub, mul_one, mul_comm x e, hex, sub_zero]
    rw [h2]
    exact Ideal.mul_mem_left _ x (Ideal.subset_span ⟨he.one_sub, h1⟩)

end GlobalTheory.CompanionTheory.CompIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIffStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
alias GlobalTheory.T.mem_idempotent_complement_iff := GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInduction
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem glue_idempotent_property :
    ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) →
      (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' →
        Q (e + e')) →
      (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  intro S _ Q h0 hmul hadd hloc
  let I : Ideal S :=
    { carrier := {x | ∃ e : S, IsIdempotentElem e ∧ Q e ∧ e * x = x}
      zero_mem' := ⟨0, IsIdempotentElem.zero, h0, by simp⟩
      add_mem' := by
        rintro x y ⟨e, he, hQe, hex⟩ ⟨e', he', hQe', hey⟩
        have hee : e * e = e := he
        have hee' : e' * e' = e' := he'
        have h1e : IsIdempotentElem (1 - e) := he.one_sub
        have hg : IsIdempotentElem (e' * (1 - e)) :=
          IsIdempotentElem.mul he' h1e
        have horth : e * (e' * (1 - e)) = 0 := by
          have : e * (e' * (1 - e)) = e' * (e - e * e) := by ring
          rw [this, hee]; simp
        refine ⟨e + e' * (1 - e), ?_, hadd e _ he hg horth hQe (hmul e' _ he' h1e hQe'), ?_⟩
        · show (e + e' * (1 - e)) * (e + e' * (1 - e)) = e + e' * (1 - e)
          have hg' : (e' * (1 - e)) * (e' * (1 - e)) = e' * (1 - e) := hg
          have : (e + e' * (1 - e)) * (e + e' * (1 - e))
              = e * e + 2 * (e * (e' * (1 - e))) + (e' * (1 - e)) * (e' * (1 - e)) := by ring
          rw [this, hee, horth, hg']; simp
        · have h1 : (e + e' * (1 - e)) * x = x := by
            have : (e + e' * (1 - e)) * x = e * x + e' * (x - e * x) := by ring
            rw [this, hex]; simp
          have h2 : (e + e' * (1 - e)) * y = y := by
            have : (e + e' * (1 - e)) * y = e * y + (e' * y) - e * (e' * y) := by ring
            rw [this, hey]; ring
          rw [mul_add, h1, h2]
      smul_mem' := by
        rintro c x ⟨e, he, hQe, hex⟩
        refine ⟨e, he, hQe, ?_⟩
        show e * (c * x) = c * x
        calc e * (c * x) = c * (e * x) := by ring
          _ = c * x := by rw [hex]  }
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨e, he, hem, hQ⟩ := hloc m hm
    exact hem (hIm ⟨e, he, hQ, by rw [show e * e = e from he]⟩)
  have h1 : (1 : S) ∈ I := by rw [htop]; exact Submodule.mem_top
  obtain ⟨e, _, hQ, he1⟩ := h1
  have : e = 1 := by simpa using he1
  exact this ▸ hQ

end GlobalTheory.CompanionTheory.Idem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInductionStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
alias GlobalTheory.T.idempotent_local_induction := GlobalTheory.CompanionTheory.Idem.glue_idempotent_property
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLift
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectQuotient

theorem exists_frobenius_iterate (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (k : ℕ) : ∃ f : R →+* R, ∀ x, f x = x ^ p ^ k := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact ⟨RingHom.id R, fun x => Subsingleton.elim _ _⟩
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
    exact ⟨iterateFrobenius R p k, fun x => iterateFrobenius_def p k x⟩

theorem solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  intro p _ A _ S _ _ B _ _ i I m n a c hp hPQ hS
  obtain ⟨y, hy⟩ := hS
  have hpS : (p : S) = 0 := by
    have := congrArg (algebraMap A S) hp
    simpa using this
  choose k₀ x hx using fun j => hPQ.pow (y j)
  obtain ⟨K, hK⟩ : ∃ K, K = Finset.univ.sup k₀ := ⟨_, rfl⟩
  let s : Fin n → S := fun j => x j ^ p ^ (K - k₀ j)
  have hs : ∀ j, y j ^ p ^ K = i (s j) := by
    intro j
    have hle : k₀ j ≤ K := hK ▸ Finset.le_sup (Finset.mem_univ j)
    have hpow : p ^ K = p ^ k₀ j * p ^ (K - k₀ j) := by
      rw [← pow_add]; congr 1; omega
    have hxj : y j ^ p ^ k₀ j = i (x j) := hx j
    rw [hpow, pow_mul, hxj]
    simp [s, map_pow]
  obtain ⟨fB, hfB⟩ := exists_frobenius_iterate p B hPQ.pf.char K
  have he : ∀ t, i (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) = 0 := by
    intro t
    have h1 := congrArg fB (hy t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    have h2 : ∀ j, fB (a t j • y j) = a t j ^ p ^ K • i (s j) := by
      intro j
      rw [hfB, smul_pow, hs]
    simp only [h2] at h1
    rw [hfB, ← map_pow] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes, sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun j _ => map_smul i _ _
  choose k₁ hk₁ using fun t => (hPQ.ker _).1 (he t)
  obtain ⟨L, hL⟩ : ∃ L, L = Finset.univ.sup k₁ := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ := exists_frobenius_iterate p S hpS L
  refine ⟨K + L, fun j => s j ^ p ^ L, fun t => ?_⟩
  have hle : k₁ t ≤ L := hL ▸ Finset.le_sup (Finset.mem_univ t)
  have hpow : p ^ L = p ^ k₁ t * p ^ (L - k₁ t) := by
    rw [← pow_add]; congr 1; omega
  have hmem : (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) ^ p ^ L ∈ I := by
    rw [hpow, pow_mul]
    exact I.pow_mem_of_mem (hk₁ t) _ (pow_pos (Fact.out : p.Prime).pos _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hfS, map_sub, map_sum] at hmem
  have h3 : ∀ j, fS (a t j ^ p ^ K • s j) = a t j ^ p ^ (K + L) • s j ^ p ^ L := by
    intro j
    rw [hfS, smul_pow, ← pow_mul, ← pow_add]
  simp only [h3] at hmem
  rw [hfS, ← map_pow, ← pow_mul, ← pow_add] at hmem
  exact hmem

end GlobalTheory.CompanionTheory.PerfectQuotient
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLiftStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
alias GlobalTheory.T.frobenius_power_solution_lift := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeMinor

theorem det_mul_submatrix_expand {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_sz {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_nF {K ι κ : Type} [NormedField K] [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : κ → ι) : ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

theorem norm_minor_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp

theorem nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))

theorem nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]

theorem nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id

theorem mulF : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩

end GlobalTheory.CompanionTheory.WedgeMinor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlacesStatement
open Matrix PositivityTheory.Rg.BcB.D1
alias GlobalTheory.T.multiplicativity_finite_places := GlobalTheory.CompanionTheory.WedgeMinor.mulF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.GramWedge

theorem star_dotProduct_self {α : Type} [Fintype α] (w : α → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using Complex.conj_mul' (w i)

theorem norm_entry_le_sz {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (a : ι') (b : ι) :
    ‖g a b‖ ≤ sz g :=
  le_ciSup (f := fun p : ι' × ι => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (a, b)

theorem sum_norm_mulVec_sq_le {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
  have row : ∀ a, ‖(g *ᵥ v) a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    intro a
    have h1 : ‖(g *ᵥ v) a‖ ≤ sz g * ∑ b, ‖v b‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_entry_le_sz g a b) (norm_nonneg _)
    have h2 : (∑ b, ‖v b‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖)
    calc ‖(g *ᵥ v) a‖ ^ 2 ≤ (sz g * ∑ b, ‖v b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = sz g ^ 2 * (∑ b, ‖v b‖) ^ 2 := mul_pow _ _ _
      _ ≤ sz g ^ 2 * ((Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ a, ‖(g *ᵥ v) a‖ ^ 2
      ≤ ∑ _a : ι', (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := Finset.sum_le_sum fun a _ => row a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem posSemidef_smul_gram_sub {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by
  set c : ℝ := (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 with hc
  have hG : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  have hH : ((g * A)ᴴ * (g * A)).IsHermitian := isHermitian_conjTranspose_mul_self _
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG.smul (show star (c : ℂ) = c from Complex.conj_ofReal c)).sub hH) fun x => ?_
  have e : ∀ {α : Type} [Fintype α] (B : Matrix α κ ℂ),
      star x ⬝ᵥ ((Bᴴ * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro α _ B
    rw [← mulVec_mulVec, star_mulVec, dotProduct_mulVec]
  have e1 := e A
  have e2 : star x ⬝ᵥ (((g * A)ᴴ * (g * A)) *ᵥ x) = star (g *ᵥ (A *ᵥ x)) ⬝ᵥ (g *ᵥ (A *ᵥ x)) := by
    rw [e (g * A), mulVec_mulVec]
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, e1, e2, star_dotProduct_self,
    star_dotProduct_self, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (sub_nonneg.2 (sum_norm_mulVec_sq_le g (A *ᵥ x)))

theorem gram_mul_det {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (s : Matrix κ κ ℂ) :
    ((A * s)ᴴ * (A * s)).det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) * (Aᴴ * A).det := by
  have h : star s.det * s.det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' s.det
  rw [conjTranspose_mul, show sᴴ * Aᴴ * (A * s) = sᴴ * (Aᴴ * A) * s by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    det_mul, det_mul, det_conjTranspose, ← h]
  ring

theorem mulI_of_detMono : DetMono → MulI := by
  intro hm ι ι' κ _ _ _ _ A
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩
  · have h := hm κ _ _ (posSemidef_conjTranspose_mul_self (g * A)) (posSemidef_smul_gram_sub g A)
    rw [det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
    exact h
  · simp only [nI]
    rw [gram_mul_det, Complex.re_ofReal_mul, mul_comm]
  · have h := gram_mul_det (1 : Matrix κ κ ℂ) s
    simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, det_one, mul_one] at h
    simp only [nI]
    rw [h, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.GramWedge

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlacesStatement
open Matrix PositivityTheory.Rg.BcB.D1
alias GlobalTheory.T.multiplicativity_infinite_places := GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
noncomputable section

open Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.Jp.Unif

theorem integral_coset {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (c : G ⧸ N → ℂ) :
    ∫ x, c (QuotientGroup.mk (ρ x)) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u, c u := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hS : ∀ u : G ⧸ N, ∃ y : X, {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} =
      (fun x => y * x) ⁻¹' (ρ ⁻¹' (N : Set G)) := by
    intro u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, hy⟩ := hρ g⁻¹
    refine ⟨y, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, map_mul, hy]
    rw [eq_comm, QuotientGroup.eq]
  choose y hy using hS
  have hmeas : ∀ u : G ⧸ N, MeasurableSet {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} := by
    intro u
    rw [hy u]
    exact hN.preimage (measurable_const_mul (y u))
  have hmeasure : ∀ u : G ⧸ N,
      ν.real {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} = ν.real (ρ ⁻¹' (N : Set G)) := by
    intro u
    rw [hy u]
    show (ν _).toReal = (ν _).toReal
    rw [measure_preimage_mul]
  have hdecomp : (fun x => c (QuotientGroup.mk (ρ x))) = fun x =>
      ∑ u, Set.indicator {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} (fun _ => c u) x := by
    funext x
    rw [Finset.sum_eq_single (QuotientGroup.mk (ρ x) : G ⧸ N)]
    · exact (Set.indicator_of_mem (show x ∈ {x' : X | (QuotientGroup.mk (ρ x') : G ⧸ N) =
        QuotientGroup.mk (ρ x)} from rfl) (fun _ => c (QuotientGroup.mk (ρ x)))).symm
    · intro u _ hu
      exact Set.indicator_of_notMem (by intro h; exact hu (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [finsum_eq_sum_of_fintype, hdecomp, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [integral_indicator_const _ (hmeas u), hmeasure u, Complex.real_smul]
  · intro u _
    exact (integrable_const (c u)).indicator (hmeas u)

theorem integral_level {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (φ : G → ℂ)
    (hφ : ∀ κ, ∀ γ ∈ N, φ (κ * γ) = φ κ) :
    ∫ x, φ (ρ x) ∂ν = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hone : ∫ _x, (1 : ℂ) ∂ν = 1 := by simp
  have hsum : ∑ᶠ _u : G ⧸ N, (1 : ℂ) = (Nat.card (G ⧸ N) : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
      nsmul_eq_mul, mul_one]
  have h1 : ∫ _x, (1 : ℂ) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ _u : G ⧸ N, (1 : ℂ) :=
    GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun _ => 1)
  rw [hone, hsum] at h1
  have hA : (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) = (Nat.card (G ⧸ N) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  calc ∫ x, φ (ρ x) ∂ν = ∫ x, φ (Quotient.out (QuotientGroup.mk (ρ x) : G ⧸ N)) ∂ν := by
        congr 1
        funext x
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (ρ x)
        rw [hh, hφ _ _ h.2]
    _ = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) :=
        GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun u => φ (Quotient.out u))
    _ = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by rw [hA]

theorem finite_quot_sq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) : Finite (O ⧸ Ideal.span {ϖ ^ 2}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Finite.of_fintype (IsLocalRing.ResidueField O)
  rw [← Ideal.span_singleton_pow, ← hm]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) 2

theorem finite_quotient_level_square_congruence {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) {ϖ : O} (hϖ : Irreducible ϖ) :
    Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := by
  haveI := GlobalTheory.CompanionTheory.Jp.Unif.finite_quot_sq hϖ
  haveI : Finite (Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    inferInstanceAs (Finite (GlobalTheory.CompanionTheory.Jp.Ix n → GlobalTheory.CompanionTheory.Jp.Ix n → O ⧸ Ideal.span {ϖ ^ 2}))
  haveI : Finite (GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    Finite.of_injective (fun g : GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) =>
      (g : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))
      (fun _ _ h => Units.ext h)
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :
      GL (GlobalTheory.CompanionTheory.Jp.Ix n) O →* GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))

theorem jpUnif : JpUnif := by
  intro O _ _ _ _ n ϖ hϖ X _ _ _ ν _ _ ρ hρ hN φ hφ
  haveI := finite_quotient_level_square_congruence n hϖ
  exact integral_level ν (Gam2 (n := n) ϖ) ρ hρ hN φ hφ

end GlobalTheory.CompanionTheory.Jp.Unif

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatementStatement
open GlobalTheory.CompanionTheory.Jp
alias GlobalTheory.T.uniform_boundedness_statement := GlobalTheory.CompanionTheory.Jp.Unif.jpUnif
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem coface_rel (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)) :
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := by
  have key : ∀ j : Fin n,
      (k.succAbove i).succAbove ((i.predAbove k).succAbove j) = k.succAbove (i.succAbove j) :=
    fun j => Fin.succAbove_succAbove_succAbove_predAbove k i j
  apply AlgHom.coe_ringHom_injective
  refine (hwp n).uniq (K (n + 1 + 1)) _ _ ?_ ?_
  · rw [AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]
  · intro j
    have h1 : ((δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k))).comp (ι n j)
        = ((δ (n + 1) k).comp (δ n i)).comp (ι n j) := by
      rw [AlgHom.comp_assoc, hδ, hδ, AlgHom.comp_assoc, hδ, hδ, key]
    ext x
    exact AlgHom.congr_fun h1 x

end GlobalTheory.CompanionTheory.WpCoface
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlatten
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.Comb

theorem interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm_flatten {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)

end GlobalTheory.CompanionTheory.Comb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlattenStatement
open Zc.Comb
universe u
alias GlobalTheory.T.perm_flatten_of_shuffle := GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten
end
end
