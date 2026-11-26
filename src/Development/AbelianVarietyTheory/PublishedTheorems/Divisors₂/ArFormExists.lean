module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def ArFormExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

namespace GlobalTheory.Published

def LanglandsSquareIntegrable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (IsSqIntOn σ J X Y T φ ↔ ∀ S, T ⊆ S → ∀ s, IsCuspExp σ J X Y S K φ s → NegExp S T s)

def LanglandsLemmaUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
          ∀ (T : Finset (Fin r)) (φ : GAd σ J → ℂ), IsAutOn σ J X Y T K φ →
            (∀ S, T ⊆ S → ∃! φc, IsCuspComp σ J X Y S K φ φc) ∧
            ((∀ S, T ⊆ S → IsCuspComp σ J X Y S K φ 0) → φ = 0) ∧
            (φ ≠ 0 → ∃ S, T ⊆ S ∧ ∃ s, IsCuspExp σ J X Y S K φ s)

def AutomorphicFormsUnitary : Prop := LanglandsSquareIntegrable ∧ LanglandsLemmaUnitary

end GlobalTheory.Published

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ}

theorem isSqInt_iff (H : GlobalTheory.Published.LanglandsSquareIntegrable) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (hK : IsMaxCpt σ J K) (hφ : IsAut σ J K φ) :
    IsSqInt σ J φ ↔ ∀ S s, IsCuspExp σ J X Y S K φ s → ∀ k ∈ S, ∑ i with i ≤ k, (s i).re < 0 := by
  simpa only [isSqIntOn_empty, negExp_empty, Finset.empty_subset, forall_const] using
    H F E σ h n J hJ r X Y hW K hK ∅ φ (isAutOn_empty.2 hφ)


end GlobalTheory.StdPar

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published


open GlobalTheory.EisLine in
def EisensteinResidueLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
      ∃ R : ℂ, R ≠ 0 ∧ ∀ g : GAd σ J,
        Tendsto (fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : T, (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
          (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)) (𝓝 R)

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.CA (IsCM)
open GlobalTheory.Adelic (cutIdeal mem_support_cutIdeal)
open GlobalTheory.QCoh GlobalTheory.Vanishing RingTheory.Sequence

namespace GlobalTheory.Published

def ProperIntersectionLength : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (D : ℕ), IsProjOver f →
    topologicalKrullDim X = D → ∀ (L : LB X) (hL : L.IsLB) (s : Fin D → L.Sec),
    ((cutIdeal hL s).support : Set X).Finite →
    (∀ y ∈ (cutIdeal hL s).support, IsCM (X.presheaf.stalk y)) →
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤)

end GlobalTheory.Published

namespace GlobalTheory.ProperCut

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k)

theorem ringKrullDim_stalk_eq [IsIntegral X] [LocallyOfFiniteType f] {x : X} (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_stalk_eq_coheight]
    exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge
  obtain ⟨A, _, _, _, _, _, j, _, ⟨q, rfl⟩, -, hA⟩ := exists_affine_chart_trdeg_eq f x
  obtain ⟨d, -, hd⟩ := exists_ringKrullDim_eq_and_trdeg_eq k A
  have hq : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 (by
    have := hx.preimage j.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ j.isOpenEmbedding.injective] at this)
  rw [ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of A) q).commRingCatIsoToRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal),
    ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field d hd]
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨B, _, _, _, _, _, i, _, hy, -, hB⟩ := exists_affine_chart_trdeg_eq f y
  refine ⟨_, i.isOpenEmbedding.isOpen_range, hy, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
  exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := B)).trans
    (ringKrullDim_eq_of_trdeg_eq k B (hB.trans (hA.symm.trans hd)))).le

theorem discreteTopology_subscheme [LocallyOfFiniteType f] (I : X.IdealSheafData) (h : (I.support : Set X).Finite) :
    Finite I.subscheme ∧ DiscreteTopology I.subscheme := by
  have : Finite I.subscheme := Set.finite_univ_iff.1 <| Set.Finite.of_finite_image
    (by rwa [Set.image_univ, I.range_subschemeι]) I.subschemeι.isClosedEmbedding.injective.injOn
  have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ f)
  exact ⟨‹_›, JacobsonSpace.discreteTopology (Set.toFinite _)⟩

theorem isClosed_singleton_of_finite [LocallyOfFiniteType f] (I : X.IdealSheafData) (h : (I.support : Set X).Finite)
    {y : X} (hy : y ∈ I.support) : IsClosed ({y} : Set X) := by
  obtain ⟨z, rfl⟩ := exists_ι_eq hy
  have := (discreteTopology_subscheme f I h).2
  simpa using I.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete {z})

theorem residueDegree_of_isClosedImmersion {Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) :
    i.residueDegree y = 1 := by
  letI := (i.residueFieldMap y).hom.toAlgebra
  refine Module.finrank_of_bijective_algebraMap ⟨(i.residueFieldMap y).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Y.residue_surjective y a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective y b
  exact ⟨X.residue _ c, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i y) c⟩

theorem topSelf_eq_length {D : ℕ} (hf : IsProjOver f) {L : LB X} (hL : L.IsLB) (s : Fin D → L.Sec)
    (hfin : ((cutIdeal hL s).support : Set X).Finite)
    (hCM : ∀ y ∈ (cutIdeal hL s).support, IsCM (X.presheaf.stalk y))
    (hD : ∀ y ∈ (cutIdeal hL s).support, (D : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk y)) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤) := by
  classical
  letI := algebraΓOfHom f
  letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
  have := isNoetherian_of_isProjOver hf
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  have hker : ∀ (z : (cutIdeal hL s).subscheme) (c : L.ι) (hc : (cutIdeal hL s).subschemeι z ∈ L.U c),
      Ideal.ofList (List.ofFn fun i => X.presheaf.germ (L.U c) _ hc ((s i).f c)) =
        RingHom.ker ((cutIdeal hL s).subschemeι.stalkMap z).hom := fun z c hc =>
    (ofList_ofFn_eq_span_range _).trans ((ker_stalkMap _ z).trans (stalkId_cutIdeal hL s c _ hc)).symm
  have hmem := mem_support_cutIdeal hL s
  generalize cutIdeal hL s = I at *
  obtain ⟨_, _⟩ := discreteTopology_subscheme f I hfin
  letI := Fintype.ofFinite I.subscheme
  have hV : topologicalKrullDim I.subscheme ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : IsLocallyArtinian I.subscheme := .of_topologicalKrullDim_le_zero hV
  have : IsArtinianScheme I.subscheme := {}
  have hfi : IsFinite (I.subschemeι ≫ f) :=
    have : LocallyQuasiFinite (I.subschemeι ≫ f) := .of_finite_preimage_singleton _ fun _ => Set.toFinite _
    .of_locallyQuasiFinite _
  have hs : suppDim (QCoh.structureModule I.subscheme) ≤ 0 := suppDim_structureModule.trans_le hV
  have hlen : ∀ z : I.subscheme, IsFiniteLength (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) :=
    fun z => (structureModuleStalkEquiv z).isFiniteLength (isFiniteLength_stalk hs z)
  have hreg : ∀ y ∈ I.support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c)) := by
    intro y hy c hc
    obtain ⟨z, rfl⟩ := exists_ι_eq hy
    refine isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le (hCM _ hy) (fun a ha => ?_) ?_
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) ((hker z c hc).le (Ideal.subset_span ha))
    · have : IsArtinianRing (I.subscheme.presheaf.stalk z) :=
        (isFiniteLength_iff_isNoetherian_isArtinian.1 (hlen z)).2
      rw [hker, ringKrullDim_eq_of_ringEquiv
        (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z)),
        ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance, zero_add, List.length_ofFn]
      exact hD _ hy
  have hsum : topSelfIntersection k L D = (∑ z : I.subscheme, (I.subschemeι ≫ f).residueDegree z *
      (Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z)).toNat : ℕ) := by
    choose c hc using Semi.LB.mem_of_cover hL
    have key := CutDegree.interNum_eq_sum_length f hf hL c hc (Finset.univ.image I.subschemeι) (fun x hx => ?_)
      (List.ofFn s) (structureModule X) (fun x _ hx => ?_) fun x hx => ?_
    · have e : topSelfIntersection k L D = topSelfIntersection k L (List.ofFn s).length := by rw [List.length_ofFn]
      rw [e, topSelf_def, key, Finset.sum_image I.subschemeι.isClosedEmbedding.injective.injOn]
      refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
      rw [CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion I.subschemeι, mul_one,
        mul_comm, List.map_ofFn]
      refine congrArg (_ * ENat.toNat ·) ?_
      letI := (I.subschemeι.stalkMap z).hom.toAlgebra
      rw [← Module.length_eq_of_surjective (S := X.presheaf.stalk (I.subschemeι z))
        (I.subschemeι.stalkMap_surjective z)]
      refine (Submodule.Quotient.equiv _ (LinearMap.ker (Algebra.linearMap _ (I.subscheme.presheaf.stalk z)))
        (structureModuleStalkEquiv _) ?_).length_eq.trans
        (LinearMap.quotKerEquivOfSurjective _ (I.subschemeι.stalkMap_surjective z)).length_eq
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, smul_eq_mul, Ideal.mul_top]
      exact hker z _ _
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
      exact isClosed_singleton_of_finite f I hfin (ι_mem_support I z)
    · obtain ⟨z, rfl⟩ := exists_ι_eq ((hmem x).2 fun i => hx _ (List.mem_ofFn.2 ⟨i, rfl⟩))
      exact Finset.mem_image_of_mem _ (Finset.mem_univ z)
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
      rw [List.map_ofFn]
      exact ((structureModuleStalkEquiv _).isWeaklyRegular_congr _).2
        (hreg _ (ι_mem_support I z) _ _).toIsWeaklyRegular
  refine ⟨hfi, hreg, fun z => Module.length_ne_top_iff.2 (hlen z), by rw [finsum_eq_sum_of_fintype, hsum],
    ((I.subschemeι ≫ f).finite_appTop).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2), ?_⟩
  rw [hsum, ← ((coh.zeroUnitEquiv I.subscheme).restrictScalars k).finrank_eq]
  refine congrArg _ (Eq.trans ?_ (hdim_zero_eq_sum_toNat (I.subschemeι ≫ f) hs (S := Finset.univ) (by simp)).symm)
  exact Finset.sum_congr rfl fun z _ => by rw [mul_comm, (structureModuleStalkEquiv z).length_eq]

theorem isCM_stalk_of_smooth {D : ℕ} (hd : SmoothOfRelativeDimension D f) {y : X} (hy : IsClosed ({y} : Set X)) :
    IsCM (X.presheaf.stalk y) := by
  have := (StabFlat.stalk_of_smooth_local k X f D hd y hy _ (Spec.map_preimage _).symm inferInstance).2.2.1
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at this
  have := IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk y))
  exact isCM_of_isRegularLocalRing _

theorem topSelf_eq_length_of_smooth {D : ℕ} (hd : SmoothOfRelativeDimension D f) (hf : IsProjOver f) {L : LB X}
    (hL : L.IsLB) (s : Fin D → L.Sec) (hfin : ((cutIdeal hL s).support : Set X).Finite) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤) := by
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  exact topSelf_eq_length f hf hL s hfin
    (fun y hy => isCM_stalk_of_smooth f hd (isClosed_singleton_of_finite f _ hfin hy))
    fun y hy => (CutDegree.ringKrullDim_stalk hd (isClosed_singleton_of_finite f _ hfin hy)).ge

end GlobalTheory.ProperCut

namespace GlobalTheory.Published

theorem ProperIntersectionLength_holds : ProperIntersectionLength := fun _ _ _ _ f _ hf hd _ hL s hfin hCM =>
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  ProperCut.topSelf_eq_length f hf hL s hfin hCM fun _ hy =>
    ((ProperCut.ringKrullDim_stalk_eq f (ProperCut.isClosed_singleton_of_finite f _ hfin hy)).trans hd).ge

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.Published

def SerreHolomorphicSections : Prop :=
  ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p →
    ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB →
      Function.Bijective fun s : B.Sec =>
        (⟨secVal p (RingHom.id ℂ) s, R.secVal_mem_holSec s⟩ : R.holSec B)

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {q : Y' ⟶ Sp k'}
  {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D D' : ℕ} {m : CxPts q τ → CxPts p σ} {B : LB Y}


variable (r m B) in
def pullVal : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] ((B.pull r).ι → CxPts q τ → ℂ) where
  toFun s J z := s (J PUnit.unit) (m z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullVal_injective (hb : Function.Surjective m) : Function.Injective (pullVal r m B) :=
  fun _ _ h => funext₂ fun i y => by
    obtain ⟨z, rfl⟩ := hb y
    exact congrFun₂ h (fun _ => i) z

theorem mem_ptsIn_pull (hm : ∀ z, (m z).1 = z.1 ≫ r) {J : (B.pull r).ι} {z : CxPts q τ} :
    z ∈ ptsIn q τ ((B.pull r).U J) ↔ m z ∈ ptsIn p σ (B.U (J PUnit.unit)) := by
  rw [← mem_ptsIn_preimage hm, mem_ptsIn, mem_ptsIn]
  exact mem_pull

theorem pullVal_mem_holSec (hm : ∀ z, (m z).1 = z.1 ≫ r) {R : AnRead p σ D} (R' : AnRead q τ D')
    {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ R.holSec B) : pullVal r m B s ∈ R'.holSec (B.pull r) := by
  refine ⟨⟨fun J J' z h h' => ?_, fun J z h => hs.1.2 _ _ (mt (mem_ptsIn_pull hm).2 h)⟩, fun J =>
    ((hs.2 _).comp_map (isOpen_ptsIn _) hm R').mono fun _ hz => (mem_ptsIn_pull hm).1 hz⟩
  rw [gv_linComb (m := fun _ => m z) (fun _ => hm z) h h', Fintype.prod_unique, zpow_one]
  exact hs.1.1 _ _ _ ((mem_ptsIn_pull hm).1 h) ((mem_ptsIn_pull hm).1 h')

theorem cval_pullChart_ofSec {ρ : k →+* k'} (hm : ∀ z, (m z).1 = z.1 ≫ r) (w : r ≫ p = q ≫ spMap ρ)
    (s : B.Sec) : cval τ (pullChart (W := ⊤) (GlobalTheory.chartPullPull B r) w le_top (H0.ofSec p ⊤ s)) =
      pullVal r m B (secVal p σ s) := funext₂ fun J z => by
  by_cases h : z ∈ ptsIn q τ ((B.pull r).U J)
  · rw [cval_pullChart hm _ _ _ h, cval_ofSec]
    rfl
  · exact ((cval_mem _ _).2 _ _ h).trans ((secVal_mem s).2 _ _ (mt (mem_ptsIn_pull hm).2 h)).symm

end BaseChange

theorem SerreHolomorphicSections.bijective_valC (h : SerreHolomorphicSections) {F : Type} [Field F]
    {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ} [SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) : Function.Bijective (R.valC B) := by
  let := σ.toAlgebra
  have H := IsPullback.of_hasPullback p (spMap σ)
  generalize Limits.pullback.fst p (spMap σ) = r at H
  generalize Limits.pullback.snd p (spMap σ) = q at H
  have hq := ProjSpace.isProjOver_of_isPullback_spMap σ H hp
  have hs : SmoothOfRelativeDimension D q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange D
    MorphismProperty.of_isPullback H ‹SmoothOfRelativeDimension D p›
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts q (RingHom.id ℂ) → CxPts p σ, (∀ z, (m z).1 = z.1 ≫ r) ∧
      Function.Surjective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, (bijective_bcMap H _).2⟩
  have hB' := LB.isLB_pull hB r
  have hS := h _ q D hs hq (AnRead.all _ _ D) _ hB'
  have hE := isExtension_pullChart_top (k := F) (E := ℂ) H hB hB' (GlobalTheory.chartPullPull B r) hp hq
  set ι := pullChart (O := ⊤) (W := ⊤) (GlobalTheory.chartPullPull B r) H.w le_top
  let L : SecC p σ B →ₗ[ℂ] H0 q (B.pull r) ⊤ :=
    SecC.lift (ι.toAddMonoidHom.comp (H0.ofSec p ⊤)) fun a s =>
      (congrArg ι (H0.ofSec_smul a s)).trans (map_smulₛₗ ι a _)
  have hL (s) : L (SecC.of p σ s) = ι (H0.ofSec p ⊤ s) := SecC.lift_of _ _ s
  have hc (x) : cval (RingHom.id ℂ) (L x) = pullVal r m B (SecC.val x) := by
    refine LinearMap.eqOn_span' (f := cval (RingHom.id ℂ) ∘ₗ L) (g := pullVal r m B ∘ₗ SecC.val)
      (s := range (SecC.of p σ)) ?_ (SecC.span_range_of.ge Submodule.mem_top)
    rintro _ ⟨s, rfl⟩
    simp only [LinearMap.comp_apply, hL, SecC.val_of]
    exact cval_pullChart_ofSec hm H.w s
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun s => ?_⟩
  · have h₀ : L x = 0 := by
      obtain ⟨t, ht⟩ := H0.bijective_ofSec_top.2 (L x)
      have e := hc x
      rw [← ht, cval_ofSec, show SecC.val x = 0 from congrArg Subtype.val hx, map_zero] at e
      rw [← ht, hS.1 (a₁ := t) (a₂ := 0) (Subtype.ext (e.trans (map_zero _).symm)), map_zero]
    have := finite_top hp hB
    let b := Module.finBasis F (H0 p B ⊤)
    choose v hv using fun i => H0.bijective_ofSec_top.2 (b i)
    have hx' : x ∈ Submodule.span ℂ (range fun i => SecC.of p σ (v i)) := by
      refine (SecC.span_range_of.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨s, rfl⟩
      have e : s = ∑ i, DVR.FlatBC.algX p ⊤ (b.repr (H0.ofSec p ⊤ s) i) • v i :=
        (H0.bijective_ofSec_top (p := p)).1 (by simp only [map_sum, H0.ofSec_smul, hv, b.sum_repr])
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [SecC.of_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hL, hv] at h₀
    simp [Fintype.linearIndependent_iff.1 (hE.indep _ b b.linearIndependent) c h₀]
  · obtain ⟨t, ht⟩ := hS.2 ⟨_, pullVal_mem_holSec hm (AnRead.all _ _ D) s.2⟩
    have hr : H0.ofSec q ⊤ t ∈ LinearMap.range L := by
      refine (hE.span.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨f, rfl⟩
      obtain ⟨u, rfl⟩ := H0.bijective_ofSec_top.2 f
      exact ⟨_, hL u⟩
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, Subtype.ext (pullVal_injective (r := r) hb ((hc x).symm.trans ?_))⟩
    rw [hx, cval_ofSec]
    exact congrArg Subtype.val ht

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LbH0EqChiStructureModuleOfKrullDimZero
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section General
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

end General

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

end Space

end GlobalTheory.NefNumericsModel
end
end
