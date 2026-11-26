module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.KummerExtensions.EtaleRootsOfUnityReductionGenerator

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleTrace.FinLCover
section -- merged from Development.EtaleCohomology.EtaleTrace.RatPtInPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem RatPtIn_of : RatPtIn := by
  intro k _ _ P r hr V hV
  have := hr
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace r
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩
  have h := pointOfClosedPoint_apply r x hxc a
  show (pointOfClosedPoint r x hxc) a ∈ V
  rw [h]; exact hxV

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.FibreOfEtalePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

lemma isPullback_equalizer {k : Type} [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P)
    (hπ : π ≫ r = p) (t : Pt r) :
    IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π t.1 := by
  have key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b := by
    intro T a b h
    rw [← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · rw [Category.assoc]; exact equalizer.condition _ _
  · intro s
    exact equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])
  · intro s; exact equalizer.lift_ι _ _
  · intro s
    rw [← Category.assoc, equalizer.lift_ι]; exact key s.fst s.snd s.condition
  · intro s m h1 _
    apply equalizer.hom_ext
    exact h1.trans (equalizer.lift_ι _ _).symm

theorem FibreOfEtale_of : FibreOfEtale := by
  intro k _ X P p r π hπ V hE t ht
  have hr : Set.range t.1.base ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ht x
  set t' := IsOpenImmersion.lift V.ι t.1 hr
  have ht' : t' ≫ V.ι = t.1 := IsOpenImmersion.lift_fac _ _ _
  have s := (congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr
    (isPullback_equalizer p r π hπ t)
  have h := IsPullback.of_right' s (isPullback_morphismRestrict π V).flip
  exact MorphismProperty.of_isPullback h hE

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenUseBackPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma gub_stalk_inj {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at ha
  have := Scheme.germToFunctionField_injective X U (ha.trans (map_zero _).symm)
  rw [this, map_zero]

lemma gub_notMem {k : Type} [Field k] {N : ℕ} (h : MvPolynomial (Fin (N + 1)) k) {d : ℕ}
    (hh : h ∈ homogeneousSubmodule (Fin (N + 1)) k d) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • d)) (y : Proj (homogeneousSubmodule (Fin (N + 1)) k))
    (hy : y ∈ (Proj (homogeneousSubmodule (Fin (N + 1)) k)).basicOpen
      (Proj.awayToSection _ h (HomogeneousLocalization.Away.mk _ hh n f hf))) :
    y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
  obtain ⟨hyU, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hy
  have hu2 := hu.map (Proj.stalkIso' (homogeneousSubmodule (Fin (N + 1)) k) y)
  erw [Proj.stalkIso'_germ] at hu2
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu2
  erw [ProjectiveSpectrum.Proj.awayToSection_apply] at hu2
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk'] at hu2
  rw [Proj.mem_basicOpen]
  have hp : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (hI := hp) _ _ _ _).mp hu2

lemma gub_cover {k : Type} [Field k] {N : ℕ} (y : Proj (homogeneousSubmodule (Fin (N + 1)) k)) :
    ∃ i, y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : y ∈ (⊤ : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  exact hm

theorem GenUseBack_of : GenUseBack := by
  intro k _ X _ p N ι v hG n hn f hf x hne hloc
  obtain ⟨i, hxi⟩ := gub_cover (ι x)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)
  have hxU : x ∈ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := hxi
  have hη := genUse_generic_mem _ x hxU
  have hvi : eval₂ (kHom p) v (MvPolynomial.X i) ≠ 0 := ((hG 1 one_pos _ hXi).1).mp hη
  have hf' : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • 1) := by
    rw [smul_eq_mul, mul_one]; exact (mem_homogeneousSubmodule _ _).mpr hf
  have key := (hG 1 one_pos _ hXi).2 n f hf' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := ⟨⟨x, hxU⟩⟩
  have hγ : algebraMap _ X.functionField (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) =
      eval₂ (kHom p) v f / eval₂ (kHom p) v (MvPolynomial.X i) ^ n := by
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff (pow_ne_zero _ hvi)]
    exact key
  have hg : ((MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n).IsHomogeneous n := by
    simpa using (isHomogeneous_X k i).pow n
  obtain ⟨δ, hδ⟩ := hloc _ hg
  have hu : IsUnit (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) := by
    refine isUnit_iff_exists_inv.mpr ⟨δ, gub_stalk_inj x ?_⟩
    rw [map_mul, map_one, hγ, hδ, eval₂_pow]
    have h1 := pow_ne_zero n hvi
    field_simp
  have hmem := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hxU, hu⟩
  rw [← Scheme.preimage_basicOpen] at hmem
  exact gub_notMem _ hXi n f hf' _ hmem

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.JetIndepPf
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem jetIndep_chain {n : ℕ} (w : Fin n → K) (F : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval w F) =
      ∑ j, aeval w (pderiv j F) • KaehlerDifferential.D k K (w j) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hf, pderiv_X, Finset.sum_add_distrib, mul_smul, Finset.smul_sum, Derivation.leibniz]
    simp [Pi.single_apply]
    simp only [apply_ite (aeval w), map_zero, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul]

theorem jetIndep_pderiv {n : ℕ} (w : Fin n → K) (hw : LinearIndependent K (jet k w)) {m : ℕ}
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous m) (h0 : aeval w F = 0) (j : Fin n) :
    aeval w (pderiv j F) = 0 := by
  have e1 := congrArg (aeval w) hF.sum_X_mul_pderiv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, aeval_X, map_nsmul, h0, smul_zero] at e1
  have e2 := jetIndep_chain w F
  rw [h0, Derivation.map_zero] at e2
  refine Fintype.linearIndependent_iff.1 hw (fun j => aeval w (pderiv j F)) ?_ j
  ext
  · simp only [jet, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
    rw [← e1]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [jet, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]
    exact e2.symm

theorem jetIndep_dvd {n p : ℕ} [CharP k p] (F : MvPolynomial (Fin n) k) (h : ∀ j, pderiv j F = 0)
    (α : Fin n →₀ ℕ) (hα : α ∈ F.support) (i : Fin n) : p ∣ α i := by
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · simp [h0]
  have hc := congrArg (AddMonoidAlgebra.coeff · (α - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hα' : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
    ext l
    by_cases hl : i = l
    · subst hl; simp; omega
    · simp [hl]
  rw [hα'] at hc
  have hne : AddMonoidAlgebra.coeff F α ≠ 0 := mem_support_iff.1 hα
  have h1 : (((α - Finsupp.single i 1 : Fin n →₀ ℕ) i : ℕ) : k) + 1 = 0 := (mul_eq_zero.1 hc).resolve_left hne
  have e : (α - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = α i := by simp; omega
  rw [← CharP.cast_eq_zero_iff k p, ← e]
  exact_mod_cast h1

theorem jetIndep_root {n p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (F : MvPolynomial (Fin n) k) {m : ℕ} (hF : F.IsHomogeneous m) (hd : ∀ α ∈ F.support, ∀ i, p ∣ α i) :
    ∃ G : MvPolynomial (Fin n) k, G.IsHomogeneous (m / p) ∧ F = G ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let q : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun α => Finsupp.mapRange (· / p) (Nat.zero_div p) α
  have hq : ∀ α ∈ F.support, p • q α = α := by
    intro α hα; ext i; simp [q, Nat.mul_div_cancel' (hd α hα i)]
  refine ⟨∑ α ∈ F.support, monomial (q α) ((frobeniusEquiv k p).symm (AddMonoidAlgebra.coeff F α)), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro α hα
    apply isHomogeneous_monomial
    have hm : α.degree = m := by
      have := hF (mem_support_iff.1 hα)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have : p * (q α).degree = m := by
      have h2 := congrArg Finsupp.degree (hq α hα)
      rw [map_nsmul, smul_eq_mul] at h2
      rw [h2, hm]
    rw [← this, Nat.mul_div_cancel_left _ hp]
  · rw [sum_pow_char]
    conv_lhs => rw [F.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [monomial_pow, frobeniusEquiv_symm_pow_p, hq α hα]

theorem JetIndep_of : JetIndep := by
  intro k K _ _ _ _ n w hw m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hF h0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_contra hne
    have ht := hF.totalDegree hne
    rw [totalDegree_eq_zero_iff_eq_C] at ht
    rw [ht, aeval_C, map_eq_zero_iff _ (algebraMap k K).injective] at h0
    exact hne (by rw [ht, h0, C_0])
  have hpd : ∀ j, pderiv j F = 0 := fun j =>
    ih (m - 1) (by omega) _ hF.pderiv (jetIndep_pderiv w hw F hF h0 j)
  obtain ⟨p, hcp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · have := Fact.mk hpp
    have : ExpChar k p := ExpChar.prime hpp
    have : PerfectRing k p := PerfectField.toPerfectRing p
    obtain ⟨G, hG, rfl⟩ := jetIndep_root F hF (fun α hα i => jetIndep_dvd F hpd α hα i)
    rw [map_pow] at h0
    have hG0 := ih (m / p) (Nat.div_lt_self hm hpp.one_lt) G hG (pow_eq_zero_iff hpp.ne_zero |>.1 h0)
    rw [hG0, zero_pow hpp.ne_zero]
  · ext α
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hc
    have hα0 : α = 0 := by
      ext i; simpa using jetIndep_dvd (p := 0) F hpd α (mem_support_iff.2 hc) i
    have := hF hc
    subst hα0
    simp at this
    omega

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.TrdegLePf
noncomputable section
open Cardinal IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.EtaleTrace.Cov

theorem kaehler_adjoin_subsingleton (k K : Type) [Field k] [Field K] [Algebra k K] (s : Set K)
    (hs : Submodule.span K (KaehlerDifferential.D k K '' s) = ⊤) :
    Subsingleton Ω[K⁄(IntermediateField.adjoin k s)] := by
  set L := IntermediateField.adjoin k s
  have hD : ∀ x : K, KaehlerDifferential.D L K x = 0 := by
    intro x
    have hx : KaehlerDifferential.D k K x ∈ Submodule.span K (KaehlerDifferential.D k K '' s) := by
      rw [hs]; trivial
    have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k L K K) hx
    rw [Submodule.map_span, KaehlerDifferential.map_D] at h2
    have h3 : (KaehlerDifferential.map k L K K) '' (KaehlerDifferential.D k K '' s) ⊆ {0} := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      have : y = algebraMap L K ⟨y, IntermediateField.subset_adjoin k s hy⟩ := rfl
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.mem_singleton_iff]
      rw [this, Derivation.map_algebraMap]
    have h4 := Submodule.span_mono h3 h2
    simpa using h4
  have htop := KaehlerDifferential.span_range_derivation L K
  have hbot : Submodule.span K (Set.range (KaehlerDifferential.D L K)) = ⊥ := by
    rw [Submodule.span_eq_bot]; rintro _ ⟨x, rfl⟩; exact hD x
  rw [hbot] at htop
  constructor; intro a b
  have ha : a ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  have hb : b ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  rw [Submodule.mem_bot] at ha hb; rw [ha, hb]

theorem TrdegLe_of : TrdegLe := by
  intro k K _ _ _ _
  obtain ⟨b, hbs, hbsp, hbli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D k K))
  rw [KaehlerDifferential.span_range_derivation] at hbsp
  have hpre : ∀ ω : b, ∃ y : K, KaehlerDifferential.D k K y = ω := fun ω => hbs ω.2
  choose t ht using hpre
  set s : Set K := Set.range t
  have himg : KaehlerDifferential.D k K '' s = b := by
    ext ω; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; rw [ht]; exact i.2
    · intro hω; exact ⟨t ⟨ω, hω⟩, ⟨_, rfl⟩, ht _⟩
  have hsub := kaehler_adjoin_subsingleton k K s (by rw [himg, hbsp])
  set L := IntermediateField.adjoin k s
  have : Algebra.FormallyUnramified L K := ⟨hsub⟩
  have : Algebra.EssFiniteType L K := Algebra.EssFiniteType.of_comp k L K
  have : Algebra.IsSeparable L K := (Algebra.FormallyUnramified.iff_isSeparable L K).mp inferInstance
  have : Algebra.IsAlgebraic (Algebra.adjoin k s) K := Algebra.IsAlgebraic.trans _ L K
  have h1 := Algebra.IsAlgebraic.trdeg_le_cardinalMk k s (A := K)
  have h2 : #s ≤ #b := Cardinal.mk_range_le
  have h3 : #b = (Module.finrank K Ω[K⁄k] : Cardinal) := by
    rw [Module.finrank_eq_rank, ← (Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbsp]))).mk_eq_rank'']
  exact h1.trans (h2.trans h3.le)

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.HomRelPf
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

theorem homRel_aeval_scale (k K : Type) [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K)
    (H : MvPolynomial (Fin n) k) (m : ℕ) (hH : H.IsHomogeneous m) :
    aeval (fun j => Polynomial.C (v j) * Polynomial.X) H = Polynomial.C (aeval v H) * Polynomial.X ^ m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_def, eval₂_eq, aeval_def, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = m := by
    have := hH (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  rw [IsScalarTower.algebraMap_apply k K (Polynomial K), Polynomial.algebraMap_eq, mul_assoc]

theorem HomRel_of : HomRel := by
  intro k K _ _ _ d hd n hn v
  classical
  set x : Fin n → Polynomial K := fun j => Polynomial.C (v j) * Polynomial.X with hx
  have htr : Algebra.trdeg k (Polynomial K) = Algebra.trdeg k K + 1 := by
    rw [← trdeg_add_eq (R := k) (S := K) (A := Polynomial K), Polynomial.trdeg_of_isDomain]
  have hni : ¬ AlgebraicIndependent k x := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin] at h1
    have h2 : ((n : ℕ) : Cardinal) ≤ ((d + 1 : ℕ) : Cardinal) := by
      push_cast; exact h1.trans (by gcongr)
    have : n ≤ d + 1 := by exact_mod_cast h2
    omega
  rw [algebraicIndependent_iff] at hni
  push Not at hni
  obtain ⟨G, hGx, hG0⟩ := hni
  obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m G ≠ 0 := by
    by_contra h
    push Not at h
    apply hG0
    rw [← sum_homogeneousComponent G]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨m, homogeneousComponent m G, hm, homogeneousComponent_isHomogeneous m G, ?_⟩
  have hsum : aeval x G = ∑ i ∈ Finset.range (G.totalDegree + 1),
      Polynomial.C (aeval v (homogeneousComponent i G)) * Polynomial.X ^ i := by
    conv_lhs => rw [← sum_homogeneousComponent G]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      homRel_aeval_scale k K v _ i (homogeneousComponent_isHomogeneous i G)
  have hmem : m ∈ Finset.range (G.totalDegree + 1) := by
    rw [Finset.mem_range]
    by_contra h
    exact hm (homogeneousComponent_eq_zero m G (by omega))
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) (hsum.symm.trans hGx)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rwa [Finset.sum_ite_eq, if_pos hmem] at hc

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.StepPf
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.StepPf

lemma eval₂_mul_left {k R σ : Type} [CommSemiring k] [CommSemiring R] (f : k →+* R) (x : σ → R) (r : R)
    {m : ℕ} {F : MvPolynomial σ k} (hF : F.IsHomogeneous m) :
    eval₂ f (fun j => r * x j) F = r ^ m * eval₂ f x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma jet_sub {k K : Type} [Field k] [Field K] [Algebra k K] (a b : K) (c : k) :
    ((a - algebraMap k K c * b), KaehlerDifferential.D k K (a - algebraMap k K c * b)) =
      (a, KaehlerDifferential.D k K a) - (algebraMap k K c) • (b, KaehlerDifferential.D k K b) := by
  ext
  · simp [Algebra.smul_def]
  · simp [Derivation.leibniz]

lemma exists_c {k K : Type} [Field k] [Infinite k] [Field K] [Algebra k K] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (hF0 : F ≠ 0) (a : Fin (n + 1) → K) (j0 : Fin (n + 1)) (ha : a j0 ≠ 0) :
    ∃ c : Fin (n + 1) → k, eval c F ≠ 0 ∧ c (Fin.last n) ≠ 0 ∧ ∑ j, a j * algebraMap k K (c j) ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k K, φ (a j0) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff k (a j0)).mp h)
  set G : MvPolynomial (Fin (n + 1)) k := ∑ j, C (φ (a j)) * X j with hGdef
  have hG : ∀ c, eval c G = φ (∑ j, a j * algebraMap k K (c j)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hGdef, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (a j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hG0 : G ≠ 0 := by
    intro h
    have := hG (Pi.single j0 1)
    rw [h] at this
    simp [Pi.single_apply] at this
    exact hφ this.symm
  have hP : F * X (Fin.last n) * G ≠ 0 := mul_ne_zero (mul_ne_zero hF0 (X_ne_zero _)) hG0
  obtain ⟨c, hc⟩ : ∃ c, eval c (F * X (Fin.last n) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  simp only [map_mul, eval_X] at hc
  refine ⟨c, ?_, ?_, ?_⟩
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · intro h0
    apply right_ne_zero_of_mul hc
    rw [hG, h0, map_zero]

theorem Step_of : LateralTheory.EtaleTrace.Cov.Step := by
  intro k K _ _ _ _ n v m F hF0 hFh hFv hli
  obtain ⟨a, ha, j0, hj0⟩ := Fintype.not_linearIndependent_iff.mp hli
  obtain ⟨c, hcF, hcl, hcs⟩ := exists_c F hF0 a j0 hj0
  set e : k := (c (Fin.last n))⁻¹ with he
  set d : Fin (n + 1) → k := fun j => e * c j with hd
  have hdl : d (Fin.last n) = 1 := inv_mul_cancel₀ hcl
  have hdF : eval d F ≠ 0 := by
    have h := eval₂_mul_left (RingHom.id k) c e hFh
    change eval₂ (RingHom.id k) d F ≠ 0
    rw [show (fun j => e * c j) = d from rfl] at h
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hcl)) hcF
  set s : K := ∑ j, a j * algebraMap k K (d j) with hsdef
  have hs0 : s ≠ 0 := by
    have : s = algebraMap k K e * ∑ j, a j * algebraMap k K (c j) := by
      simp only [hsdef, hd, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hcl)) hcs
  set w : Fin n → K := fun j => v j.castSucc - algebraMap k K (d j.castSucc) * v (Fin.last n) with hw
  have hjw : ∀ j, LateralTheory.EtaleTrace.Cov.jet k w j =
      LateralTheory.EtaleTrace.Cov.jet k v j.castSucc - algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j
    exact jet_sub _ _ _
  have h1 : ∀ j : Fin n, LateralTheory.EtaleTrace.Cov.jet k v j.castSucc =
      LateralTheory.EtaleTrace.Cov.jet k w j + algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j; rw [hjw]; abel
  have hlast : s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = -(∑ j : Fin n, a j.castSucc • LateralTheory.EtaleTrace.Cov.jet k w j) := by
    have hs : s = ∑ j : Fin n, a j.castSucc * algebraMap k K (d j.castSucc) + a (Fin.last n) := by
      rw [hsdef, Fin.sum_univ_castSucc, hdl, map_one, mul_one]
    rw [Fin.sum_univ_castSucc] at ha
    simp_rw [h1, smul_add, Finset.sum_add_distrib, smul_smul] at ha
    rw [hs, add_smul, Finset.sum_smul, eq_neg_iff_add_eq_zero, ← ha]
    abel
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hjw]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hL : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k w)) := by
        have : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = s⁻¹ • (s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n)) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [this, hlast]
        refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_))
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      induction j using Fin.lastCases with
      | last => exact hL
      | cast j =>
        rw [h1]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨j, rfl⟩) (Submodule.smul_mem _ _ hL)
  · intro O hO hk ⟨i, hvi, hvO⟩
    let ι : k →+* O := (algebraMap k K).codRestrict O hk
    let U : Fin (n + 1) → O := fun j => ⟨v j / v i, hvO j⟩
    have hUF : eval₂ ι U F = 0 := by
      apply Subtype.val_injective
      have h := eval₂_comp_left O.subtype ι U F
      change O.subtype (eval₂ ι U F) = 0
      rw [h]
      have h2 : O.subtype.comp ι = algebraMap k K := by ext x; rfl
      have h3 : (O.subtype ∘ U) = fun j => (v i)⁻¹ * v j := by
        funext j; simp [U, div_eq_inv_mul]
      rw [h2, h3, eval₂_mul_left _ _ _ hFh, ← aeval_def, hFv, mul_zero]
    let W : Fin n → O := fun l => U l.castSucc - ι (d l.castSucc) * U (Fin.last n)
    have hWv : ∀ l, (W l : K) = w l / v i := by
      intro l
      simp only [W, U, ι, hw, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, RingHom.codRestrict_apply]
      ring
    by_contra hcon
    push Not at hcon
    have hWm : ∀ l, IsLocalRing.residue O (W l) = 0 := by
      intro l
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hval : w l / v i * (y : K) = 1 := by
        rw [← hWv]
        exact congrArg Subtype.val hy
      have hwl : w l ≠ 0 := by
        intro h0; rw [h0, zero_div, zero_mul] at hval; exact zero_ne_one hval
      obtain ⟨j, hj⟩ := hcon l hwl
      apply hj
      have : v j / w l = v j / v i * (y : K) := by
        rw [eq_comm, eq_div_iff hwl]
        calc v j / v i * (y : K) * w l = v j * (w l / v i * (y : K)) := by ring
          _ = v j := by rw [hval, mul_one]
      rw [this]
      exact O.mul_mem (hvO j) y.2
    set π := IsLocalRing.residue O
    set t := π (U (Fin.last n))
    have hπU : (fun j => π (U j)) = fun j => t * (π.comp ι) (d j) := by
      funext j
      induction j using Fin.lastCases with
      | last => rw [hdl, map_one, mul_one]
      | cast l =>
        have := hWm l
        simp only [W, map_sub, map_mul, sub_eq_zero] at this
        rw [this, RingHom.comp_apply, mul_comm]
    have hmain : t ^ m * (π.comp ι) (eval d F) = 0 := by
      have h := eval₂_comp_left π ι U F
      rw [hUF, map_zero] at h
      have h' : (π ∘ U) = fun j => t * (π.comp ι) (d j) := hπU
      rw [h', eval₂_mul_left _ _ _ hFh] at h
      have h4 := eval₂_comp_left (π.comp ι) (RingHom.id k) d F
      rw [RingHom.comp_id] at h4
      rw [h]
      exact congrArg (t ^ m * ·) h4
    have hne : (π.comp ι) (eval d F) ≠ 0 := (map_ne_zero _).mpr hdF
    have ht : t = 0 := pow_eq_zero_iff'.mp ((mul_eq_zero.mp hmain).resolve_right hne) |>.1
    have hUi : π (U i) = 0 := by
      have := congrFun hπU i
      rw [this, ht, zero_mul]
    have : U i = 1 := Subtype.ext (by simp [U, div_self hvi])
    rw [this, map_one] at hUi
    exact one_ne_zero hUi

end LateralTheory.EtaleTrace.StepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.JetUnramPf
namespace LateralTheory.EtaleTrace.Cov

open KaehlerDifferential in
theorem JetUnram_of : JetUnram := by
  intro k K O _ _ _ _ φ n w i hwi hspan hk hw
  let _ : Algebra O K := φ.toAlgebra
  show Algebra.FormallyUnramified O K
  constructor
  have hD0 : ∀ z ∈ φ.range, D O K z = 0 := by
    rintro _ ⟨o, rfl⟩
    exact (D O K).map_algebraMap o
  let D' : Derivation k K Ω[K⁄O] := Derivation.mk'
    { toFun := fun x => D O K x
      map_add' := fun x y => (D O K).map_add x y
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, (D O K).leibniz, hD0 _ (hk c), smul_zero, add_zero, algebraMap_smul] }
    (fun a b => (D O K).leibniz a b)
  have hD' : ∀ x, D'.liftKaehlerDifferential (D k K x) = D O K x := fun x =>
    D'.liftKaehlerDifferential_comp_D x
  let G : (K × Ω[K⁄k]) →ₗ[K] Ω[K⁄O] :=
    D'.liftKaehlerDifferential.comp (LinearMap.snd K K Ω[K⁄k]) -
      (LinearMap.fst K K Ω[K⁄k]).smulRight ((w i)⁻¹ • D O K (w i))
  have hG : ∀ j, G (jet k w j) = 0 := by
    intro j
    obtain ⟨u, hu⟩ := hw j
    have hwj : w j = φ u * w i := by rw [hu]; field_simp
    show D'.liftKaehlerDifferential (D k K (w j)) - w j • ((w i)⁻¹ • D O K (w i)) = 0
    rw [hD', hwj, (D O K).leibniz, hD0 _ ⟨u, rfl⟩, smul_zero, add_zero, smul_smul, mul_assoc,
      mul_inv_cancel₀ hwi, mul_one, sub_self]
  have hG0 : G = 0 := LinearMap.ext_on_range hspan (fun j => by rw [hG j]; rfl)
  have hDz : ∀ x : K, D O K x = 0 := by
    intro x
    have h := LinearMap.congr_fun hG0 (0, D k K x)
    have h2 : G (0, D k K x) = D O K x := by
      show D'.liftKaehlerDifferential (D k K x) - (0 : K) • ((w i)⁻¹ • D O K (w i)) = D O K x
      rw [hD', zero_smul, sub_zero]
    rw [← h2, h]; rfl
  suffices (⊤ : Submodule K Ω[K⁄O]) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun y => this trivial
  rw [← span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hDz x

end LateralTheory.EtaleTrace.Cov
end

section -- merged from Development.EtaleCohomology.EtaleTrace.ProjectPf
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

lemma pf_div_mem {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (O : Subring K)
    (hk : ∀ c : k, algebraMap k K c ∈ O) (y : K) (hv : ∀ j, v j / y ∈ O) (x : K)
    (hx : x ∈ Submodule.span k (Set.range v)) : x / y ∈ O := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hv j
  | zero => simp
  | add a b _ _ ha hb => rw [add_div]; exact O.add_mem ha hb
  | smul c a _ ha => rw [Algebra.smul_def, mul_div_assoc]; exact O.mul_mem (hk c) ha

lemma pf_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) :
    Module.Finite K (K × Ω[K⁄k]) ∧ Module.finrank K (K × Ω[K⁄k]) = d + 1 := by
  have hf : Module.Finite K (K × Ω[K⁄k]) := ⟨by rw [← hv]; exact Submodule.fg_span (Set.finite_range _)⟩
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_surjective (LinearMap.snd K K Ω[K⁄k]) LinearMap.snd_surjective
  refine ⟨hf, ?_⟩
  rw [Module.finrank_prod, Module.finrank_self, hd]; omega

lemma pf_card {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) : d + 1 ≤ n := by
  obtain ⟨_, h⟩ := pf_finrank d hd v hv
  have := finrank_range_le_card (R := K) (jet k v)
  have e := congrArg (fun s : Submodule K (K × Ω[K⁄k]) => Module.finrank K s) hv
  simp only [finrank_top] at e
  simp only [Set.finrank, Fintype.card_fin] at this
  omega

theorem Project_of (hStep : Step) (hHom : HomRel) : Project := by
  intro k K _ _ _ _ d hd htr n v hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (pf_card d hd v hv)
  induction m with
  | zero =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    refine ⟨v, fun i => Submodule.subset_span ⟨i, rfl⟩, hv,
      linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hr]), ?_⟩
    intro O _ _ h; exact h
  | succ m ih =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    have hdep : ¬ LinearIndependent K (jet k v) := by
      intro hl
      have := hl.fintype_card_le_finrank
      simp [hr] at this
    obtain ⟨e, F, hF0, hFh, hFv⟩ := hHom k K d htr (d + 1 + (m + 1)) (by omega) v
    obtain ⟨w', hw'k, hw'sp, hw'O⟩ := hStep k K (d + 1 + m) v e F hF0 hFh hFv hdep
    obtain ⟨w, hwk, hwsp, hwli, hwO⟩ := ih w' (hw'sp.trans hv)
    refine ⟨w, fun i => ?_, hwsp, hwli, ?_⟩
    · exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hw'k j) (hwk i)
    · intro O hO hk h
      obtain ⟨i, hi, hiO⟩ := hw'O O hO hk h
      obtain ⟨l, hl, hlO⟩ := hwO O hO hk ⟨i, hi, fun j => pf_div_mem v O hk _ hiO _ (hw'k j)⟩
      refine ⟨l, hl, fun j => ?_⟩
      have : v j / w l = (v j / w' i) * (w' i / w l) := by field_simp
      rw [this]; exact O.mul_mem (hiO j) (hlO i)

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.FieldDimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem finrank_frac_of_stdSmooth (k R K : Type) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d k R] :
    Module.finrank K Ω[K⁄k] = d := by
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.IsStandardSmooth k R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Module.Free R Ω[R⁄k] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hr : Module.rank R Ω[R⁄k] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hf : Module.finrank R Ω[R⁄k] = d := Module.finrank_eq_of_rank_eq hr
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]

theorem FieldDim_of : FieldDim := by
  intro k _ d X _ p hp
  letI := (kHom p).toAlgebra
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)
  have hUtop : U = ⊤ := by
    have hs : Subsingleton (PrimeSpectrum k) := inferInstance
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hy : p.base (genericPoint X) ∈ U := e hx
    exact (show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy
  subst hUtop
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d := by
    have := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact this
  letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V := by
      rw [Scheme.Hom.appLE, Category.assoc]
      exact (congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm
    simp only [RingHom.algebraMap_toAlgebra, kHom, ψ]
    have H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V := by
      rw [Category.assoc, ← key]
    exact congrArg (fun f => CommRingCat.Hom.hom f c) H
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  exact finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.JetSpanPf
noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.JetSpanPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

lemma aeval_mem_adj {n : ℕ} (v : Fin n → K) (g : MvPolynomial (Fin n) k) :
    aeval v g ∈ Algebra.adjoin k (Set.range v) := by
  rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨g, rfl⟩

lemma essFT {n : ℕ} (v : Fin n → K)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) :
    Algebra.EssFiniteType k K := by
  classical
  rw [Algebra.essFiniteType_iff]
  refine ⟨Finset.univ.image v, fun z => ?_⟩
  have hs : ((Finset.univ.image v : Finset K) : Set K) = Set.range v := by simp
  rw [hs]
  obtain ⟨f, g, rfl⟩ := hz z
  by_cases h : aeval v f = 0
  · refine ⟨1, Subalgebra.one_mem _, isUnit_one, ?_⟩
    simp [h]
  · refine ⟨aeval v f, aeval_mem_adj v f, IsUnit.mk0 _ h, ?_⟩
    rw [div_mul_cancel₀ _ h]; exact aeval_mem_adj v g

def T {n : ℕ} (v : Fin n → K) : Submodule K Ω[K⁄k] :=
  (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))).comap (LinearMap.inr K K Ω[K⁄k])

lemma fst_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (x : K) :
    ((x, 0) : K × Ω[K⁄k]) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) := by
  have h := Submodule.smul_mem (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))) x
    (Submodule.subset_span ⟨i, rfl⟩)
  simpa [LateralTheory.EtaleTrace.Cov.jet, hi] using h

lemma dv_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (j : Fin n) :
    KaehlerDifferential.D k K (v j) ∈ T v := by
  have h1 : LateralTheory.EtaleTrace.Cov.jet k v j ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) :=
    Submodule.subset_span ⟨j, rfl⟩
  have h2 := Submodule.sub_mem _ h1 (fst_mem v i hi (v j))
  show LinearMap.inr K K Ω[K⁄k] (KaehlerDifferential.D k K (v j)) ∈
    Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))
  convert h2 using 1
  simp [LateralTheory.EtaleTrace.Cov.jet]

lemma dpoly_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (g : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval v g) ∈ T v := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hp hq
  | mul_X p j hp =>
    rw [map_mul, aeval_X, Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (dv_mem v i hi j)) (Submodule.smul_mem _ _ hp)

lemma dall_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) (z : K) :
    KaehlerDifferential.D k K z ∈ T v := by
  obtain ⟨f, g, hfg⟩ := hz z
  by_cases h : aeval v f = 0
  · rw [hfg, h, div_zero, map_zero]; exact Submodule.zero_mem _
  · have hg : aeval v g = z * aeval v f := by rw [hfg, div_mul_cancel₀ _ h]
    have key := congrArg (KaehlerDifferential.D k K) hg
    rw [Derivation.leibniz] at key

    have : KaehlerDifferential.D k K z =
        (aeval v f)⁻¹ • (KaehlerDifferential.D k K (aeval v g) - z • KaehlerDifferential.D k K (aeval v f)) := by
      rw [key, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (dpoly_mem v i hi g)
      (Submodule.smul_mem _ _ (dpoly_mem v i hi f)))

end LateralTheory.EtaleTrace.JetSpanPf

open LateralTheory.EtaleTrace.JetSpanPf in
theorem LateralTheory.EtaleTrace.Cov.JetSpan_of : LateralTheory.EtaleTrace.Cov.JetSpan := by
  intro k K _ _ _ n v i hi hz
  refine ⟨?_, essFT v hz⟩
  rw [eq_top_iff]
  rintro ⟨x, ω⟩ -
  have hω : ω ∈ T (k := k) v := by
    have : (⊤ : Submodule K Ω[K⁄k]) ≤ T v := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro _ ⟨z, rfl⟩; exact dall_mem v i hi hz z
    exact this Submodule.mem_top
  have : ((x, ω) : K × Ω[K⁄k]) = (x, 0) + LinearMap.inr K K Ω[K⁄k] ω := by simp
  rw [this]
  exact Submodule.add_mem _ (fst_mem v i hi x) hω
end
end

namespace LateralTheory.Fin.LCover
theorem projective_space_over_field_integral : LateralTheory.EtaleTrace.Cov.PNIntegral := by
  apply LateralTheory.EtaleTrace.Cov.PNIntegral_of
theorem projective_space_standard_chart_basic_properties : LateralTheory.EtaleTrace.Cov.PNBasic := by
  apply LateralTheory.EtaleTrace.Cov.PNBasic_of <;> first | exact projective_space_over_field_integral
theorem homogeneous_localization_away_generator_evaluation : LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval_of
theorem homogeneous_localization_away_generated_by_coordinates : LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway_of
theorem projective_coordinates_generate_inside_chart : LateralTheory.EtaleTrace.Cov.GenIn := by
  apply LateralTheory.EtaleTrace.Cov.GenIn_of <;> first | exact homogeneous_localization_away_generator_evaluation | exact homogeneous_localization_away_generated_by_coordinates
theorem projective_chart_ring_hom_over_field : LateralTheory.EtaleTrace.Cov.ChartOverK := by
  apply LateralTheory.EtaleTrace.Cov.ChartOverK_of
theorem projective_chart_generic_section_values_agree : LateralTheory.EtaleTrace.Cov.ChartGenVal := by
  apply SchemeAppLEComposition.Cb.etale_projective_chart_generic_valuation_identity
theorem projective_chart_generic_section_on_open : LateralTheory.EtaleTrace.Cov.ChartGenOn := by
  apply LateralTheory.EtaleTrace.Cov.ChartGenOn_of_val <;> first | exact projective_chart_generic_section_values_agree
theorem projective_coordinate_sections_generate_on_chart : LateralTheory.EtaleTrace.Cov.GenOutChart := by
  apply LateralTheory.EtaleTrace.Cov.GenOutChart_of_two <;> first | exact projective_chart_ring_hom_over_field | exact projective_chart_generic_section_on_open
theorem projective_coordinate_sections_agree_on_overlap : LateralTheory.EtaleTrace.Cov.GenOnAgree := by
  apply LateralTheory.EtaleTrace.Cov.GenOnAgree_of
theorem projective_coordinate_sections_glue_across_charts : LateralTheory.EtaleTrace.Cov.GenOutGlue := by
  apply LateralTheory.EtaleTrace.Cov.GenOutGlue_of_agree <;> first | exact projective_coordinate_sections_agree_on_overlap
theorem projective_coordinate_sections_generate_outside_hyperplane : LateralTheory.EtaleTrace.Cov.GenOut := by
  apply LateralTheory.EtaleTrace.Cov.GenOut_of <;> first | exact projective_coordinate_sections_generate_on_chart | exact projective_coordinate_sections_glue_across_charts
theorem function_field_generators_pull_back_to_chart : LateralTheory.EtaleTrace.Cov.GenUseBack := by
  apply LateralTheory.EtaleTrace.Cov.GenUseBack_of
theorem projective_coordinates_generate_function_field : LateralTheory.EtaleTrace.Cov.GenUse := by
  apply LateralTheory.EtaleTrace.Cov.GenUse_of <;> first | exact function_field_generators_pull_back_to_chart
theorem coordinate_differentials_span_function_field_kaehler : LateralTheory.EtaleTrace.Cov.JetSpan := by
  apply LateralTheory.EtaleTrace.Cov.JetSpan_of
theorem function_field_transcendence_degree_le_dim : LateralTheory.EtaleTrace.Cov.TrdegLe := by
  apply LateralTheory.EtaleTrace.Cov.TrdegLe_of
theorem homogeneous_relation_coordinate_integral_dependence : LateralTheory.EtaleTrace.Cov.HomRel := by
  apply LateralTheory.EtaleTrace.Cov.HomRel_of
theorem linear_projection_reduce_ambient_dimension : LateralTheory.EtaleTrace.Cov.Step := by
  apply LateralTheory.EtaleTrace.StepPf.Step_of
theorem linear_projection_etale_cover_exists : LateralTheory.EtaleTrace.Cov.Project := by
  apply LateralTheory.EtaleTrace.Cov.Project_of <;> first | exact linear_projection_reduce_ambient_dimension | exact homogeneous_relation_coordinate_integral_dependence
theorem generic_linear_forms_independent_differentials : LateralTheory.EtaleTrace.Cov.JetIndep := by
  apply LateralTheory.EtaleTrace.Cov.JetIndep_of
theorem linear_projection_unramified_of_independent_differentials : LateralTheory.EtaleTrace.Cov.JetUnram := by
  apply LateralTheory.EtaleTrace.Cov.JetUnram_of
theorem kaehler_differentials_function_field_rank_eq_dim : LateralTheory.EtaleTrace.Cov.FieldDim := by
  apply LateralTheory.EtaleTrace.Cov.FieldDim_of
theorem linear_projection_finite_surjective_onto_affine_space : LateralTheory.EtaleTrace.Cov.FinSurj := by
  apply LateralTheory.EtaleTrace.Cov.FinSurj_of_full <;> first | exact projective_space_standard_chart_basic_properties
theorem finite_cover_etale_at_generic_point : LateralTheory.EtaleTrace.Cov.GenEtaleAtBot := by
  apply LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf.GenEtaleAtBot_of
theorem finite_surjective_unramified_generically_etale : LateralTheory.EtaleTrace.Cov.GenEtale := by
  apply LateralTheory.EtaleTrace.Cov.GenEtale_of_atBot <;> first | exact finite_cover_etale_at_generic_point
theorem rational_point_in_nonempty_open_over_alg_closed : LateralTheory.EtaleTrace.Cov.RatPtIn := by
  apply LateralTheory.EtaleTrace.Cov.RatPtIn_of
theorem etale_fibre_over_rational_point_of_etale_restriction : LateralTheory.EtaleTrace.Cov.FibreOfEtale := by
  apply LateralTheory.EtaleTrace.Cov.FibreOfEtale_of
theorem finite_cover_etale_fibre_over_rational_point : LateralTheory.EtaleTrace.Cov.Fibre := by
  apply LateralTheory.EtaleTrace.Cov.Fibre_of <;> first | exact finite_surjective_unramified_generically_etale | exact rational_point_in_nonempty_open_over_alg_closed | exact etale_fibre_over_rational_point_of_etale_restriction
theorem etale_finite_cover_of_smooth_variety : LateralTheory.EtaleTrace.LCover := by
  apply LateralTheory.EtaleTrace.Cov.goal_of <;> first | exact projective_space_standard_chart_basic_properties | exact projective_coordinates_generate_inside_chart | exact projective_coordinate_sections_generate_outside_hyperplane | exact projective_coordinates_generate_function_field | exact coordinate_differentials_span_function_field_kaehler | exact function_field_transcendence_degree_le_dim | exact homogeneous_relation_coordinate_integral_dependence | exact linear_projection_reduce_ambient_dimension | exact linear_projection_etale_cover_exists | exact generic_linear_forms_independent_differentials | exact linear_projection_unramified_of_independent_differentials | exact kaehler_differentials_function_field_rank_eq_dim | exact linear_projection_finite_surjective_onto_affine_space | exact finite_cover_etale_fibre_over_rational_point
theorem intersectionNumber_baseChange : LateralTheory.EtaleTrace.LCover := etale_finite_cover_of_smooth_variety
end LateralTheory.Fin.LCover
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finCov_holds :
    UpperTheory.Gal.KunnethLefschetz.FinCov := by
  unfold UpperTheory.Gal.KunnethLefschetz.FinCov
  intro k _ _ d X p h1 h2 h3
  obtain ⟨π, t, e1, e2, e3, -⟩ := LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3
  exact ⟨π, e1, e2, e3⟩
