module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.Immersion
namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem AlgRes.fderiv_affCoord_ker_eq_bot {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (i : Fin R.n)
    (x : R.M) (hx : x ∈ R.src i) (hxD : (fun q => eval (R.coord i x) (R.lift i q)) ∉ conePts D)
    (p : (k : K) → ι k) (hp : ∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0)
    (j : Fin A.n) (hj : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)))
      (A.chart j x)).ker = ⊥ := by
  classical
  have hy0t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy0 : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  set f : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) with hfdef
  obtain ⟨O, hO, hxO, -, q, F, hOF⟩ := R.inv i x hx hxD p hp
  obtain ⟨ψ, hψc, hxψ, hψs, hψ⟩ :=
    hA.2 i x hx (R.sncAt i x hx).r (R.sncAt i x hx).span_eq O hO hxO
  set r := (R.sncAt i x hx).r with hr
  have hw0 : f (A.chart j x) = affCoord p (fun q => eval (R.coord i x) (R.lift i q)) := by
    simp only [f, hsy0]
  have hqw0 : eval (f (A.chart j x)) q ≠ 0 := by rw [hw0]; exact (hOF x hxO).2.1
  let H : ((Σ k, ι k) → ℂ) → Fin (R.amb i) → ℂ := fun w l => eval w (F l) / eval w q
  let G : ((Σ k, ι k) → ℂ) → Fin e → ℂ := fun w => (A.chart j ∘ ψ.symm) (evalFam r (H w))
  have hHx : ∀ y ∈ O, H (affCoord p fun q => eval (R.coord i y) (R.lift i q)) = R.coord i y := by
    intro y hy; funext l; simp only [H]; rw [div_eq_iff (hOF y hy).2.1]; exact ((hOF y hy).2.2 l).symm
  have hH0 : H (f (A.chart j x)) = R.coord i x := by rw [hw0]; exact hHx x hxO
  have hHan : AnalyticAt ℂ H (f (A.chart j x)) := by
    rw [analyticAt_pi_iff]; intro l
    exact (AnalyticOnNhd.eval_mvPolynomial (F l) _ (Set.mem_univ _)).div
      (AnalyticOnNhd.eval_mvPolynomial q _ (Set.mem_univ _)) hqw0
  have hEan : AnalyticAt ℂ (evalFam r) (H (f (A.chart j x))) := by
    rw [analyticAt_pi_iff]; intro l
    exact AnalyticOnNhd.eval_mvPolynomial (r l) _ (Set.mem_univ _)
  have hTan : AnalyticAt ℂ (A.chart j ∘ ψ.symm) (evalFam r (H (f (A.chart j x)))) := by
    rw [hH0, ← hψ x hxψ]
    refine (hψc j).2 (ψ x) ⟨ψ.map_source hxψ, ?_⟩
    show ψ.symm (ψ x) ∈ (A.chart j).source
    rw [ψ.left_inv hxψ]; exact hj
  have hGd : DifferentiableAt ℂ G (f (A.chart j x)) :=
    DifferentiableAt.comp (g := A.chart j ∘ ψ.symm) (f := evalFam r ∘ H) (f (A.chart j x))
      hTan.differentiableAt
      (DifferentiableAt.comp (f (A.chart j x)) hEan.differentiableAt hHan.differentiableAt)
  have hfd : DifferentiableAt ℂ f (A.chart j x) := by
    rw [differentiableAt_pi]; intro q'
    have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src i :=
      ⟨hy0t, by show (A.chart j).symm (A.chart j x) ∈ R.src i; rw [hsy0]; exact hx⟩
    have h1 := hA.1 i (R.lift i q') j (A.chart j x) hmem
    have h2 := hA.1 i (R.lift i ⟨q'.1, p q'.1⟩) j (A.chart j x) hmem
    have hne : ((fun y => eval (R.coord i y) (R.lift i ⟨q'.1, p q'.1⟩)) ∘ (A.chart j).symm)
        (A.chart j x) ≠ 0 := by
      simp only [Function.comp, hsy0]; exact hp q'.1
    exact (h1.div h2 hne).differentiableAt
  have hev : (G ∘ f) =ᶠ[𝓝 (A.chart j x)] id := by
    have h1 : ∀ᶠ y in 𝓝 (A.chart j x), y ∈ (A.chart j).target :=
      (A.chart j).open_target.mem_nhds hy0t
    have h2 : ∀ᶠ y in 𝓝 (A.chart j x), (A.chart j).symm y ∈ ψ.source :=
      ((A.chart j).continuousAt_symm hy0t).preimage_mem_nhds
        (ψ.open_source.mem_nhds (by rw [hsy0]; exact hxψ))
    filter_upwards [h1, h2] with y hy1 hy2
    have hy'O : (A.chart j).symm y ∈ O := (hψs hy2).1
    show (A.chart j) (ψ.symm (evalFam r (H (f y)))) = y
    have hfy : f y = affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) := rfl
    rw [hfy, hHx _ hy'O, ← hψ _ hy2, ψ.left_inv hy2, (A.chart j).right_inv hy1]
  have hcomp := hGd.hasFDerivAt.comp (A.chart j x) hfd.hasFDerivAt
  have huniq := hcomp.unique ((hasFDerivAt_id (A.chart j x)).congr_of_eventuallyEq hev)
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  have hv' : fderiv ℂ f (A.chart j x) v = 0 := hv
  rw [← this, hv', map_zero]

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.MemBasicOpenSecHomIff
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

namespace AffPres

variable (P : AffPres s)

theorem mem_basicOpen_secHom_iff (x : W) (hx : x ∈ P.V) (f : MvPolynomial (Fin P.n) ℂ) :
    x ∈ W.basicOpen (P.secHom f) ↔ f ∉ P.ptOf x hx := by
  set g := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv
    (Ideal.Quotient.mk P.K f) with hg
  have h1 : x ∈ W.basicOpen (P.secHom f) ↔
      (⟨x, hx⟩ : P.V.toScheme) ∈ P.V.toScheme.basicOpen (P.iso.hom.app ⊤ g) := by
    rw [Scheme.Opens.mem_basicOpen_toScheme]
    have e : P.secHom f = W.presheaf.map (eqToHom P.V.ι_image_top.symm).op (P.iso.hom.app ⊤ g) := rfl
    have e' := Scheme.basicOpen_res W (i := (eqToHom P.V.ι_image_top.symm).op)
      (f := (P.iso.hom.app ⊤ g : Γ(W, P.V.ι ''ᵁ ⊤)))
    rw [e]
    refine (Iff.of_eq (congrArg (fun O => x ∈ O) e')).trans ?_
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have e2 := Scheme.preimage_basicOpen P.iso.hom g
  refine h1.trans (Iff.trans (Iff.of_eq (congrArg (fun O => (⟨x, hx⟩ : P.V.toScheme) ∈ O) e2.symm)) ?_)
  show P.iso.hom.base ⟨x, hx⟩ ∈ (Spec _).basicOpen g ↔ _
  have e4 := AlgebraicGeometry.basicOpen_eq_of_affine
    (R := .of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) (Ideal.Quotient.mk P.K f)
  rw [hg, e4]
  exact Iff.rfl

theorem secHom_C' (c : ℂ) : P.secHom (C c) = constSec s P.V c := by
  have e1 : P.secHom (C c) = P.V.topIso.hom (P.iso.hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)))) := rfl
  have e2 : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop
        ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have e3 : P.iso.hom.appTop ((Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
      (P.V.ι ≫ s).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← P.hover]
    rfl
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫
      W.presheaf.map (homOfLE (le_top : P.V.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        W.presheaf.map (eqToHom P.V.ι_image_top.symm).op =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appLE ⊤ P.V le_top := by
    rw [← Functor.map_comp]
    rfl
  rw [e1, e2, e3]
  exact congrArg (fun φ => φ.hom c) key

theorem eval_coord_eq_val [LocallyOfFiniteType s] (x : W) (hx : x ∈ P.V)
    (hc : IsClosed ({x} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    eval (P.coord x hx) f = val s (P.secHom f) x hx := by
  obtain ⟨φ, hφ⟩ := val_ringHom s P.V x hx hc
  set ψ := φ.comp P.secHom with hψdef
  have hC : ∀ c, ψ (C c) = c := by
    intro c
    rw [hψdef, RingHom.comp_apply, hφ, secHom_C', val_const s _ x hx hc]
  have hker : ∀ g, ψ g = 0 → g ∈ P.ptOf x hx := by
    intro g h
    by_contra hg
    rw [← mem_basicOpen_secHom_iff] at hg
    rw [hψdef, RingHom.comp_apply, hφ, val_eq_zero_iff s _ x hx hc,
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen] at h
    exact h hg
  have hpr : P.ptOf x hx ≠ ⊤ :=
    Ideal.comap_ne_top _ (P.iso.hom.base ⟨x, hx⟩).isPrime.ne_top
  have hX : ∀ j, ψ (X j) = P.coord x hx j := by
    intro j
    have h1 : X j - C (ψ (X j)) ∈ P.ptOf x hx := hker _ (by rw [map_sub, hC, sub_self])
    have h2 : X j - C (P.coord x hx j) ∈ P.ptOf x hx :=
      Classical.epsilon_spec (p := fun c : ℂ => X j - C c ∈ P.ptOf x hx) ⟨_, h1⟩
    have h3 : C (ψ (X j) - P.coord x hx j) ∈ P.ptOf x hx := by
      have := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    by_contra hne
    have hu : IsUnit (C (ψ (X j) - P.coord x hx j) : MvPolynomial (Fin P.n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map C
    exact hpr (Ideal.eq_top_of_isUnit_mem _ h3 hu)
  have hψ : ψ = eval (P.coord x hx) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hφ]
  exact (RingHom.congr_fun hψ f).symm

end AffPres

end

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.SegreIdealIsHomogeneous
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry

noncomputable section

section Quot

variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ))

attribute [local instance] MvPolynomial.gradedAlgebra

def quotGrading : ℕ → Submodule ℂ (MvPolynomial σ ℂ ⧸ I) :=
  fun d => (homogeneousSubmodule σ ℂ d).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap

theorem quot_gradedAlgebra (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    Nonempty (GradedAlgebra (quotGrading I)) := by
  classical
  have hgm : SetLike.GradedMonoid (quotGrading I) :=
    { one_mem := ⟨1, SetLike.one_mem_graded (homogeneousSubmodule σ ℂ), map_one (Ideal.Quotient.mkₐ ℂ I)⟩
      mul_mem := by
        rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, SetLike.mul_mem_graded hf hg, map_mul (Ideal.Quotient.mkₐ ℂ I) f g⟩ }
  have hproj : ∀ i, (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j) ≤
      LinearMap.ker (GradedAlgebra.proj (homogeneousSubmodule σ ℂ) i) := by
    intro i
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro g hg
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ hg hj]
  have hint : DirectSum.IsInternal (quotGrading I) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      rintro x ⟨f, hf, rfl⟩ hx
      have hx' : (Ideal.Quotient.mkₐ ℂ I).toLinearMap f ∈
          (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap := by
        simp only [Submodule.map_iSup]
        exact hx
      obtain ⟨g, hg, hgf⟩ := hx'
      have hfg : f - g ∈ I := by
        rw [← Ideal.Quotient.eq]
        exact hgf.symm
      have hcomp := (hI.mem_iff (homogeneousSubmodule σ ℂ)).mp hfg i
      have hgi : (DirectSum.decompose (homogeneousSubmodule σ ℂ) g i : MvPolynomial σ ℂ) = 0 := by
        have := hproj i hg
        rwa [LinearMap.mem_ker, GradedAlgebra.proj_apply] at this
      rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, hgi, sub_zero,
        DirectSum.decompose_of_mem_same _ hf] at hcomp
      show Ideal.Quotient.mk I f = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    · have htop : (⨆ i, homogeneousSubmodule σ ℂ i) = ⊤ :=
        (DirectSum.Decomposition.isInternal (homogeneousSubmodule σ ℂ)).submodule_iSup_eq_top
      unfold quotGrading
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective ℂ I
  exact ⟨{ hgm, hint.chooseDecomposition with }⟩

end Quot

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
  aeval fun p => ∏ k, X ⟨k, p k⟩

def segreIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Ideal (MvPolynomial ((k : K) → ι k) ℂ) :=
  P.comap (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ)

private lemma isWH_of_multiHomog [DecidableEq K] {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  intro d hd
  have h := hf d (MvPolynomial.mem_support_iff.mpr hd)
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, ← h k, Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl
    intro i _
    simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro i _
    simp [Pi.single_apply, Ne.symm hb]
  · simp

private lemma segre_isWH [DecidableEq K] {φ : MvPolynomial ((k : K) → ι k) ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) :
    IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (segreMap φ)
      (fun _ => n) := by
  classical
  have hg : ∀ p : (k : K) → ι k, IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))
      (∏ k, X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) (fun _ => 1) := by
    intro p
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (fun k => (Pi.single k 1 : K → ℕ))
      (fun k _ => isWeightedHomogeneous_X ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) ⟨k, p k⟩)
    convert this using 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← mem_weightedHomogeneousSubmodule]
  show aeval (fun p : (k : K) → ι k => ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) φ ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [φ.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hdeg : (0 : K → ℕ) + ∑ p ∈ d.support, d p • (fun _ : K => 1) = fun _ => n := by
    have hw := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum] at hw
    funext j
    simp only [zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    simpa using hw
  rw [← hdeg]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hg p).pow (d p))

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem segreIdeal_isHomogeneous {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    (segreIdeal P).IsHomogeneous (homogeneousSubmodule ((k : K) → ι k) ℂ) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  letI := MvPolynomial.weightedGradedAlgebra ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))
  have hPh : (Ideal.span S).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWH_of_multiHomog ha)⟩
  intro n φ hφ
  unfold segreIdeal at hφ ⊢
  rw [Ideal.mem_comap] at hφ ⊢
  have hdec : (DirectSum.decompose (homogeneousSubmodule ((k : K) → ι k) ℂ) φ n :
      MvPolynomial ((k : K) → ι k) ℂ) = homogeneousComponent n φ :=
    MvPolynomial.decomposition.decompose'_apply φ n
  rw [hdec]
  have h1 := (hPh.mem_iff _).mp hφ (fun _ => n)
  have hwdec : (DirectSum.decompose (weightedHomogeneousSubmodule ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)))
      (segreMap φ) (fun _ => n) : MvPolynomial (Σ k, ι k) ℂ) =
      weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (fun _ => n) (segreMap φ) :=
    MvPolynomial.weightedDecomposition.decompose'_apply ℂ _ _ _
  rw [hwdec] at h1
  have hsum : segreMap φ = ∑ m ∈ Finset.range (φ.totalDegree + 1), segreMap (homogeneousComponent m φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_homogeneousComponent]
  have hterm : ∀ m, weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (fun _ => n)
      (segreMap (homogeneousComponent m φ)) = if n = m then segreMap (homogeneousComponent m φ) else 0 := by
    intro m
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (segre_isWH (homogeneousComponent_isHomogeneous m φ)))]
    by_cases h : n = m
    · subst h
      simp
    · rw [if_neg, if_neg h]
      intro he
      obtain ⟨k⟩ := ‹Nonempty K›
      exact h (congrFun he k)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum] at h1
  simp only [hterm, Finset.sum_ite_eq] at h1
  split_ifs at h1 with hn
  · exact h1
  · rw [homogeneousComponent_eq_zero _ _ (by simp at hn; omega), map_zero]
    exact zero_mem _

abbrev segreGrading (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    ℕ → Submodule ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
  quotGrading (segreIdeal P)

@[reducible] def segreGraded {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    GradedAlgebra (segreGrading P) :=
  Classical.choice (quot_gradedAlgebra _ (segreIdeal_isHomogeneous hP))

def projX (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) : Scheme :=
  letI := segreGraded hP
  Proj (segreGrading P)

abbrev segreW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P :=
  Ideal.Quotient.mk _ (X p)

theorem segreW_mem (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    segreW P p ∈ segreGrading P 1 := by
  exact ⟨X p, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℂ p), rfl⟩

def chartOpen {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    (projX P hP).affineOpens :=
  letI := segreGraded hP
  ⟨Proj.basicOpen (segreGrading P) (segreW P p), Proj.isAffineOpen_basicOpen _ _ (segreW_mem P p) one_pos⟩

theorem chartOpen_cover {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (x : projX P hP) : ∃ p, x ∈ (chartOpen hP p).1 := by
  classical
  letI := segreGraded hP
  by_contra hcon
  push_neg at hcon
  have hall : ∀ p, segreW P p ∈ x.asHomogeneousIdeal := by
    intro p
    by_contra h
    exact hcon p ((Proj.mem_basicOpen (segreGrading P) (segreW P p) x).mpr h)
  have key : ∀ f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set ((k : K) → ι k))),
      Ideal.Quotient.mk (segreIdeal P) f ∈ x.asHomogeneousIdeal.toIdeal := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨p, -, rfl⟩
      exact hall p
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact add_mem ha hb
    · intro a b _ hb
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hb
  apply ProjectiveSpectrum.not_irrelevant_le x
  intro a ha
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  rw [x.asHomogeneousIdeal.isHomogeneous.mem_iff]
  intro i
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [ha]
    exact zero_mem _
  · obtain ⟨f, hf, hfa⟩ := (DirectSum.decompose (segreGrading P) a i).2
    rw [← hfa]
    apply key
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push_neg at hne
    have hm0 : m = 0 := Finsupp.ext fun p => hne p (Set.mem_univ p)
    have hw := ((mem_homogeneousSubmodule i f).mp hf) (MvPolynomial.mem_support_iff.mp hm)
    rw [hm0, map_zero] at hw
    omega

end

end ReciprocityTheory.AnForm.R
end
