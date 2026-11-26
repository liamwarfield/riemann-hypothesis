module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

section Linear

variable {ι O : Type} [Fintype ι] [CommRing O]
variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]

theorem mem_eig (ρ : O →+* Module.End R N) (σ : O →+* R) (u : N) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def Splits (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : Prop :=
  ∀ m : N, ∃! f : ι → N, (∀ s a, ρ a (f s) = τ s a • f s) ∧ ∑ s, f s = m

def sumMap (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : (∀ s, eigSp ρ (τ s)) →ₗ[R] N :=
  ∑ s, (eigSp ρ (τ s)).subtype ∘ₗ LinearMap.proj s

theorem sumMap_apply (ρ : O →+* Module.End R N) (τ : ι → O →+* R) (g : ∀ s, eigSp ρ (τ s)) :
    sumMap ρ τ g = ∑ s, (g s : N) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_bij {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    Function.Bijective (sumMap ρ τ) := by
  constructor
  · intro g g' e
    have := (h (sumMap ρ τ g)).unique (y₁ := fun s => (g s : N)) (y₂ := fun s => (g' s : N))
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g s).2 a, (sumMap_apply ρ τ g).symm⟩
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g' s).2 a, by rw [e, sumMap_apply]⟩
    exact funext fun s => Subtype.ext (congrFun this s)
  · intro m
    obtain ⟨f, ⟨hf, hs⟩, -⟩ := h m
    exact ⟨fun s => ⟨f s, (mem_eig ρ (τ s) _).2 (hf s)⟩, by rw [sumMap_apply]; exact hs⟩

theorem exists_bases [DecidableEq ι] [IsLocalRing R] [Module.Finite R N] [Module.Projective R N]
    {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    ∃ r : ι → ℕ, Nonempty (∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) := by
  let e := LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h)
  haveI hP : Module.Projective R (∀ s, eigSp ρ (τ s)) := Module.Projective.of_equiv e.symm
  have key : ∀ s, Module.Free R (eigSp ρ (τ s)) ∧ Module.Finite R (eigSp ρ (τ s)) := fun s => by
    haveI : Module.Finite R (∀ s, eigSp ρ (τ s)) := Module.Finite.equiv e.symm
    haveI : Module.Finite R (eigSp ρ (τ s)) :=
      Module.Finite.of_surjective (LinearMap.proj s : (∀ s, eigSp ρ (τ s)) →ₗ[R] eigSp ρ (τ s))
        (fun y => ⟨Pi.single s y, by simp⟩)
    haveI : Module.Projective R (eigSp ρ (τ s)) :=
      Module.Projective.of_split (LinearMap.single R (fun s => eigSp ρ (τ s)) s) (LinearMap.proj s)
        (LinearMap.ext fun y => by simp)
    haveI : Module.FinitePresentation R (eigSp ρ (τ s)) := Module.finitePresentation_of_projective _ _
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  refine ⟨fun s => Module.finrank R (eigSp ρ (τ s)), ⟨fun s => ?_⟩⟩
  haveI := (key s).1
  haveI := (key s).2
  exact Module.finBasis R _

def totBasis [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) : Module.Basis (Σ s, Fin (r s)) R N :=
  (Pi.basis b).map (LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h))

theorem totBasis_apply [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (s : ι) (i : Fin (r s)) :
    totBasis h b ⟨s, i⟩ = b s i := by
  simp only [totBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply, sumMap_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

variable {T N' : Type} [CommRing T] [AddCommGroup N'] [Module T N']

theorem image_frame [DecidableEq ι] {θ : R →+* T} {ρ : O →+* Module.End R N} {τ : ι → O →+* R}
    {ρ' : O →+* Module.End T N'} (h' : Splits ρ' fun s => θ.comp (τ s)) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (β : N →ₛₗ[θ] N')
    (B : Module.Basis (Σ s, Fin (r s)) T N') (hB : ∀ s i, B ⟨s, i⟩ = β (b s i))
    (hρ : ∀ a e, ρ' a (β e) = β (ρ a e)) (s : ι) :
    LinearIndependent T (fun i => β (b s i)) ∧
      Submodule.span T (Set.range fun i => β (b s i)) = eigSp ρ' (θ.comp (τ s)) := by
  have hv : ∀ s i, ∀ a, ρ' a (β (b s i)) = (θ.comp (τ s)) a • β (b s i) := fun s i a => by
    rw [hρ, (mem_eig ρ (τ s) _).1 (b s i).2 a, β.map_smulₛₗ]
    rfl
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_⟩
  · have := B.linearIndependent.comp (Sigma.mk s) sigma_mk_injective
    convert this using 1
    exact funext fun i => (hB s i).symm
  · rintro _ ⟨i, rfl⟩
    exact (mem_eig ρ' _ _).2 (hv s i)
  · let f : ι → N' := fun s' => ∑ i, B.repr w ⟨s', i⟩ • β (b s' i)
    have hf : ∀ s' a, ρ' a (f s') = (θ.comp (τ s')) a • f s' := fun s' a => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [f, map_sum, Finset.smul_sum, map_smul, hv s']
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsum : ∑ s', f s' = w := by
      have := B.sum_repr w
      rw [Fintype.sum_sigma] at this
      simpa only [f, hB] using this
    have hw' := (mem_eig ρ' _ _).1 hw
    have hu := (h' w).unique (y₁ := f) (y₂ := fun s' => if s' = s then w else 0) ⟨hf, hsum⟩
      ⟨fun s' a => by
        by_cases e : s' = s
        · subst e; simpa using hw' a
        · simp [e], by simp⟩
    have : w = f s := by simpa using (congrFun hu s).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

open GlobalTheory.CompanionTheory.Ar.LieVB

theorem splits_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {S : Type} [CommRing S] (κ : c.F →+* S) {N : Type} [AddCommGroup N] [Module S N]
    (ρ : 𝓞 E →+* Module.End S N) : Splits ρ (fun s : E →+* ℂ => κ.comp (tauIn c s)) := by
  letI : Algebra c.F S := κ.toAlgebra
  exact fun m => GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ m

theorem exists_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  classical
  intro E _ _ _ H l c X t A _ _ x κ σ
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨N, _, _, ⟨M⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X t.G A x N M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X t.G A x N M
  have hsp := splits_of c κ ρ
  obtain ⟨r, ⟨b⟩⟩ := exists_bases hsp
  refine ⟨r σ, fun i => M.pt (b σ i), ?_⟩
  intro T _ θ x' hx' v hv
  subst hx'
  obtain ⟨N', _, _, ⟨M'⟩⟩ := lieModel_exists X t.G T (spMap θ ≫ x)
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act X t.G T (spMap θ ≫ x) N' M' (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  let q := Fintype.equivFin (Σ s, Fin (r s))
  obtain ⟨β, B, hB, hβ⟩ := basis_tr θ x (spMap θ ≫ x) rfl M M' ((totBasis hsp b).reindex q)
  have hB' : ∀ s i, (B.reindex q.symm) ⟨s, i⟩ = β (b s i) := fun s i => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      totBasis_apply]
  have hact : ∀ a e, ρ' a (β e) = β (ρ a e) := fun a e => pt_left_inj M' (by
    rw [hβ, hρ a e, Over.comp_left, ← Category.assoc, ← hβ e, hρ' a (β e), Over.comp_left])
  have hsp' : Splits ρ' (fun s : E →+* ℂ => θ.comp (κ.comp (tauIn c s))) := splits_of c (θ.comp κ) ρ'
  obtain ⟨hli, hspan⟩ := image_frame hsp' b β (B.reindex q.symm) hB' hact σ
  have hvv : v = fun k => M'.pt (β (b σ k)) := funext fun k => Over.OverMorphism.ext (by
    rw [hv k, hβ])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action X T t.G (spMap θ ≫ x) N' M').2 (𝓞 E) t.act ρ' ((θ.comp κ).comp (tauIn c σ)) hρ').2 _ _).2
    ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangentsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_eigen_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtends
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSections

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl


omit [GrpObj G] in
theorem ringHom_ext_of_mono {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ X) [Mono x] {a b : R →+* A}
    (h : spMap a ≫ x = spMap b ≫ x) : a = b :=
  congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h))

theorem extends_of_tr {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G ξ E) {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk q.1)
    (j : F → E) (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap ((genMap ξ q).comp ψ)) ≫ (MR.pt e).left) (e : F)
    (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G)
    (hv : v.left = spMap (dualMap ψ) ≫ (MR.pt e).left) : M.Extends q (j e) v := by
  refine ⟨?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom _ _ _).toRingHom) ≫ v.left = _
    rw [hv, ← Category.assoc]
    have h : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk q.1) (X.presheaf.stalk q.1) (X.presheaf.stalk q.1)).toRingHom) ≫
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ) =
        spMap ψ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      apply RingHom.ext
      intro a
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    rw [h, Category.assoc, MR.tan e]
    exact congrArg (·.left) (comp_one (M := G)
      (Over.homMk (spMap ψ) hψ : Over.mk (X.fromSpecStalk q.1) ⟶ Over.mk x))
  · rw [hj, ← spMap_dual_comp, Category.assoc, ← hv]

variable [Smooth G.hom] [IsCommMonObj G]

theorem exists_affine_chart (G : Over X) [GrpObj G] [Smooth G.hom] [IsCommMonObj G] (y : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (F : Type) (_ : AddCommGroup F) (_ : Module Γ(X, U) F)
      (_ : LieModel G (R := Γ(X, U)) hU.fromSpec F) (n : ℕ) (_ : Module.Basis (Fin n) Γ(X, U) F), y ∈ U := by
  obtain ⟨R₁, _, x₁, hx₁, F₁, _, _, M₁, n, b₁, hy⟩ := exists_chart G y
  have hU : IsAffineOpen x₁.opensRange := isAffineOpen_opensRange x₁
  let R₀ : Type := Γ(X, x₁.opensRange)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hr : Set.range x₀ ⊆ Set.range x₁ := by
    change Set.range hU.fromSpec ⊆ _
    rw [hU.range_fromSpec]
    exact subset_of_eq (Scheme.Hom.coe_opensRange x₁)
  let τ : R₁ →+* R₀ := (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom
  have hτ : spMap τ ≫ x₁ = x₀ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x₁ x₀ hr)).hom) ≫ x₁ = x₀
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  obtain ⟨F₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R₀ x₀
  obtain ⟨-, B, -, -⟩ := basis_tr τ x₁ x₀ hτ M₁ M₀ b₁
  exact ⟨_, hU, F₀, _, _, M₀, n, B, hy⟩

theorem exists_germs {R : Type} [CommRing R] {x : Sp R ⟶ X} {F : Type} [AddCommGroup F] [Module R F]
    (MR : LieModel G x F) {n : ℕ} (b : Module.Basis (Fin n) R F) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (φ : R →+* Ω) (j : F →ₛₗ[φ] E)
    (hj : ∀ e, (M.pt (j e)).left = spMap (dualMap φ) ≫ (MR.pt e).left) (p : Cpt ξ)
    (ψ : R →+* X.presheaf.stalk p.1) (hψ : spMap ψ ≫ x = X.fromSpecStalk p.1) (hg : (genMap ξ p).comp ψ = φ)
    {c : E} (hc : c ∈ M.lat p) :
    ∃ s : Fin n → X.presheaf.stalk p.1, c = ∑ k, genMap ξ p (s k) • j (b k) := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p c).1 hc
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨β, Bq, hBq, hβ⟩ := basis_tr (A := X.presheaf.stalk p.1) ψ x (X.fromSpecStalk p.1) hψ MR Mq b
  obtain ⟨jq, hjq⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ξ (genMap ξ p)
    (spec_genMap ξ p) Mq M
  have hcomp : ∀ e, jq (β e) = j e := fun e => LieVB.pt_left_inj M (by
    rw [hjq, hβ, ← Category.assoc, spMap_dual_comp, hg, hj])
  obtain ⟨y, rfl⟩ := Mq.onto v hv.1
  have hy : c = jq y := pt_left_inj M (hv.2.trans (hjq y).symm)
  refine ⟨fun k => Bq.repr y k, ?_⟩
  rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← Bq.sum_repr y, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [jq.map_smulₛₗ, hBq, hcomp]

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar.LieSections

theorem exists_common_denom {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) {I : Type} [Finite I]
    (s : I → X.presheaf.stalk y) : ∃ (f : Γ(X, U)) (r : I → Γ(X, U)), y ∈ X.basicOpen f ∧
      ∀ i, (X.presheaf.germ U y hy).hom f * s i = (X.presheaf.germ U y hy).hom (r i) := by
  let u : U := ⟨y, hy⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (u : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf u
  have hloc := hU.isLocalization_stalk u
  obtain ⟨⟨f, hf⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hU.primeIdealOf u).asIdeal.primeCompl (S := X.presheaf.stalk (u : X)) s
  choose r hr using hint
  refine ⟨f, r, (Scheme.mem_basicOpen _ _ _ hy).2 ?_, fun i => ?_⟩
  · exact IsLocalization.map_units (M := (hU.primeIdealOf u).asIdeal.primeCompl)
      (X.presheaf.stalk (u : X)) ⟨f, hf⟩
  · have := hr i
    rw [Algebra.smul_def] at this
    exact this.symm

end GlobalTheory.CompanionTheory.Ar.LieSections

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieSections in
theorem lieLat_germs_eq_sections : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hN hc
  obtain ⟨U, hU, F₀, _, _, M₀, n, b₀, hpU⟩ := LieSections.exists_affine_chart G p.1
  let R₀ : Type := Γ(X, U)
  let x₀ : Sp R₀ ⟶ X := hU.fromSpec
  have hx₀ : IsOpenImmersion x₀ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : x₀.opensRange = U := hU.opensRange_fromSpec
  have hgen : genPt ξ ∈ x₀.opensRange := p.2.mem_open x₀.opensRange.isOpen (by rw [hrange]; exact hpU)
  obtain ⟨φ₀, hφ₀⟩ := LieVB.exists_lift x₀ ξ hgen
  let ψ₀ : R₀ →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  have hψ₀ : spMap ψ₀ ≫ x₀ = X.fromSpecStalk p.1 := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hpU]
    rfl
  have hg : (genMap ξ p).comp ψ₀ = φ₀ := LieSections.ringHom_ext_of_mono x₀ (by
    rw [LieSections.spMap_comp', Category.assoc, hψ₀, hφ₀]
    exact LieTangent.spec_genMap ξ p)
  obtain ⟨j₀, hj₀⟩ := LieVB.exists_tr x₀ ξ φ₀ hφ₀ M₀ M
  choose s hs using fun i => LieSections.exists_germs M₀ b₀ M φ₀ j₀ hj₀ p ψ₀ hψ₀ hg (hc i)
  obtain ⟨f, r, hpf, hr⟩ := LieSections.exists_common_denom hU p.1 hpU (fun ik : J × Fin n => s ik.1 ik.2)
  obtain ⟨g, hgN, hpg⟩ := hU.exists_basicOpen_le (V := N) ⟨p.1, hN⟩ hpU
  let D : X.Opens := X.basicOpen (f * g)
  have hD : IsAffineOpen D := hU.basicOpen (f * g)
  have hDU : D ≤ U := X.basicOpen_le (f * g)
  have hpD : p.1 ∈ D := by
    change p.1 ∈ X.basicOpen (f * g)
    rw [Scheme.basicOpen_mul]
    exact ⟨hpf, hpg⟩
  let R : Type := Γ(X, D)
  let x : Sp R ⟶ X := hD.fromSpec
  have hx : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hD.fromSpec)
  have hxr : x.opensRange = D := hD.opensRange_fromSpec
  let ρ : R₀ →+* R := (X.presheaf.map (homOfLE hDU).op).hom
  have hρ : spMap ρ ≫ x₀ = x := hU.map_fromSpec hD (homOfLE hDU).op
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G R x
  obtain ⟨β, hβ⟩ := LieVB.exists_tr x₀ x ρ hρ M₀ MF
  have hu : IsUnit (ρ (f * g)) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace (f * g)
  obtain ⟨w, hw⟩ : ∃ w : R, ρ f * w = 1 := by
    rw [map_mul] at hu
    exact (isUnit_of_mul_isUnit_left hu).exists_right_inv
  refine ⟨R, inferInstance, x, hx, F, inferInstance, inferInstance, MF,
    fun i => ∑ k, (ρ (r (i, k)) * w) • β (b₀ k), ?_, ?_, fun q ψ hψ i v hv => ?_⟩
  · rw [hxr]; exact hpD
  · rw [hxr]
    have hDg : D = X.basicOpen f ⊓ X.basicOpen g := X.basicOpen_mul f g
    exact (hDg.le.trans inf_le_right).trans hgN
  let φ : R →+* Ω := (genMap ξ q).comp ψ
  have hφ : spMap φ ≫ x = ξ := by
    rw [LieSections.spMap_comp', Category.assoc, hψ]
    exact LieTangent.spec_genMap ξ q
  have hφρ : φ.comp ρ = φ₀ := LieSections.ringHom_ext_of_mono x₀ (by
    rw [LieSections.spMap_comp', Category.assoc, hρ, hφ, hφ₀])
  obtain ⟨j, hj⟩ := LieVB.exists_tr x ξ φ hφ MF M
  have hjβ : ∀ u, j (β u) = j₀ u := fun u => LieVB.pt_left_inj M (by
    rw [hj, hβ, ← Category.assoc, LieVB.spMap_dual_comp, hφρ, hj₀])
  have hjc : j (∑ k, (ρ (r (i, k)) * w) • β (b₀ k)) = c i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [j.map_smulₛₗ, hjβ]
    congr 1
    have h1 : φ (ρ f) * φ w = 1 := by rw [← map_mul, hw, map_one]
    have h2 : φ (ρ (r (i, k))) = φ₀ (r (i, k)) := congrArg (fun t => t (r (i, k))) hφρ
    have h3 : φ (ρ f) = φ₀ f := congrArg (fun t => t f) hφρ
    have h4 : φ₀ f * genMap ξ p (s i k) = φ₀ (r (i, k)) := by
      have := congrArg (genMap ξ p) (hr (i, k))
      rw [map_mul] at this
      have e : ∀ a, genMap ξ p (ψ₀ a) = φ₀ a := fun a => congrArg (fun t => t a) hg
      rw [show (X.presheaf.germ U p.1 hpU).hom f = ψ₀ f from rfl,
        show (X.presheaf.germ U p.1 hpU).hom (r (i, k)) = ψ₀ (r (i, k)) from rfl, e, e] at this
      exact this
    rw [map_mul, h2, ← h4, ← h3, mul_comm (φ (ρ f)), _root_.mul_assoc, h1, _root_.mul_one]
  rw [← hjc]
  exact LieSections.extends_of_tr M MF q ψ hψ j hj _ v hv

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lie_model_extends : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | exact GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCover
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartCover

private lemma eval_eq_zero_of_mem_mcPts' {K : Type} {J : K → Type}
    (P : Ideal (MRing J)) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    ∀ g ∈ pC P, MvPolynomial.eval z g = 0 := by
  intro g hg
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) := by
    unfold pC
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact RingHom.mem_ker.mpr (hz.2 f hf)
  exact RingHom.mem_ker.mp (hle hg)

private lemma torusSmul_mem_mcPts' {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (P : Ideal (MRing J)) (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P))
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    torusSmul c z ∈ mcPts P := by
  have hv := eval_eq_zero_of_mem_mcPts' P z hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz ⊢
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hmem : MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P := by
      unfold pC
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hP c z hv _ hmem

theorem mcPts_finite_cover_up_to_torus :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  intro K _ J _ P hP C O hO hcov
  classical
  set S : Set ((Σ k, J k) → ℂ) :=
    {w | (∀ k, ∑ i, ‖w ⟨k, i⟩‖ ^ 2 = 1) ∧
      ∀ f ∈ P, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} with hS
  have hSsub : S ⊆ mcPts P := by
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hw.2⟩
    by_contra h
    push Not at h
    have h1 := hw.1 k
    simp [h] at h1
  have hScl : IsClosed S := by
    rw [hS]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun k => ?_)
      (isClosed_iInter fun f => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
        (continuous_norm.comp (continuous_apply _)).pow 2) continuous_const
    · exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, J k) → ℂ)) (r := 1)).subset ?_
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    have h2 : ‖w ⟨k, i⟩‖ ^ 2 ≤ 1 := by
      rw [← hw.1 k]
      exact Finset.single_le_sum (f := fun j => ‖w ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (w ⟨k, i⟩)]
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover O hO
    (fun w hw => Set.mem_iUnion.2 (hcov w (hSsub hw)))
  refine ⟨t.card, fun a => (t.equivFin.symm a : C), ?_⟩
  intro z hz
  have hz0 := hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz0
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz0.1 k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  set c : K → ℂ := fun k => (((Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ) with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    rw [hcdef]
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hpos k)).ne'
  have hck : ∀ k, ‖c k‖ ^ 2 = (∑ i, ‖z ⟨k, i⟩‖ ^ 2)⁻¹ := by
    intro k
    rw [hcdef]
    simp only
    rw [Complex.norm_real, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (hpos k).le]
  have hmem := torusSmul_mem_mcPts' P hP c hc z hz
  have hw : torusSmul c z ∈ S := by
    have hm := hmem
    simp only [mcPts, Set.mem_ofPred_eq] at hm
    simp only [hS, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hm.2⟩
    have e1 : ∀ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ‖z ⟨k, i⟩‖ ^ 2 := fun i => by
      show ‖c k * z ⟨k, i⟩‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum, hck k,
      inv_mul_cancel₀ (hpos k).ne']
  have hcov' := ht hw
  simp only [Set.mem_iUnion] at hcov'
  obtain ⟨i, hi, hiO⟩ := hcov'
  refine ⟨t.equivFin ⟨i, hi⟩, c, hc, ?_, hmem⟩
  show torusSmul c z ∈ O ((t.equivFin.symm (t.equivFin ⟨i, hi⟩) : C))
  rw [Equiv.symm_apply_apply]
  exact hiO

end GlobalTheory.CompanionTheory.Ar.ChartCover
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torus_translates_cover : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus | exact GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GP

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_coeff {r : ℕ} (b b₀ : Fin r → E) (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i)
    (hli : LinearIndependent Ω b) (i : Fin r) :
    ∃ t : Ω, t ≠ 0 ∧ b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i := by
  have hni : b i ∉ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := hli.notMem_span_image (by simp)
  have h1 : b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ (i+1) := by rw [← h]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [GlobalTheory.CompanionTheory.Ar.Flag.step_succ] at h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have ht : t ≠ 0 := by rintro rfl; apply hni; rw [h, ← hyz]; simpa using hy
  exact ⟨t, ht, by rw [← hyz]; simpa using hy⟩

theorem gr_isGen_of_frame (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ)
    (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) (hb : L.IsFrameAt b p) (i : Fin r) {t : Ω}
    (ht : t ≠ 0) (hy : b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p t := by
  refine ⟨ht, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro s ⟨e, he, hs⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have h2 : (∑ k, c k • b k) - (s / t) • b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := by
      rw [h]
      have : (∑ k, c k • b k) - (s / t) • b i =
          ((∑ k, c k • b k) - s • b₀ i) - (s / t) • (b i - t • b₀ i) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht]; abel
      rw [this]; exact sub_mem hs (Submodule.smul_mem _ _ hy)
    obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[Ω] Ω, ∀ k, φ (b k) = if k = i then 1 else 0 := by
      obtain ⟨g, hg⟩ := (Fintype.linearCombination Ω b).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro m hm; funext k; exact Fintype.linearIndependent_iff.1 hb.1 m (by simpa [Fintype.linearCombination_apply] using hm) k))
      refine ⟨(LinearMap.proj i).comp g, fun k => ?_⟩
      have := LinearMap.congr_fun hg (Pi.single k 1)
      simp [Fintype.linearCombination_apply_single] at this
      simp [this, Pi.single_apply, eq_comm]
    have h3 : GlobalTheory.CompanionTheory.Ar.flagStep Ω b i ≤ LinearMap.ker φ := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have : k ≠ i := by rintro rfl; simp at hk
      simp [hφ, this])
    have h4 := h3 h2
    have h5 : ∀ k, φ (c k • b k) = (c k : Ω) * φ (b k) := fun k => φ.map_smul (c k : Ω) (b k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mem_ker, map_sub, map_sum, h5, map_smul, hφ] at h4
    simp at h4
    refine Submodule.mem_span_singleton.2 ⟨c i, ?_⟩
    show (c i : Ω) * t = s
    rw [sub_eq_zero.1 h4, div_mul_cancel₀ _ ht]
  · rintro _ rfl
    exact ⟨b i, by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩, hy⟩

theorem gen_ratio {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    ∃ u : Ω, u ∈ regAt ξ p ∧ u⁻¹ ∈ regAt ξ p ∧ s = u * t := by
  have a1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self _
  have a2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs.2, ht.2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 a2
  have hu' : (u : Ω) * t = s := hu
  have hv' : (v : Ω) * s = t := hv
  have e : (v : Ω) * (u : Ω) = 1 := by
    refine mul_right_cancel₀ ht.1 ?_
    rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
  refine ⟨u, u.2, ?_, hu'.symm⟩
  rw [← eq_inv_of_mul_eq_one_left e]
  exact v.2

theorem gen_mul {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {t u : Ω} (h : Λ.IsGenAt p t) (h0 : u ≠ 0)
    (hu : u ∈ regAt ξ p) (hu' : u⁻¹ ∈ regAt ξ p) : Λ.IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero h0 h.1, ?_⟩
  rw [h.2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u⁻¹, hu'⟩, inv_mul_cancel_left₀ h0 _⟩
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

end Frames

section Pull

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {E E₀ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₀] [Module Ω₀ E₀]

theorem mem_flagStep_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {y : Fin r → E₀} {n : ℕ} {x : E₀} (hx : x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    j x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_pull_le {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {x y : Fin r → E₀} {n : ℕ} (h : GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ x n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (x k)) n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_flagStep_pull hj (h (Submodule.subset_span ⟨k, hk, rfl⟩))

theorem isFrameAt_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀))) {r : ℕ} {b : Fin r → E₀}
    (hb : L₀.IsFrameAt b p₀) : L.IsFrameAt (fun k => j (b k)) p := by
  refine ⟨hli _ _ hb.1, ?_⟩
  rw [hL]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ L₀ p₀ := he
    rw [hb.2] at he'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun k _ => ?_
    have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ p) • j (b k) := hj (c k : Ω₀) (b k)
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    refine ⟨b k, ?_, rfl⟩
    show b k ∈ L₀ p₀
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem isGenAt_pull (i : Ω₀ →+* Ω) (j : E₀ →+ E) {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    {r : ℕ} {c₀ : Fin r → E₀} {c : Fin r → E} (hc : ∀ a, j (c₀ a) = c a)
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀)))
    (hf : L₀.IsFlagVBOn Set.univ c₀) (a : Fin r) {t₀ : Ω₀} (h : (L₀.gr c₀ a).IsGenAt p₀ t₀) :
    (L.gr c a).IsGenAt p (i t₀) := by
  obtain ⟨U, hU, b₁, hb, hfr⟩ := hf p₀ trivial
  have hfr' := hfr p₀ trivial hU
  obtain ⟨t₁, ht₁, hy⟩ := exists_coeff b₁ c₀ hb hfr'.1 a
  have g₁ := gr_isGen_of_frame L₀ b₁ c₀ p₀ hb hfr' a ht₁ hy
  obtain ⟨u, hu, hu', rfl⟩ := gen_ratio h g₁
  have hc' : c = fun k => j (c₀ k) := funext fun a => (hc a).symm
  subst hc'
  have hframe : L.IsFrameAt (fun k => j (b₁ k)) p := isFrameAt_pull hreg hj hli hL hfr'
  have hadapt : ∀ n, GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (b₁ k)) n = GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) n :=
    fun n => le_antisymm (flagStep_pull_le hj (hb n).le) (flagStep_pull_le hj (hb n).ge)
  have hy' : j (b₁ a) - i t₁ • j (c₀ a) ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) a := by
    have := mem_flagStep_pull hj hy
    rwa [map_sub, hj] at this
  have g := gr_isGen_of_frame L (fun k => j (b₁ k)) (fun k => j (c₀ k)) p hadapt hframe a
    ((map_ne_zero i).2 ht₁) hy'
  have hu0 : u ≠ 0 := left_ne_zero_of_mul h.1
  rw [map_mul]
  refine gen_mul g ((map_ne_zero i).2 hu0) (hreg _ hu) ?_
  rw [← map_inv₀]
  exact hreg _ hu'

end Pull

theorem genPull_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hr hj hli hb hV
  intro q hq s a t₀ hg
  exact isGenAt_pull i j (hr q) hj hli (hb s) (hV q hq s) (Fl₀.sub s) a hg

end GlobalTheory.CompanionTheory.Ar.Chg.GP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecondStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames | exact GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames <;> assumption)
end
end
