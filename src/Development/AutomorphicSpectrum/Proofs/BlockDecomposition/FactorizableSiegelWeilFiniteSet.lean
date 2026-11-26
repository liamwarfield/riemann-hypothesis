module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PureCIsSchwartzBruhat
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem repr_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

end Coord

section Box

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_box (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v, IsCompact (C v))
    (hS : ∀ v, v ∉ S → C v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    IsCompact {y : Af F | ∀ v, y v ∈ C v} := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF
  have hcoe := RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)
  let K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) :=
    {x | ∀ v, x v ∈ C v}
  have hK : IsCompact K := by
    rw [hcoe.isCompact_iff]
    have : (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hx
        refine ⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩,
          fun v => hx v (Set.mem_univ v), rfl⟩
    rw [this]
    exact isCompact_univ_pi hC
  have himg := hK.image hemb.continuous
  have hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v :=
        Filter.eventually_principal.2 fun v hv => hS v hv (hy v)
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      exact hx v
  rw [hset]
  exact himg

end Box

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))


end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

namespace PureTuple

open NumberField IsDedekindDomain
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem coord_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    PureSB.coordH (Fv F v) b (projV v X a i) k = (PureSB.coordH (Af F) b (X a i) k) v :=
  PureSB.repr_map b (evalV F v) (X a i) k

theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → Fin n → Fin M → Fv F v ⊗[F] E) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h : (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X a i) = fun X =>
      (PureSB.coordH (Fv F v) b).symm (fun k => (PureSB.coordH (Af F) b (X a i) k) v) := by
    funext X
    apply (PureSB.coordH (Fv F v) b).injective
    rw [Homeomorph.apply_symm_apply]
    funext k
    exact coord_projV v b X a i k
  rw [h]
  refine (PureSB.coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)
  exact (RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp
    ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))

theorem projV_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ latV b v ↔ ∀ a i k, (PureSB.coordH (Af F) b (X a i) k) v ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_
  rw [← coord_projV v b X a i k]
  rfl

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))


include b in
theorem isClosed_boxF (hA : ∀ v, IsCompact (A v)) : IsClosed (boxF A) := by
  have h : boxF A = ⋂ v, projV v ⁻¹' A v := by
    ext X
    exact ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
  rw [h]
  refine isClosed_iInter fun v => ?_
  haveI : T2Space (Fv F v ⊗[F] E) := (PureSB.coordH (Fv F v) b).isEmbedding.t2Space
  exact (hA v).isClosed.preimage (continuous_projV v b)

theorem isOpen_boxF (hA : ∀ v, IsOpen (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) : IsOpen (boxF A) := by
  have hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hI : IsOpen {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} := by
    have e : {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
        PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} =
        ⋂ a, ⋂ i, ⋂ k, (fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k) ⁻¹'
          {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k :=
      (continuous_apply k).comp
        ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))
    exact hT.preimage hc
  have h : boxF A = {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩
      ⋂ v ∈ S, projV v ⁻¹' A v := by
    ext X
    constructor
    · intro hX
      refine ⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩
      have := hX v
      rw [hS v hv] at this
      exact (projV_mem_latV v b X).1 this a i k
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter₂.1 h2 v hv
      · rw [hS v hv]
        exact (projV_mem_latV v b X).2 fun a i k => h1 a i k v hv
  rw [h]
  exact hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))

theorem isCompact_boxF (hA : ∀ v, IsCompact (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    IsCompact (boxF A) := by
  let B : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun a i k v => (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => PureSB.coordH (Fv F v) b (Y a i) k) '' A v
  have hB : ∀ a i k v, IsCompact (B a i k v) := fun a i k v =>
    (hA v).image ((continuous_apply k).comp
      ((PureSB.coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))
  have hBS : ∀ a i k v, v ∉ S →
      B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro a i k v hv _ ⟨Y, hY, rfl⟩
    rw [hS v hv] at hY
    exact hY a i k
  let eW : (Fin n → Fin M → Af F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Af F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => PureSB.coordH (Af F) b
  have hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k =>
      {y : Af F | ∀ v, y v ∈ B a i k v}) :=
    eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun k => PureSB.isCompact_box S (B a i k) (hB a i k) (hBS a i k))
  refine hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_
  exact ⟨projV v X, hX v, coord_projV v b X a i k⟩

end PureTuple

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b S φ A hφ hA hS
  have hc := PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl := PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho := PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod hφ (Φf := (boxF A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.WhitFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSetStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorizable_siegel_weil_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProd
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitUnit

theorem compact_zpowers_fst {H : Type} [Group H] [TopologicalSpace H] [T2Space H] (t : H × H)
    (hc : IsCompact (closure (Subgroup.zpowers t : Set (H × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set H)) := by
  have hi : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (H × H))) := hc.image continuous_fst
  refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
  rintro x ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure ⟨k, rfl⟩, ?_⟩
  simp

theorem main : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  intro H _ _ _ _ σ K d d' _ hσ hK hd hd' hcpt hsurj
  refine ⟨?_, ?_⟩
  · rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    obtain ⟨h₁, h₂⟩ := (mem_twCent_swTw σ hσ d d' t).1 ht
    have hg : t.1 ∈ K :=
      hcpt (Subgroup.subset_closure ⟨h₁, compact_zpowers_fst t hc⟩)
    refine Subgroup.mem_prod.2 ⟨hg, ?_⟩
    rw [h₂]
    exact K.mul_mem (K.mul_mem hd' (hK _ hg)) (K.inv_mem hd')
  · rintro ⟨x₁, x₂⟩ hy
    have hy' := Subgroup.mem_prod.1 hy
    have hz₁ : x₁⁻¹ * d * σ x₂ ∈ K := by simpa [swTw] using hy'.1
    have hz₂ : x₂⁻¹ * d' * σ x₁ ∈ K := by simpa [swTw] using hy'.2
    have hN : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ ∈ K := by
      have e : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ = (x₁⁻¹ * d * σ x₂) * σ (x₂⁻¹ * d' * σ x₁) := by
        simp only [map_mul, map_inv, hσ, MonoidHom.id_apply]
        group
      rw [e]
      exact K.mul_mem hz₁ (hK _ hz₂)
    obtain ⟨g, hg, hk₁⟩ := hsurj x₁ hN
    refine ⟨(g, d' * σ g * d'⁻¹), (mem_twCent_swTw σ hσ d d' _).2 ⟨hg, rfl⟩,
      (g⁻¹ * x₁, d' * σ (g⁻¹ * x₁) * (x₂⁻¹ * d' * σ x₁)⁻¹), ?_, ?_⟩
    · exact Subgroup.mem_prod.2 ⟨hk₁, K.mul_mem (K.mul_mem hd' (hK _ hk₁)) (K.inv_mem hz₂)⟩
    · ext
      · simp
      · simp only [Prod.mk_mul_mk, map_mul, map_inv]
        group

end GlobalTheory.CompanionTheory.SplitUnit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProdStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_twist_compact_part_in_prod : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  first | exact @GlobalTheory.CompanionTheory.SplitUnit.main | exact GlobalTheory.CompanionTheory.SplitUnit.main | (intros; apply GlobalTheory.CompanionTheory.SplitUnit.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAll
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Grams

theorem sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n d b T hT
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (b k)
  have hJ' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (J i j)
  have hT' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ a c, inclR (F := F) (Fv F v) (T a c) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun c => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (T a c)
  have htr : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (Algebra.trace F E (b k))
  filter_upwards [Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (F := F) (1 / 2), hb, hJ', hT', htr,
    Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_crd_oev (E := E) b] with v hh hbv hJv hTv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ a i, X a i ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a i
    rw [hrepr (X a i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Formalism.L2.SG.Pf.NcS.IntWittPf.oev_smul' v (hX a i k) (hbv k)
  have hG : ∀ a c, hR (Fv F v) σ J (X a) (X c) ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    show ∑ i, ∑ j, sigR (Fv F v) σ (X a i) * JR (Fv F v) J i j * X c j ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (Formalism.L2.SG.Pf.NcS.IntWittPf.oev_sigR v σ (hx a i)) (hJv i j)) (hx c j)
  have hS : ∀ a c, ((hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X :
      HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    exact sub_mem (hTv a c) (hG a c)
  have htrace : ∀ z ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
    intro z hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrepr z, map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hz k) (htrv k)
  exact ⟨fun i => mul_mem hh (htrace _ (hS i i)), fun i j _ k => hc _ (hS i j) k⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.Grams
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAllStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gram_integral_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensionalStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_finite_dimensional : GlobalTheory.CompanionTheory.EGlue.PairFD := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairFD_holds | exact GlobalTheory.CompanionTheory.EGlue.pairFD_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairFD_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdClose
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdClose
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.MCl

theorem nodup_of_close {ε : ℝ} (hε : ε < 1 / 4) {m n : Multiset ℂ}
    (h : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n) (hg : GapM n) : m.Nodup := by
  induction h with
  | zero => exact Multiset.nodup_zero
  | @cons a b as bs hab hrel ih =>
    have hgn : (b ::ₘ bs).Nodup := hg.1
    have hb : b ∉ bs := (Multiset.nodup_cons.1 hgn).1
    have hg' : GapM bs := by
      refine ⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩
      exact hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy
    refine Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩
    obtain ⟨y, hy, hay⟩ := Multiset.exists_mem_of_rel_of_mem hrel ha
    have hne : b ≠ y := fun e => hb (e ▸ hy)
    have h1 := hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne
    have h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖ := by
      have : b - y = (a - y) - (a - b) := by ring
      rw [this]
      calc ‖(a - y) - (a - b)‖ ≤ ‖a - y‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - y‖ := add_comm _ _
    linarith

theorem prod_close (u : ℂ) (n : Multiset ℂ) : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : Multiset ℂ,
    Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n →
      ‖(m.map (u + ·)).prod - (n.map (u + ·)).prod‖ < δ := by
  induction n using Multiset.induction_on with
  | empty =>
    intro δ hδ
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have : m = 0 := Multiset.rel_zero_right.1 hm
    subst this
    simpa using hδ
  | cons b bs ih =>
    intro δ hδ
    have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod) :=
      continuous_mul.continuousAt
    obtain ⟨δ', hδ', H⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨ε₁, hε₁, H₁⟩ := ih δ' hδ'
    refine ⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩
    obtain ⟨a, as, hab, has, rfl⟩ := Multiset.rel_cons_right.1 hm
    have has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs :=
      has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)
    have h1 : ‖(u + a) - (u + b)‖ < δ' := by
      have e : (u + a) - (u + b) = a - b := by ring
      rw [e]
      have := hab.trans (min_le_right _ _)
      linarith
    have h2 := H₁ as has'
    have hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ' := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1, h2⟩
    have h3 := H hd
    rw [dist_eq_norm] at h3
    simpa [Multiset.map_cons, Multiset.prod_cons] using h3

end GlobalTheory.CompanionTheory.EGlue.MCl

namespace GlobalTheory.CompanionTheory.EGlue

theorem mCloseFacts_holds : MCloseFacts := by
  refine ⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg,
    fun m n hm u => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Multiset.exists_mem_of_rel_of_mem h hx
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    have h2 := hB y hy
    have h3 : ‖x - y‖ ≤ ε := hxy
    linarith
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, H⟩ := MCl.prod_close u n δ hδ
    filter_upwards [hm ε hε] with k hk
    rw [dist_eq_norm]
    exact H _ hk

end GlobalTheory.CompanionTheory.EGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdCloseStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_facts_alt : GlobalTheory.CompanionTheory.EGlue.MCloseFacts := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | exact GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandard
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxF A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxF A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxF A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ M n d b I c minf m hE
  obtain ⟨-, -, S₀, hS₀⟩ := hE
  refine ⟨S₀, fun S hS φ hφ hφi A hA hfin hoff => ?_⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hB := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurableSet_box b n M S A hA hoff
  have hp := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurable_projInf (E := E) b n M
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) :=
    {X | ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} with hBdef
  set P : ℝ := ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal with hP
  have hP0 : 0 ≤ P := tprod_nonneg fun _ => ENNReal.toReal_nonneg
  set K : ℝ≥0∞ := (c : ℝ≥0∞) * (∏ v ∈ S, m v (A v)) * ENNReal.ofReal P with hK
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.prod_ne_top fun v _ => hfin v)) ENNReal.ofReal_ne_top
  have hmap : (I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf = K • minf := by
    ext T hT
    rw [Measure.map_apply hp hT, Measure.restrict_apply (hp hT), Measure.smul_apply, smul_eq_mul]
    have hform := hS₀ S hS (T.indicator 1) (fun v => (A v).indicator 1)
      (measurable_one.indicator hT) (fun v => measurable_one.indicator (hA v))
    simp_rw [GlobalTheory.CompanionTheory.SW.EulerBox.pureL_indicator_eq b S _ A hoff] at hform
    rw [lintegral_indicator hB, lintegral_indicator_one hT] at hform
    have hl : ∫⁻ X in B, T.indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) ∂I =
        I (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T ∩ B) := by
      have : (fun X => T.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) =
          (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T).indicator 1 := by
        funext X
        by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projInf X ∈ T
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show X ∈ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
          rfl
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show X ∉ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
      rw [this, lintegral_indicator_one (hp hT), Measure.restrict_apply (hp hT)]
    rw [hl] at hform
    change _ = _ * _ * ENNReal.ofReal P at hform
    rw [hform]
    simp_rw [lintegral_indicator_one (hA _)]
    rw [hK]; ring
  have hfun : pureN φ A = B.indicator (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) :=
    funext fun X => pureN_eq_indicator φ A X
  refine ⟨?_, ?_⟩
  · have h1 : Integrable φ ((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [hmap]; exact hφi.smul_measure hKtop
    have h2 := (integrable_map_measure hφ.aestronglyMeasurable hp.aemeasurable).1 h1
    rw [hfun]
    exact IntegrableOn.integrable_indicator h2 hB
  · have h1 : ∫ X, pureN φ A X ∂I = ∫ Y, φ Y ∂((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [integral_map hp.aemeasurable hφ.aestronglyMeasurable, hfun]
      exact integral_indicator hB
    rw [h1, hmap, integral_smul_measure]
    have hKr : K.toReal = (c : ℝ) * (∏ v ∈ S, (m v (A v)).toReal) * P := by
      rw [hK, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hP0]
      simp
    rw [hKr, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WhitFree.Euler
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandardStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_almost_all_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN | exact GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN | (intros; apply GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinates
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem half_trace_eq (σ : E →ₐ[F] E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = (Θ z w).re := by
  have h4 := h.2.2.2 z w
  have h5 : e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = 2 * (Θ z w).re := by
    have := congrArg Complex.re h4
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
    rw [this]; ring
  rw [map_mul, Pi.mul_apply, he, h5, map_div₀, map_one, map_ofNat]
  ring

def evC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) : Ainf F ⊗[F] E →+* ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp (Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ))

theorem evC_apply (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) (z : Ainf F ⊗[F] E) :
    evC Θ w z = Θ z w := rfl

theorem coord_gramR (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    matC Θ (gramR (Ainf F) σ J X) w = gramC (J.map (τ w)) (tupC Θ X w) := by
  ext a c
  change evC Θ w (Formalism.UG.hform (sigR (Ainf F) σ) (JR (Ainf F) J) (X a) (X c)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, gramC, tupC, evC_apply, h.2.1, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show inclR (Ainf F) (J i j) = (1 : Ainf F) ⊗ₜ[F] (J i j) from rfl, h.2.2.1]

theorem coord_trace_mul (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) :
    Θ (Matrix.trace (B * G)) w = Matrix.trace (matC Θ B w * matC Θ G w) := by
  change evC Θ w _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  rfl

theorem gramC_smul {n M : ℕ} (c : ℂ) (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    gramC (c • J) X = c • gramC J X := by
  ext a b
  simp only [gramC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psiInf_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ ρ e τ Θ h he a ψ hψ M n J B X
  change ψ (pairA F _ 0) = _
  rw [hψ]
  congr 3
  rw [phaseM]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [half_trace_eq σ ρ e τ Θ h he, coord_trace_mul, coord_gramR σ e τ Θ h, gramC_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinatesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase <;> assumption)
end
end
