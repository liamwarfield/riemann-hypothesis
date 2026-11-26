module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RestrSchA

variable {κ₁ κ : Type} {j : κ₁ → κ}

theorem extend_map {M N : Type} [Zero M] [Zero N] (hj : Function.Injective j) (φ : M → N) (h0 : φ 0 = 0)
    (y : κ₁ → M) : (fun i => φ (Function.extend j y 0 i)) = Function.extend j (fun a => φ (y a)) 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, h0]

theorem extend_add {M : Type} [AddZeroClass M] (hj : Function.Injective j) (y z : κ₁ → M) :
    Function.extend j (y + z) 0 = Function.extend j y 0 + Function.extend j z 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_smul {R M : Type} [Zero M] [SMulZeroClass R M] (hj : Function.Injective j) (c : R) (y : κ₁ → M) :
    Function.extend j (c • y) 0 = c • Function.extend j y 0 := by
  funext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem continuous_extend {M : Type} [TopologicalSpace M] [Zero M] (hj : Function.Injective j) :
    Continuous (fun y : κ₁ → M => Function.extend j y 0) := by
  refine continuous_pi fun i => ?_
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp only [hj.extend_apply]
    exact continuous_apply a
  · simp only [Function.extend_apply' _ _ _ h]
    exact continuous_const

theorem isClosedEmbedding_extend {M : Type} [TopologicalSpace M] [Zero M] [T2Space M] (hj : Function.Injective j) :
    Topology.IsClosedEmbedding (fun y : κ₁ → M => Function.extend j y 0) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : κ → M => x ∘ j)
    (fun y => by funext a; simp [hj.extend_apply]) (by fun_prop) (continuous_extend hj)

end GlobalTheory.RestrSchA

namespace GlobalTheory.RestrSchA

open scoped Classical

variable {κ₁ κ : Type} {j : κ₁ → κ}

def extL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (hj : Function.Injective j) :
    (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' y z := extend_add hj y z
  map_smul' c y := extend_smul hj c y
  cont := continuous_extend hj

theorem norm_le_extL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype κ₁] [Fintype κ]
    (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖extL V hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : extL V hj y (j a) = y a := by simp [extL, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm _ _

def restrS (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j) :
    SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ₁ → NumberField.mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (extL (NumberField.mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => by
      have := norm_le_extL hj y
      have h0 := norm_nonneg (extL (NumberField.mixedEmbedding.mixedSpace F) hj y)
      simp only [pow_one, one_mul]
      linarith⟩

theorem restrS_apply (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (y : κ₁ → NumberField.mixedEmbedding.mixedSpace F) :
    restrS F hj f y = f (Function.extend j y 0) := by
  simp [restrS, extL]

theorem sb_comp_extend (F : Type) [Field F] [NumberField F] (hj : Function.Injective j)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y => g (Function.extend j y 0)) ∈ SB (κ₁ → FiniteAdeleRing (𝓞 F) F) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
  exact ⟨hg.1.comp_continuous (continuous_extend hj), hg.2.comp_isClosedEmbedding (isClosedEmbedding_extend hj)⟩

theorem pureA_extend (F : Type) [Field F] [NumberField F] [Fintype κ₁] [Fintype κ] (hj : Function.Injective j)
    (f : SchwartzMap (κ → NumberField.mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (y : κ₁ → AdeleRing (𝓞 F) F) :
    pureA F f g (Function.extend j y 0) = pureA F (restrS F hj f) (fun z => g (Function.extend j z 0)) y := by
  simp only [pureA, restrS_apply]
  rw [extend_map hj (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
      (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0; exact map_zero _) y,
    extend_map hj (fun x : AdeleRing (𝓞 F) F => x.2) rfl y]

theorem mem_schA_comp_extend : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  intro F _ _ κ₁ κ _ _ j hj Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨restrS F hj f, fun z => g (Function.extend j z 0), sb_comp_extend F hj hg, ?_⟩
    funext y
    exact pureA_extend F hj f g y
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.RestrSchA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
namespace GlobalTheory.AdTh.MarkUniq

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem isDerivAt0_comp_lin {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 (fun z => e (L z)) w v) : IsDerivAt0 e (L w) v := by
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := by simpa only [map_zero] using h.1
  refine ⟨h0, fun U hU f => (h.2 U hU f).trans ?_⟩
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
    refine ⟨trivial, ?_⟩
    rw [← h0]
    intro x _
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
    ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
  let L' := LinearMap.toContinuousLinearMap L
  have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
    rw [map_zero]; exact hd.hasFDerivAt
  exact DFunLike.congr_fun (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv w

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)}

theorem ex_eq (F : FamilyUnif Xo s ty') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g' → ℂ)) (hP : IsPeriod (F.Di i) ty' P)
    (ex : (Fin g → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hol : IsHolTo Set.univ (fun z => (ex z).left)) (R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (v : ∀ j : Fin g, epsPt (F.u i P) ⟶ Xo.univ.t.G)
    (h1 : ∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (v j).left)
    (h2 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (R (Pi.single j 1)) (v j).left) (z : Fin g → ℂ) :
    F.ex i P (R z) = ex z := by
  have dk : DiscreteTopology {z // F.ex i P z = 1} := by
    have h0 : (fun z => F.ex i P z = 1) = fun z => z ∈ P.range := funext fun z => propext (F.ex_ker i P hP z)
    show DiscreteTopology (Subtype fun z => F.ex i P z = 1)
    rw [h0]
    exact hP.2.2.1
  have hol' := GlobalTheory.ExpChain.isHolTo_ex F i P hP
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre Xo.X Xo.X Xo.univ.t.G Xo.univ.t.G _ _ g g' ex (F.ex i P) (𝟙 _)
    (MonoidHom.id _) Xo.univ.t.semi.smooth hadd (F.ex_add i P hP) hol hol' (F.ex_diff i P hP) dk (Category.id_comp _)
    (fun x => Category.comp_id _)
  have hf : ∀ z, F.ex i P (f z) = ex z := hf
  have hfR : f = R := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    show f (Pi.single j 1) = R (Pi.single j 1)
    have h3 : IsDerivAt0 (fun z => (F.ex i P z).left) (f (Pi.single j 1)) (v j).left :=
      isDerivAt0_comp_lin hol' f (by simpa only [hf] using h1 j)
    exact ((F.ex_diff i P hP).2 (v j) (h2 j).1).unique h3 (h2 j)
  rw [← hfR, hf]

theorem exists_transport (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (Over.mk x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧
      (∀ w, ∃ v : epsPt x0 ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (F.ex i P z).left) w v.left) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        toUnit _ ≫ Xo.univ.eta a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  exact ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, fun w => ((F.ex_diff i P hP).1 w).exists, F.ex_eta i P hP⟩

theorem mark_congr {J : Type} (e : Fin g ≃ J) (e' : Fin g' ≃ J) (F : FamilyUnif Xo s ty) (F' : FamilyUnif Xo s ty')
    (i : Fin F.n) (i' : Fin F'.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F'.Di i').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F'.Di i') ty' P') (x : Sp ℂ ⟶ Xo.X) (hx : x = F.u i P)
    (hx' : x = F'.u i' P') (u : J → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hu : ∀ j, u j ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x)
    (h1 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single (e.symm j) 1) (u j))
    (h2 : ∀ j, IsDerivAt0 (fun z => (F'.ex i' P' z).left) (Pi.single (e'.symm j) 1) (u j))
    (gam : (F.Di i).La → (F'.Di i').La) (hg : ∀ a j, P' (gam a) j = P a (e.symm (e' j))) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ b, gam (F.t i a) = F'.t i' a + l.M • b := by
  classical
  intro a ha
  subst hx'
  obtain ⟨ex, hl, hadd, -, heta⟩ := exists_transport F i P hP _ hx
  have hl' : (fun z => (ex z).left) = fun z => (F.ex i P z).left := funext hl
  let R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := LinearMap.funLeft ℂ ℂ fun j => e.symm (e' j)
  have hR : ∀ j, R (Pi.single j 1) = Pi.single (e'.symm (e j)) 1 := fun j => by
    funext k
    show (Pi.single j (1 : ℂ) : Fin g → ℂ) (e.symm (e' k)) = _
    simp only [Pi.single_apply, Equiv.symm_apply_eq, Equiv.eq_symm_apply]
  have key := ex_eq F' i' P' hP' ex hadd (by rw [hl']; exact GlobalTheory.ExpChain.isHolTo_ex F i P hP) R
    (fun j => Over.homMk (u (e j)) (hu _))
    (fun j => by rw [hl']; have := h1 (e j); rw [Equiv.symm_apply_apply] at this; exact this)
    (fun j => by rw [hR]; exact h2 (e j))
  have h3 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a))) = F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (F'.t i' a)) := by
    rw [← F'.ex_eta i' P' hP' a ha, heta a ha, ← key, map_smul]
    congr 2
    exact funext (hg _)
  have h4 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a)) = 1 := by
    have h5 := F'.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a))
      ((l.M : ℂ)⁻¹ • P' (F'.t i' a))
    rw [sub_add_cancel, h3] at h5
    exact (mul_eq_right.1 h5.symm)
  obtain ⟨b, hb⟩ := (F'.ex_ker i' P' hP' _).1 h4
  have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨b, hP'.2.1 ?_⟩
  rw [map_add (f := _), map_nsmul, hb, ← smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hM, add_sub_cancel]

end Geo

end GlobalTheory.AdTh.MarkUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MarkUniq

theorem realM_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W t h := by
  have e : θ hτ.choose = t := GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (by
    have := hθ hτ.choose
    rwa [← hτ.choose_spec] at this) ht
  rw [realM, dite_eq_left hτ, ← e]
  rfl

theorem finVec_congr {D : D7} (W : HSp D) (N : ℕ) (p m q : Fin W.rank → D.host.E)
    (y w : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (h : p = m + N • q) (ew : finVec W p - y = N • w) :
    finVec W m - y = N • (w - finVec W q) := by
  funext i
  have e1 := congrFun ew i
  have e2 : finVec W p i = finVec W m i + N • finVec W q i := by
    rw [h]
    exact (map_add (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _).trans
      (congrArg _ (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _))
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e1 e2 ⊢
  rw [mul_sub, ← e1, e2]
  ring

theorem rat_eq_of_archM {D : D7} (W : HSp D) {γ γ' : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W) (τ : D.host.E →+* ℂ)
    (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) (h : archM W t γ = archM W t γ') : γ = γ' := by
  have key : ∀ δ : GA D W, ∀ δ₀ : GL (Fin W.rank) D.host.E,
      (∀ i j, (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j) → ∀ i j, archM W t δ i j = τ (δ₀.1 i j) := by
    intro δ δ₀ he i j
    change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j)) = _
    rw [he, Algebra.TensorProduct.map_tmul, map_one]
    exact ht.1 _
  obtain ⟨δ₀, -, he⟩ := hγ
  obtain ⟨δ₁, -, he'⟩ := hγ'
  have h0 : ∀ i j, (matHom W γ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  have h1 : ∀ i j, (matHom W γ').1 i j = (1 : AF D.host.F) ⊗ₜ δ₁.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he').symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  refine (h0 i j).trans (Eq.trans ?_ (h1 i j).symm)
  rw [τ.injective ((key γ δ₀ h0 i j).symm.trans ((congrFun (congrFun h i) j).trans (key γ' δ₁ h1 i j)))]

end GlobalTheory.AdTh.MarkUniq


open GlobalTheory.AdTh.MarkUniq in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.AdTh.dict_atComp_markAd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsInfFam θ → (∀ k, IsMod W hr (U.X k)) → (∀ k, IsOrthogonalFrame (U.X k) x₀) → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e F ik φ th x₀ → ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧ ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1) ∧ ∀ γ', AtComp θ W hr U.X dict x₀ h γ' → γ' = γ := by
  intro D H Dw l Xo c σ r U hσ hU hr1 hA θ W hr dict ι g e F ik φ th x₀ hθ hMod hx₀ hth hD Wt h
  subst hr
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 h
  obtain ⟨θ', hθ'⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D W θ' hθ'
  generalize hk : dict h = kx at hΛ hm hfr
  obtain ⟨k, x⟩ := kx
  dsimp only at hΛ hm hfr ⊢
  have hG : (U.X k).Gm = -W.gramᵀ := (hMod k).model.1
  obtain ⟨-, hu2, hu3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E W.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  have hfr' : ∀ τ : (U.X k).Ψ, mat x τ = archM W (θ' τ.1) (γ * h) * x₀ τ.1 := fun τ => by
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hθ' τ.1)]
    rfl
  have hmove : ∀ (γ' : GA D W) (τ : (U.X k).Ψ),
      mat (frMove θ W rfl (U.X k) γ' (fun τ => x₀ τ.1)) τ = archM W (θ' τ.1) γ' * x₀ τ.1 := fun γ' τ => by
    rw [← realM_mt hθ W γ' τ.1 (((hMod k).psi τ.1).1 τ.2) _ (hθ' τ.1)]
    rfl
  have hON : IsONFr (U.X k) x := fun τ => by
    rw [hfr', hu3 τ.1 _ _ (by rw [hG]; exact (hAr τ.1).2.2.2.2 _)]
    exact hx₀ k τ.1 τ.2
  have hdom : x ∈ (U.X k).dom := (hu2 x hON).1
  have hmem : ∀ v, v ∈ (U.X k).Λ ↔ v ∈ latG W (γ * h) := fun v => by
    rw [← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  refine ⟨hON, γ, ?_, ?_, ?_⟩
  · unfold AtComp
    rw [hk]
    refine ⟨hγ, SetLike.coe_injective hΛ.symm, funext fun τ => ?_⟩
    exact (hfr' τ).trans (hmove _ τ).symm
  · intro a ha
    obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x, hdom⟩
    obtain ⟨P', hPe', hP', hy', hd', -⟩ := Wt.pt k ⟨x, hdom⟩
    have hφ : ∀ v, Wt.φ k ((Wt.φ k).symm v) = v := (Wt.φ k).apply_symm_apply
    obtain ⟨b, hb⟩ := mark_congr e Wt.e F Wt.F (ik k) (Wt.ik k) P P' hP hP' _ hy hy'
      (fun j => (U.un k ⟨x, hdom⟩).u j.1 j.2) (fun j => ((U.un k ⟨x, hdom⟩).tan j.1 j.2).1)
      (fun j => hd j.1 j.2) (fun j => hd' j.1 j.2) (fun a => (Wt.φ k).symm (φ k a)) (fun a j => by
        rw [hPe, hPe', Equiv.apply_symm_apply]
        exact congrArg (fun v : (U.X k).Λ => perFr (U.X k) x (v : Fin W.rank → D.host.E) _ _) (hφ (φ k a))) a ha
    obtain ⟨w, hw, ew⟩ := hm a ha
    have hb' : (φ k (F.t (ik k) a) : Fin W.rank → D.host.E) =
        Wt.mark k a + l.M • (Wt.φ k b : Fin W.rank → D.host.E) := by
      have := congrArg (fun z => (Wt.φ k z : Fin W.rank → D.host.E)) hb
      simp only [map_add (f := _), map_nsmul] at this
      exact (congrArg Subtype.val (hφ _)).symm.trans this
    refine ⟨w - finVec W (Wt.φ k b : Fin W.rank → D.host.E), sub_mem hw
      (((GlobalTheory.MarkCoset.latG_spec D W _).1 _).1 ((hmem _).1 (Wt.φ k b).2)), ?_⟩
    exact finVec_congr W l.M _ _ _ _ _ hb' ew
  · intro γ' hγ'
    unfold AtComp at hγ'
    rw [hk] at hγ'
    obtain ⟨hq, -, hx⟩ := hγ'
    obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    have h1 : archM W (θ' τ) (γ' * h) * x₀ τ = archM W (θ' τ) (γ * h) * x₀ τ := by
      rw [← hmove _ ⟨τ, hτ⟩, ← hfr' ⟨τ, hτ⟩]
      exact congrArg (fun y => mat y ⟨τ, hτ⟩) hx.symm
    have hdet : IsUnit (x₀ τ).det :=
      (((hu2 (fun τ => x₀ τ.1) fun τ => hx₀ k τ.1 τ.2).1 ⟨τ, hτ⟩).1).isUnit
    have h2 : archM W (θ' τ) (γ' * h) = archM W (θ' τ) (γ * h) := by
      have := congrArg (· * (x₀ τ)⁻¹) h1
      simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] using this
    refine rat_eq_of_archM W hq hγ τ _ (hθ' τ) ?_
    have h3 : ∀ δ : GA D W, archM W (θ' τ) δ = archM W (θ' τ) (δ * h) * archM W (θ' τ) h⁻¹ := fun δ => by
      rw [← (hAr τ).2.1, mul_inv_cancel_right]
    rw [h3 γ', h3 γ, h2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisationStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_component_frame_marking_uniformisation : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsInfFam θ → (∀ k, IsMod W hr (U.X k)) → (∀ k, IsOrthogonalFrame (U.X k) x₀) → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e F ik φ th x₀ → ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧ ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1) ∧ ∀ γ', AtComp θ W hr U.X dict x₀ h γ' → γ' = γ := by
  first | exact @GlobalTheory.AdTh.dict_atComp_markAd | exact GlobalTheory.AdTh.dict_atComp_markAd | (intros; apply GlobalTheory.AdTh.dict_atComp_markAd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LabEq

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse]

theorem dualLab_length' (d : List ℤ) : (dualLab d).length = d.length := by
  simp [dualLab]

theorem dualLab_pairwise' (d : List ℤ) :
    (dualLab d).Pairwise (fun a b => b ≤ a) ↔ d.Pairwise (fun a b => b ≤ a) := by
  simp [dualLab, List.pairwise_reverse, List.pairwise_map]

theorem isLab_W_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ i P d, Good R A.μ0 P → (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P (dualLab d)) ∧ (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ i P d _
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  rw [GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, hW, hY, dualLab_length', dualLab_pairwise', dualLab_dualLab']
  refine ⟨?_, Iff.rfl⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun h => (h3 h).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun h => (h3 h).symm⟩

end GlobalTheory.LabEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ i P d, Good R A.μ0 P → (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P (dualLab d)) ∧ (IsLab (Wc D i) P d ↔ IsLab (Yc D 0) P d) := by
  first | exact @GlobalTheory.LabEq.isLab_W_iff | exact GlobalTheory.LabEq.isLab_W_iff | (intros; apply GlobalTheory.LabEq.isLab_W_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.HeckeBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compInf_eq_infTens (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem coe_infDiag (k : Eˣ) :
    (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem exists_tensor_adele_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ hcm
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc, hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

theorem exists_hchar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E,
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

end GlobalTheory.HeckeBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClassStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_of_idele_class : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E, (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧ ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m → H.HasInf (fun w => (τ w).1) m := by
  first | exact @GlobalTheory.HeckeBridge.exists_hchar | exact GlobalTheory.HeckeBridge.exists_hchar | (intros; apply GlobalTheory.HeckeBridge.exists_hchar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

def IsHalfIdem (D : D7) (ε : AE D) : Prop :=
  ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧
    (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧
    ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0

theorem exists_isHalfIdem (D : D7) : ∃ ε, IsHalfIdem D ε := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D

theorem finRat_eq (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T x = (1 - realIdem D) • (ratW T S x : WO S T) := by
  funext i j
  refine adele_ext ?_ ?_
  · exact (congrFun (congrFun (finRat_inf S T x) i) j).trans (congrFun (congrFun (fin_smul_fin (ratW T S x)) i) j).symm
  · show finPart D (ratW T S x i j) = finPart D ((1 - realIdem D) * ratW T S x i j)
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul]

theorem finRat_smul (S T : HSp D) (c : D.host.E) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T (c • x) = incA D c • finRat S T x := by
  rw [finRat_eq, finRat_eq, smul_comm]
  congr 1
  funext i j
  exact (incA D).map_mul c (x i j)

def latQ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | finRat S T x ∈ latO S T LS LT fun _ => True}
  add_mem' {x y} hx hy := by
    show finRat S T (x + y) ∈ latO S T LS LT fun _ => True
    rw [map_add (f := _)]
    exact add_mem hx hy
  zero_mem' := by
    show finRat S T 0 ∈ latO S T LS LT fun _ => True
    rw [map_zero]
    exact zero_mem _
  smul_mem' r x hx := by
    show finRat S T ((r : D.host.E) • x) ∈ latO S T LS LT fun _ => True
    rw [finRat_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latQ {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} :
    x ∈ latQ S T LS LT ↔ finRat S T x ∈ latO S T LS LT fun _ => True := Iff.rfl

def gamQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  ψ (symplO S T (finRat S T x) (finRat S T y))


open Classical in
def chiLat (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) : ℂ :=
  if (1 - realIdem D) • x ∈ latO S T LS LT (fun _ => True) then
    ψ (symplOH S T (intA D w • (1 - realIdem D) • x) ((1 - realIdem D) • x)) else 0

def serO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) : WO S T → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WO S T) (piW θ T S) (iotaW σ T S) (fun x y => ψ (symplOH S T x y))
    (omO S T) (jO S T sS sT) (ratL T S) (chiLat ψ S T LS LT w) a

def actR (S T : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : RW T S :=
  fun τ => (b τ * Matrix.of (v τ) * a τ : Matrix (Fin T.rank) (Fin S.rank) ℂ)

def gaussR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omO S T (actR S T a b v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (actR S T a b v - v) (jO S T sS sT (actR S T a b v - v)) : ℝ))

def sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    Module.End K (Matrix (Fin m) (Fin n) K) where
  toFun x := b * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandw_apply {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin m) (Fin n) K) : sandw b a x = b * x * a := rfl

theorem toMatrix_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) (sandw b a) = b ⊗ₖ aᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, sandw_apply]
  have : ∀ x : Matrix (Fin m) (Fin n) K, (Matrix.stdBasis K (Fin m) (Fin n)).repr x (i, j) = x i j := fun x => by
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem det_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a) = (b ⊗ₖ aᵀ).det := by
  rw [← toMatrix_sandw, LinearMap.det_toMatrix]

theorem det_sandw_sub_one {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a - 1) = (b ⊗ₖ aᵀ - 1).det := by
  rw [← toMatrix_sandw, ← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), map_sub, LinearMap.toMatrix_one]

end GlobalTheory.RatAut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem overK_of_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ)
    (h : σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD)) : OverK σ := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

theorem embLL_embE (D : D7) (x : D.host.E) : D.what₂.embLL (D.embE x) = D.host.φ₀ x :=
  RingHom.congr_fun D.embE_φ₀ x

theorem sqrtMinusD_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem overK_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (h : ¬ OverK σ) : OverK ((starRingEnd ℂ).comp σ) := by
  apply overK_of_sqrt
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have h1 : σ (D.embE D.host.sqrtMinusD) ^ 2 = D.what₂.embLL (D.embE D.host.sqrtMinusD) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sqrtMinusD_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd (overK_of_sqrt σ h2) h
  · rw [RingHom.comp_apply, h2, embLL_embE, h0]; simp

theorem exists_psi_of_overK {D : D7} (σ : D.what₂.LL →+* ℂ) (h : OverK σ) :
    ∃ g ∈ D.R.Psi, ∀ τ, labE σ τ = D.host.emb (g * (D.eTau τ).1) := by
  obtain ⟨g0, h0⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  refine ⟨g0, ((factEmb D.R D.host).2 _).1 ?_, fun τ => ?_⟩
  · have h1 := h D.host.sqrtMinusD (IntermediateField.mem_adjoin_simple_self ℚ _)
    have h2 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    rw [h0]
    exact h1.trans ((embLL_embE D _).trans h2)
  · rw [ConjReading.emb_mul, h0]; rfl

theorem labels_overK : ∀ {D : D7} (σ : D.what₂.LL →+* ℂ),
    (OverK σ → Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ) ∧
      (¬ OverK σ → OverK ((starRingEnd ℂ).comp σ)) := by
  intro D σ
  refine ⟨fun h => ?_, overK_conj σ⟩
  obtain ⟨g, hg, key⟩ := exists_psi_of_overK σ h
  have inj := (factEmb D.R D.host).1.1
  have main : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ := by
    intro ρ
    have hs : labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
      unfold lab; rw [dite_eq_left (ConjReading.lab_exists σ ρ)]; exact (ConjReading.lab_exists σ ρ).choose_spec
    refine hs.resolve_right fun h' => ?_
    rw [key] at h'
    exact ConjReading.conj_not_mem D ρ _ h' (Subgroup.mul_mem _ hg (D.eTau _).2)
  refine ⟨⟨fun ρ ρ' e => ?_, fun τ => ?_⟩, main⟩
  · have e' : tauE D ρ = tauE D ρ' := by rw [← main, ← main, e]
    exact D.eTau.injective (Subtype.ext (inj e'))
  · refine ⟨D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩, ?_⟩
    have e := main (D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩)
    rw [key, tauE, Equiv.apply_symm_apply] at e
    exact D.eTau.injective (Subtype.ext (mul_left_cancel (inj e)))

end GlobalTheory.GalLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F) in
def intF (N : ℕ) : Set (AF F) :=
  {x | ∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ x.2 = N • c}

theorem intF_one_mul {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x * y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c * d, fun v => mul_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 * y.2 = c * d
  rw [e, e']


variable (F E) in
def SE : AddSubgroup (AF F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}

theorem gen_mul {x y : AF F ⊗[F] E}
    (hx : x ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o})
    (hy : y ∈ {z | ∃ s ∈ intF F 1, ∃ o : 𝓞 E, z = algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o}) :
    x * y ∈ SE F E := by
  obtain ⟨s, hs, o, rfl⟩ := hx
  obtain ⟨s', hs', o', rfl⟩ := hy
  refine AddSubgroup.subset_closure ⟨s * s', intF_one_mul hs hs', o * o', ?_⟩
  have h : ((o * o' : 𝓞 E) : E) = (o : E) * o' := rfl
  rw [map_mul, h, map_mul]
  ring

theorem SE_mul {x y : AF F ⊗[F] E} (hx : x ∈ SE F E) (hy : y ∈ SE F E) : x * y ∈ SE F E := by
  induction hx using AddSubgroup.closure_induction with
  | mem g hg =>
    induction hy using AddSubgroup.closure_induction with
    | mem g' hg' => exact gen_mul hg hg'
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

theorem one_mem_SE : (1 : AF F ⊗[F] E) ∈ SE F E :=
  AddSubgroup.subset_closure ⟨1, ⟨1, fun v => one_mem _, by rw [one_smul]; rfl⟩, 1, by simp [Algebra.TensorProduct.one_def]⟩


variable (F E) in
def CE (N : ℕ) : AddSubgroup (AF F ⊗[F] E) := (SE F E).map (nsmulAddMonoidHom N)

theorem mem_CE {N : ℕ} {z : AF F ⊗[F] E} : z ∈ CE F E N ↔ ∃ s ∈ SE F E, N • s = z := by
  simp [CE]

theorem CE_step {N : ℕ} {x y : AF F ⊗[F] E} (hx : x - 1 ∈ CE F E N) (hy : y - 1 ∈ CE F E N) :
    x * y - 1 ∈ CE F E N := by
  obtain ⟨a, ha, ea⟩ := mem_CE.1 hx
  obtain ⟨b, hb, eb⟩ := mem_CE.1 hy
  refine mem_CE.2 ⟨a + b + N • (a * b), add_mem (add_mem ha hb) (nsmul_mem (SE_mul ha hb) N), ?_⟩
  rw [eq_add_of_sub_eq ea.symm, eq_add_of_sub_eq eb.symm]
  simp only [nsmul_eq_mul]
  ring


variable (F E) in
def WE (N : ℕ) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {z | (z : AF F ⊗[F] E) - 1 ∈ CE F E N ∧ ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 ∈ CE F E N}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul]; exact CE_step hx.1 hy.1,
    by rw [mul_inv_rev, Units.val_mul]; exact CE_step hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem cA_gen (σ : E →ₐ[F] E) (s : AF F) (o : 𝓞 E) :
    cA σ (algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o) =
      algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E (σ o) := by
  rw [map_mul, AlgHom.commutes]
  rfl

theorem cA_mem_SE (σ : E →ₐ[F] E) {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : cA σ z ∈ SE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [cA_gen]
    have : IsIntegral ℤ (σ (o : E)) := (o.2.map σ)
    exact AddSubgroup.subset_closure ⟨s, hs, ⟨σ o, this⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.HeckeExtend

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.UnitaryBC

namespace GlobalTheory.PolChar

theorem exists_compNorm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {χ : Formalism.L2.Host.HChar E} {u : ℝ},
    χ.IsAbsPow u → ∃ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E),
      GlobalTheory.GalOfCusp.compNorm E ψ = χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹ ∧
        ∀ v : InfinitePlace (maximalRealSubfield E), ψ.locInf v (-1) = 1 := by
  intro E _ _ _ χ u h
  refine ⟨resReal χ, Subtype.ext (MonoidHom.ext fun x => ?_), resReal_locInf_neg_one h⟩
  change χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
    χ.1 x * ((χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹)⁻¹
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, ideleConj_eq, inv_inv]

end GlobalTheory.PolChar
end
end
