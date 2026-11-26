module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AdelicStabilizerLieKerPolarization
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.StabLieAdelic
end GlobalTheory.SquareAgree.StabLieAdelic
open GlobalTheory.SquareAgree.StabLieAdelic in
theorem GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N', ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ →
    ∃ ΨD ∈ N', ∃ Φ₁ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΨD Φ₁ ∧ IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₁ := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT Pi rf rl p p' _ N' hN τ Y hY
    ΦD hΦD Φ₀ hD
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hT γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb (hN.le hΦD)
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2
  have hΨalg : (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) ∈ algD Γ.M' Bs.ψ Bs.emb :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨δ (f i), φ i, (hδ _ (hf i).1).1, (hf i).2.1, (hf i).2.2, rfl⟩
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨN := hN.stabLie γ hγ _ hΦD _ hΨalg hder
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' _ hΨalg
  refine ⟨_, hΨN, Φ₁, hΦ₁, hD₁, ?_⟩
  intro z
  obtain ⟨u, rfl⟩ := cB.surjective z
  have hs : IsStd ψ := hO.psi ▸ hT.base.std
  have hg : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hw : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have key := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ₀ (cB u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
    funext t
    have h1 := (hO.weilB _ Φ₀ hD 1 (oneP θ X τ Y t)).2 u
    rw [conjU_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hD₁.2 u]
  exact key
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N', ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ →
    ∃ ΨD ∈ N', ∃ Φ₁ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΨD Φ₁ ∧ IsDer θ X (fun h => ωB (1, h)) τ Y Φ₀ Φ₁ := by
  first | exact @_root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic | exact _root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic | (intros; apply _root_.GlobalTheory.SquareAgree.StabLieAdelic.stabilizer_lie_adelic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AdelicStabilizerFiniteOfThetaSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.StabFinAdelic
private def infIncl_local (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun a := ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((a + b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) =
      ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) +
      ((b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((c • a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) =
      c • ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

private theorem smul_eq_zero_of_fst_local (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : u • x = 0 := by
  let e : AF F := ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - e) = 0 := by
    have : (1 - e).1 = 0 := by
      show ((1 : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) -
        ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)).1 = 0
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, this, map_zero]
  have hu' : u = u * e := by
    have := hu (1 - e) h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at this
    rw [mul_comm]; exact this
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (infIncl_local F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) *
        (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        (((show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).1, 0) :
          Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact one_mul _
      · exact zero_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

private theorem smul_mat_kapX_sub_one_local : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ),
    ∀ g ∈ GfC X, ∀ u : AF D.host.F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
    u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) - 1) = 0 := by
  intro D X d e J hJ g hg u hu
  rw [mat_kapX]
  have h1 : (infHom X g).val = 1 := by rw [show infHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F)
      (AlgHom.id D.host.F D.host.E) ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : Matrix.reindex e e (Formalism.L2.Theta.mt X g) - 1 = Matrix.reindex e e (Formalism.L2.Theta.mt X g - 1) := by
    ext i j
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_fst_local _ _ _ (hM _ _) u hu

theorem stabilizer_kappa_of_isThetaSubgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  classical
  intro hP D X a a' e Bs Γ Xc om om' hT hJ N' hN g hg Φ hΦ
  have hinf := smul_mat_kapX_sub_one_local D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  have hfix : ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
      T ⊆ S → S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin D.host.F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w) →
      om' (1, k) Ψ = Ψ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, -, hφ, hcof, rfl⟩ := hx
      refine ⟨hcof.toFinset, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      refine (hS₀ S hS₀S k hk1 hk2 hk3 hk4).2 f φ hφ fun w hw => ?_
      by_contra hne
      exact hw (hTS (Set.Finite.mem_toFinset _ |>.2 hne))
    | zero => exact ⟨∅, fun _ _ _ k _ _ _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, h₁⟩ := hx
      obtain ⟨T₂, h₂⟩ := hy
      refine ⟨T₁ ∪ T₂, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      rw [map_add (f := _), h₁ S (Finset.union_subset_left hTS) hS₀S k hk1 hk2 hk3 hk4,
        h₂ S (Finset.union_subset_right hTS) hS₀S k hk1 hk2 hk3 hk4]
    | smul c x _ hx =>
      obtain ⟨T, hT'⟩ := hx
      exact ⟨T, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => by rw [map_smul, hT' S hTS hS₀S k hk1 hk2 hk3 hk4]⟩
  obtain ⟨T, hTfix⟩ := hfix Φ (hN.le hΦ)
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T ∪ S₀)
  have hk : om' (1, k) Φ = Φ :=
    hTfix S (Finset.union_subset_left hTS) (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Ψ, om' (1, x * y) Ψ = om' (1, x) (om' (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      ∀ Ψ ∈ N', om' (1, (l'.map Prod.snd).prod) Ψ ∈ N' := by
    intro l'
    induction l' with
    | nil =>
      intro _ Ψ hΨ
      simp only [List.map_nil, List.prod_nil]
      rw [Prod.mk_one_one, map_one]
      exact hΨ
    | cons x l' ih =>
      intro hx Ψ hΨ
      simp only [List.map_cons, List.prod_cons]
      rw [split']
      exact hN.stabFin x.1 x.2 (hx x List.mem_cons_self) _
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) Ψ hΨ)
  rw [hprod, split', hk]
  exact key l (fun x hx => (hl x hx).2) Φ hΦ
end GlobalTheory.StabFinAdelic
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  first | exact @_root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | exact _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | (intros; apply _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerPMax
theorem ker_projection_maximal_thetaSubspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm N N' hN hN' hle
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT'.base.std
  obtain ⟨hz, hlin⟩ := isDatum_linear Γ.M' ψ hstd cB
  have hfun : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ → Φ₀ ∈ algF ψ θ false A₁ B := by
    intro ΦD hΦD Φ₀ hD
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD hΦD
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact hΦ₁
  let S : Submodule ℂ Pi :=
    { carrier := {x | ∃ ΦD ∈ N', ∃ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ ∧ p' Φ₀ = x}
      zero_mem' := ⟨0, N'.zero_mem, 0, hz, map_zero p'⟩
      add_mem' := by
        rintro _ _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩ ⟨ΨD, hΨD, Ψ₀, hE, rfl⟩
        refine ⟨ΦD + ΨD, N'.add_mem hΦD hΨD, Φ₀ + Ψ₀, ?_, map_add p' _ _⟩
        simpa using hlin ΦD ΨD Φ₀ Ψ₀ 1 hD hE
      smul_mem' := by
        rintro c _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
        refine ⟨c • ΦD, N'.smul_mem c hΦD, c • Φ₀, ?_, map_smul p' c Φ₀⟩
        simpa using hlin 0 ΦD 0 Φ₀ c hz hD }
  have hc1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  have hS1 : ∀ g ∈ GfC X, ∀ x ∈ S, rf g x ∈ S := by
    rintro g hg _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    have hΦ₀ := hfun ΦD (hN'.le hΦD) Φ₀ hD
    have hW := hO.weilB ΦD Φ₀ hD 1 g
    rw [hc1] at hW
    exact ⟨_, _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup hP D X W.rank W₁.rank e Bs Γ Xc om om' hT' hO.JX N' hN' g hg ΦD hΦD, _, hW,
      hm.mapB.eqf g hg Φ₀ hΦ₀⟩
  have hS2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, rl τ Y x ∈ S := by
    rintro τ Y hY _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    obtain ⟨ΨD, hΨD, Φ₁, hΦ₁, hE, hder⟩ := _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB
      hθ hT hO hT' Pi rf rl p p' hm N' hN' τ Y hY ΦD hΦD Φ₀ hD
    exact ⟨ΨD, hΨD, Φ₁, hE, hm.mapB.eql τ Y hY Φ₀ (hfun _ (hN'.le hΦD) _ hD) Φ₁ hΦ₁ hder⟩
  rcases hm.irred.2 S hS1 hS2 with h0 | h1
  · left
    refine le_antisymm (fun ΦD hΦD => ?_) hle
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD (hN'.le hΦD)
    have hx : p' Φ₁ ∈ S := ⟨ΦD, hΦD, Φ₁, hD₁, rfl⟩
    rw [h0, Submodule.mem_bot] at hx
    exact (hN ΦD).2 ⟨hN'.le hΦD, Φ₁, hΦ₁, hD₁, hx⟩
  · right
    refine le_antisymm hN'.le (fun ΨD hΨD => ?_)
    obtain ⟨Ψ₀, hΨ₀, hE⟩ := hO.algB' ΨD hΨD
    have hx : p' Ψ₀ ∈ S := h1 ▸ Submodule.mem_top
    obtain ⟨ΦD, hΦD, Φ₀, hD, hpe⟩ := hx
    have hdiff : ΨD - ΦD ∈ N := by
      refine (hN _).2 ⟨(algD _ _ _).sub_mem hΨD (hN'.le hΦD), Ψ₀ - Φ₀,
        (algF ψ θ false A₁ B).sub_mem hΨ₀ (hfun _ (hN'.le hΦD) _ hD), ?_, ?_⟩
      · simpa [sub_eq_add_neg] using hlin ΨD ΦD Ψ₀ Φ₀ (-1) hE hD
      · rw [map_sub, hpe, sub_self]
    simpa using N'.add_mem (hle hdiff) hΦD
end GlobalTheory.SquareAgree.KerPMax
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_projection_isMax : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | exact _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | (intros; apply _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace <;> assumption)
end
