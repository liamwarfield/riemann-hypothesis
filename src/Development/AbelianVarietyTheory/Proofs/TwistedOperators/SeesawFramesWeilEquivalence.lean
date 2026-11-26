module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorization
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Onto

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem map_darbAlg_eq_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (hpr : (M.Pol ψ τ).map pr = ⊤)
    (hpv : ∀ v, (GlobalTheory.WeilM.SB _).map (pv v) = ⊤) :
    (darbAlg M ψ τ).map (liftPure M pr pv s) = ⊤ := by
  classical
  have H := GlobalTheory.T.weil_model_projection_factorisation σ Y Z M ψ hM P pr N pv s hs
  have hq : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
    unfold liftPure
    rw [dite_eq_left H]
    exact H.choose_spec
  have key : ∀ (x : P) (ξ : ∀ v, N v), Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      x ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT s ξ ∈ (darbAlg M ψ τ).map (liftPure M pr pv s) := by
    intro x ξ hξ
    obtain ⟨f, hf, rfl⟩ : x ∈ (M.Pol ψ τ).map pr := hpr ▸ Submodule.mem_top
    have h1 : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), pv v φ = ξ v ∧ (pv v (M.vac v) = ξ v → φ = M.vac v) := by
      intro v
      by_cases hv : pv v (M.vac v) = ξ v
      · exact ⟨M.vac v, (hM.vac v).1, hv, fun _ => rfl⟩
      · obtain ⟨φ, hφ, e⟩ : ξ v ∈ (GlobalTheory.WeilM.SB _).map (pv v) := (hpv v) ▸ Submodule.mem_top
        exact ⟨φ, hφ, e, fun k => absurd k hv⟩
    choose φ hφ hφ1 hφ2 using h1
    have h2 : ∀ᶠ v in Filter.cofinite, φ v = M.vac v := by
      have h3 : ∀ᶠ v in Filter.cofinite, ξ v = s v := hξ
      filter_upwards [hs, h3] with v a b using hφ2 v (a.trans b.symm)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, Submodule.subset_span ⟨f, φ, hf, hφ, h2, rfl⟩, ?_⟩
    rw [hq f φ hφ h2, funext hφ1]
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  have hy : y ∈ Submodule.span ℂ {z | ∃ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ ∧ z = GlobalTheory.SmallThetaModules.pureT s ξ} := by
    rw [GlobalTheory.SmallThetaModules.pureT_span]; trivial
  rw [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨ξ, hξ, rfl⟩ := hz; exact key x ξ hξ
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ c ha

theorem map_thetaLift {D : D7} {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P)
    (hS : S ≤ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k))
    (T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ)
    (hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0) :
    (S.map T).map (thetaLift Mo ψ G e S pD) = S.map pD := by
  have H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ := by
    obtain ⟨q, hq⟩ := exists_factor T S (fun x hx => hinj x (hS hx)) pD
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have hq : ∀ Ψ ∈ S, thetaLift Mo ψ G e S pD (T Ψ) = pD Ψ := by
    intro Ψ hΨ
    rw [hT Ψ (hS hΨ)]
    unfold thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  ext x
  constructor
  · rintro ⟨_, ⟨Ψ, hΨ, rfl⟩, rfl⟩
    exact ⟨Ψ, hΨ, (hq Ψ hΨ).symm⟩
  · rintro ⟨Ψ, hΨ, rfl⟩
    exact ⟨T Ψ, ⟨Ψ, hΨ, rfl⟩, hq Ψ hΨ⟩

end GlobalTheory.TripleAssembly.Onto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.ReadDerB

private theorem pure_smul_twisted_operators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = M.vac v)) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    exact ⟨1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, hv⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h₁ j
      · simpa using h₂ j
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨m, f, φ, h, rfl⟩ := hx
    refine ⟨m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ τ).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    simp [Finset.smul_sum, pure_smul_twisted_operators]

end GlobalTheory.TripleAssembly.ReadDerB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.LieInv

theorem exists_factor {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_hasSig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_hasSig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hΨ
  have hg' := fun i => (g i).2
  simp only [Set.mem_setOf_eq] at hg'
  choose f φ hf hφ hφv hfe using hg'
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hφv i⟩, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfe i]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mul (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram)
    (g h : GA D M) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (g * h) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc h := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul]
  rfl

theorem conjU_one' (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} (c : D.host.E) (hc : J = c • M.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc 1 = 1 := by
  apply Subtype.ext
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one]
  rfl

theorem finTens_cA (z : AE D) : GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.cA D z) =
    Algebra.TensorProduct.map (AlgHom.id D.host.F _) D.sp.cm.sig (GlobalTheory.LFun.finTens D.host.F D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

theorem conjU_mem_UAt (M : HSp D) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) {g : GA D M} (hg : g ∈ GinfC M) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Yd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom M g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt M g a b) =
      (1 : Matrix (Fin M.rank) (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin M.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc g) i j = Formalism.L2.Theta.cA D (Formalism.L2.Theta.mt M g i j) := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  apply GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu
  rw [hm, map_sub, finTens_cA, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_line_conjU (θ : InfFam D) (M : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin M.rank) (Fin M.rank) ℂ)
    (hθ : IsInfFam θ) (hY : Y ∈ lieAt M τ) (Yd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (c : D.host.E)
    (hc : Yd.J = c • M.gram) :
    ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Yd, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y t) := by
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Yd.J :=
    { toFun := fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd t))
      map_one' := by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, conjU_one']
      map_mul' := fun s t => by
        show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hc (oneP θ M τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, conjU_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU M c hc).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact conjU_mem_UAt M Yd c hc (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end GlobalTheory.TripleAssembly.LieInv

namespace GlobalTheory.TripleAssembly.LieInv

variable {D : D7}

end GlobalTheory.TripleAssembly.LieInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ConjFinArch

variable {D : D7}

def eInf (F : Type) [Field F] [NumberField F] : AF F :=
  ((1 : Ainf F), (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

theorem one_sub_eInf_fst (F : Type) [Field F] [NumberField F] : (1 - eInf F).1 = 0 := by
  show (1 : Ainf F) - 1 = 0
  exact sub_self _

theorem evI_sub_eInf (F : Type) [Field F] [NumberField F] : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, one_sub_eInf_fst, map_zero]

theorem eInf_smul_tmul (a : AF D.host.F) (y : D.host.E) :
    eInf D.host.F • (a ⊗ₜ[D.host.F] y) = (eInf D.host.F * a) ⊗ₜ[D.host.F] y := by
  rfl

def incInf (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : AF F)
  map_add' x y := by
    show ((x + y, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (x + y, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    show ((c • x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (c • x, c • (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))
    rw [smul_zero]

theorem eInf_mul' (a : AF D.host.F) : eInf D.host.F * a = incInf D.host.F (fstA D.host.F a) := by
  show ((1 : Ainf D.host.F) * a.1, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * a.2) = (a.1, 0)
  rw [one_mul, zero_mul]

theorem cA_tmul (a : AF D.host.F) (y : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] y) = a ⊗ₜ[D.host.F] D.sp.cm.sig y := by
  show Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig (a ⊗ₜ[D.host.F] y) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem smul_tmul_AF (r a : AF D.host.F) (y : D.host.E) :
    r • (a ⊗ₜ[D.host.F] y) = (r * a) ⊗ₜ[D.host.F] y := rfl

theorem cA_smul (r : AF D.host.F) (x : AF D.host.F ⊗[D.host.F] D.host.E) : cA D (r • x) = r • cA D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a y => rw [smul_tmul_AF, cA_tmul, cA_tmul, smul_tmul_AF]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eInf_smul (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    eInf D.host.F • x = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  have key : DistribSMul.toLinearMap D.host.F (AF D.host.F ⊗[D.host.F] D.host.E) (eInf D.host.F) =
      (TensorProduct.map (incInf D.host.F) (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E)).comp
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toLinearMap := by
    refine TensorProduct.ext' fun a y => ?_
    show eInf D.host.F • (a ⊗ₜ[D.host.F] y) = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] y))
    rw [eInf_smul_tmul, eInf_mul', Algebra.TensorProduct.map_tmul]
    rfl
  exact LinearMap.congr_fun key x

theorem eInf_smul_eq_zero {x : AF D.host.F ⊗[D.host.F] D.host.E}
    (hx : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x = 0) : eInf D.host.F • x = 0 := by
  rw [eInf_smul, hx, map_zero]

theorem one_apply_map {R S : Type} [Semiring R] [Semiring S] {n : ℕ} (f : R →+* S) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eInf_smul_conjU_sub_one (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hJ : J = c • V.gram) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = 0 := by
  have hm : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = cA D (mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [map_sub, Matrix.sub_apply, one_apply_map]
    rfl
  have hinf : infHom V g = 1 := hg
  have he : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    have := congrArg (fun h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => h.1 i j) hinf
    exact this
  rw [hm, ← cA_smul, eInf_smul_eq_zero, map_zero]
  rw [map_sub, he]
  exact sub_eq_zero.2 (one_apply_map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom i j).symm

end GlobalTheory.ConjFinArch

theorem GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  intro D V J c hJ g hg u hu
  have h1 : (1 - GlobalTheory.ConjFinArch.eInf D.host.F) * u = 0 := hu _ (GlobalTheory.ConjFinArch.evI_sub_eInf _)
  have h2 : u = u * GlobalTheory.ConjFinArch.eInf D.host.F := by
    rw [sub_mul, one_mul, sub_eq_zero] at h1
    rw [mul_comm]; exact h1
  rw [h2, mul_smul]
  have h3 : GlobalTheory.ConjFinArch.eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.ConjFinArch.eInf_smul_conjU_sub_one V c hJ hg i j, Matrix.zero_apply]
  rw [h3, smul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | exact GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one | (intros; apply GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext; apply Units.ext
  show (GlobalTheory.TripleRead.toUX X e hJ 1).1.1 = 1
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]


end GlobalTheory.TripleAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawIdentityWeilTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.GoodComm

theorem exists_open_fix_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W₁ X : HSp D}
    {A₁ : Fr W₁} {B : Fr X} {χS χT : (AE D)ˣ →* Circle} {ωB : WRep W₁ X} (hW : IsWeilDatumO ψ W₁ X χS χT ωB)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ algF ψ θ false A₁ B) :
    ∃ U : Subgroup (GA D W₁), IsOpen (U : Set (GA D W₁)) ∧ ∀ k ∈ U, k ∈ GfC W₁ → ωB (k, 1) Ψ = Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, P, hf, rfl⟩ := hΦ
    obtain ⟨U, U', hU, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std W₁ X ωB
      (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf.1
    refine ⟨U, hU, fun k hk hkf => ?_⟩
    have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ W₁ X χS χT ωB hW θ hθ k hkf 1 (one_mem _)
      (frSgn false A₁).cart B.cart A₁.onb B.onb f P hf.1
    show ωB (k, 1) (fockF ψ θ false A₁ B f P) = fockF ψ θ false A₁ B f P
    unfold fockF
    exact e.trans (by rw [hfix k hk hkf 1 (one_mem _) (one_mem _)]; rfl)
  | zero => exact ⟨⊤, by simp, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨U', hU', h'⟩ := hy
    refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun k hk hkf => ?_⟩
    rw [map_add (f := _), h k (Subgroup.mem_inf.1 hk).1 hkf, h' k (Subgroup.mem_inf.1 hk).2 hkf]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf => by rw [map_smul, h k hk hkf]⟩

theorem comm_at_good_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωB : WRep W₁ X), IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, ∀ z : GA D W₁ →₀ ℂ,
      (∀ k ∈ z.support, k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) → ∀ i, ∃ u' ∈ GfC W₁,
        (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) = ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  classical
  intro D ψ θ hθ W₁ X A₁ B α β ωB hB n Ψ u hΨ hu
  have hW : IsWeilDatumO ψ W₁ X α (α / β) ωB := hB
  choose U hU hfix using fun i => exists_open_fix_algF (A₁ := A₁) (B := B) hθ hW (hΨ i)
  have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 D.host.F) | ¬ (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁)}.Finite := fun i =>
    ((GlobalTheory.PlaceGen.gen_by_local D W₁ (U i) (hU i)).1 (u i)).preimage Sum.inl_injective.injOn
  refine ⟨Finset.univ.biUnion fun i => (hfin i).toFinset, fun v hv z hz i => ?_⟩
  have hvi : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧ GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁ := by
    by_contra hc
    exact hv (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin i).mem_toFinset.2 hc⟩)
  set uv := GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i)) with huv
  have hfixv : ωB (uv, 1) (Ψ i) = Ψ i := hfix i uv hvi.1 hvi.2
  refine ⟨u i * uv⁻¹, mul_mem (hu i) (inv_mem hvi.2), ?_⟩
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i * uv⁻¹) = 1 := by
    rw [map_mul, map_inv, huv, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have m : ∀ (a b : GA D W₁) (f : WO W₁ X → ℂ), ωB (a * b, 1) f = ωB (a, 1) (ωB (b, 1) f) := fun a b f => by
    rw [show ((a * b, (1 : GA D X)) : GA D W₁ × GA D X) = (a, 1) * (b, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ k ∈ z.support, ωB (k, 1) (ωB (u i, 1) (Ψ i)) = ωB (u i * uv⁻¹, 1) (ωB (k, 1) (Ψ i)) := by
    intro k hk
    obtain ⟨x, rfl⟩ := hz k hk
    have hc := GlobalTheory.AdelicU.commute_emb D.sp.cm.sig W₁.gram x hp
    have e1 : GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * u i =
        (u i * uv⁻¹) * (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * uv) := by
      rw [← mul_assoc, ← hc.eq]; group
    rw [← m, e1, m (u i * uv⁻¹), m (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x) uv, hfixv]
  simp only [Finsupp.sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, key k hk]

end GlobalTheory.GoodComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_commute_at_good_places_algebraic_vectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωB : WRep W₁ X), IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, ∀ z : GA D W₁ →₀ ℂ,
      (∀ k ∈ z.support, k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) → ∀ i, ∃ u' ∈ GfC W₁,
        (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) = ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  first | exact @GlobalTheory.GoodComm.comm_at_good_place | exact GlobalTheory.GoodComm.comm_at_good_place | (intros; apply GlobalTheory.GoodComm.comm_at_good_place <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.RegGood

theorem isTriple_atPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hv : X.Good v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple { B with v₁ := v, τ₁ := t } G X om om' :=
  { h with
    base := { h.base with }
    geo := { h.geo with hV := { h.geo.hV with }, hV' := { h.geo.hV' with }, hW := { h.geo.hW with } }
    chars := { h.chars with good := hv } }

end GlobalTheory.RegGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Transport

theorem exists_factor {V Q P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup P] [Module ℂ P] (T : V →ₗ[ℂ] Q) (S : Submodule ℂ V) (hT : ∀ Φ ∈ S, T Φ = 0 → Φ = 0)
    (pD : V →ₗ[ℂ] P) : ∃ q : Q →ₗ[ℂ] P, ∀ Ψ ∈ S, q (T Ψ) = pD Ψ := by
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hT x.1 x.2 hx)
  let eq := LinearEquiv.ofInjective (T ∘ₗ S.subtype) hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((pD ∘ₗ S.subtype) ∘ₗ eq.symm.toLinearMap)
  refine ⟨g, fun Ψ hΨ => ?_⟩
  have h1 : g (T Ψ) = (g ∘ₗ (LinearMap.range (T ∘ₗ S.subtype)).subtype) (eq ⟨Ψ, hΨ⟩) := rfl
  rw [h1, hg]
  simp

end GlobalTheory.TripleAssembly.Transport
end
