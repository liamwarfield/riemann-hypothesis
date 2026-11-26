module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}}

def secMap {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ _ _

theorem secMap_apply {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (x : Γ(F, U)) :
    secMap φ U x = φ.app U x := rfl

theorem secMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (U : X.Opens) (x : Γ(F, U)) :
    secMap ψ U (secMap φ U x) = secMap (φ ≫ ψ) U x := by
  rw [secMap_apply, secMap_apply, secMap_apply, Scheme.Modules.Hom.comp_app]
  rfl

theorem isCoherent_copies {k : ℕ} {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent (⨁ fun _ : Fin k => F) := by
  haveI : SheafOfModules.IsQuasicoherent F := hF.1
  refine And.intro (isQuasicoherent_biproduct _) fun U hU => ?_
  haveI : Module.Finite Γ(X, U) Γ(F, U) := hF.2 U hU
  let L : (Fin k → Γ(F, U)) →ₗ[Γ(X, U)] Γ(⨁ fun _ : Fin k => F, U) :=
    ∑ j, (secMap (biproduct.ι (fun _ : Fin k => F) j) U).comp (LinearMap.proj (R := Γ(X, U)) j)
  refine Module.Finite.of_surjective L fun m =>
    ⟨fun j => secMap (biproduct.π (fun _ : Fin k => F) j) U m, ?_⟩
  refine Eq.trans ?_ (biproduct_app_eq_sum (fun _ : Fin k => F) U m).symm
  simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    secMap_apply]

variable {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}

theorem iSup_range_diagOp (h : OpSeq k M T d) (U : X.affineOpens) (e : ℕ) :
    ⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens)) = ⊤ := by
  have key : ∀ c : Fin k, ⊤ ≤ (⨆ j, LinearMap.range (secMap (diagOp T d j e) (U : X.Opens))).comap
      (secMap (biproduct.ι (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens)) := by
    intro c
    rw [← h.gen (d + e) (Nat.le_add_right d e) U]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem i (LinearMap.mem_range.mpr
      ⟨secMap (biproduct.ι (fun _ : Fin k => M (d + e)) c) (U : X.Opens) x, ?_⟩)
    rw [secMap_comp, ← secMap_apply (T i (d + e)), secMap_comp]
    rw [show biproduct.ι (fun _ : Fin k => M (d + e)) c ≫ diagOp T d i e =
        T i (d + e) ≫ biproduct.ι (fun _ : Fin k => M (d + e + 1)) c by
          unfold diagOp
          exact biproduct.ι_map _ _]
  rw [eq_top_iff]
  intro m _
  rw [biproduct_app_eq_sum (fun _ : Fin k => M (d + e + 1)) (U : X.Opens) m]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hc := Submodule.mem_comap.mp (key c (Submodule.mem_top
    (x := secMap (biproduct.π (fun _ : Fin k => M (d + e + 1)) c) (U : X.Opens) m)))
  rwa [secMap_apply, secMap_apply] at hc

theorem kerSeq_gen_bounded : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  intro hGN X _ k M T d h U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hfin : ∀ e, Module.Finite Γ(X, U) Γ(sumN M k d e, U) := fun e =>
    (isCoherent_copies (k := k) (h.coherent (d + e))).2 U U.2
  obtain ⟨d', hd'⟩ := hGN Γ(X, U) k (fun e => Γ(sumN M k d e, U))
    (fun j e => secMap (diagOp T d j e) (U : X.Opens))
    (fun i j e x => by
      rw [secMap_comp, secMap_comp, diagOp_comm T h.comm d i j e])
    0 (fun e _ => iSup_range_diagOp h U e)
    (fun e => LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens)))
    (fun i e => by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      refine LinearMap.mem_range.mpr ⟨secMap (kerOp T h.comm d i e) (U : X.Opens) x, ?_⟩
      rw [secMap_comp, secMap_comp, kerOp_ι])
  refine ⟨d', fun e he => ?_⟩
  have hd'' : ⨆ i, Submodule.map (secMap (diagOp T d i e) (U : X.Opens))
      (LinearMap.range (secMap (kernel.ι (sumMap T d e)) (U : X.Opens))) =
      LinearMap.range (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) := hd' e he
  have hinj : Function.Injective (secMap (kernel.ι (sumMap T d (e + 1))) (U : X.Opens)) :=
    GlobalTheory.QCoh.app_injective_of_mono _ _
  apply Submodule.map_injective_of_injective hinj
  have hS : Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) =
      ⨆ i, LinearMap.range (secMap (kerOp T h.comm d i e) (U : X.Opens)) := by
    rw [Submodule.iSup_eq_span]
    simp only [LinearMap.coe_range]
    rfl
  rw [hS, Submodule.map_iSup, Submodule.map_top, ← hd'']
  refine iSup_congr fun i => ?_
  rw [← LinearMap.range_comp, ← LinearMap.range_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply]
  rw [secMap_comp, secMap_comp, kerOp_ι]

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventuallyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_operators_span_eventually : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | exact GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SimTheta

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_UJ_smul_iff (s : A →+* A) (J : Matrix n n A) (c d : A) (hdc : d * c = 1) (u : GL n A) :
    u ∈ UJ s (c • J) ↔ u ∈ UJ s J := by
  have hscale : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) =
      c • (cT s (u : Matrix n n A) * J * (u : Matrix n n A)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h
    have h' : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J := h
    rw [hscale] at h'
    change cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J
    have h2 := congrArg (fun B : Matrix n n A => d • B) h'
    simpa only [smul_smul, hdc, one_smul] using h2
  · intro h
    have h' : cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J := h
    change cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J
    rw [hscale, h']

theorem conj_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G * u * G⁻¹ ∈ UJ s J := by
  refine GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ s J G u ?_
  rw [hG]
  exact (mem_UJ_smul_iff s J c d hdc u).2 hu

theorem conj_inv_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s J := by
  have h := GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ s J G u hu
  rw [hG] at h
  exact (mem_UJ_smul_iff s J c d hdc _).1 h

end Generic

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_smul (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (c : E)
    (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (c • J) = inclR (F := F) R c • JR (F := F) R J := by
  ext i j
  simp [JR, Matrix.map_apply]

theorem gramE_smul (σ : E →ₐ[F] E) {M n : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramE σ (c • J) X = c • gramE σ J X := by
  ext a b
  simp only [gramE, hE, hform, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (c : E)
    (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = c • T} where
  toFun X := ⟨SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [SWIsom.gramE_ratAct, hg, gramE_smul, this]⟩
  invFun Y := ⟨SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have hY := Y.2
    simp only [Set.mem_setOf_eq] at hY ⊢
    have h1 : gramE σ J (SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E)
        (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1)) =
        c • gramE σ J (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1) := by
      rw [SWIsom.gramE_ratAct, hg, gramE_smul]
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one, hY] at h1
    exact (smul_right_injective _ hc h1).symm⟩
  left_inv X := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ X.1) = X.1
    rw [SWIsom.ratAct_mul, Units.inv_mul, SWIsom.ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ Y.1) = Y.1
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one]

end Alg

theorem unitaryConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (l : F) (hl : l ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) =
      (algebraMap F E l) • J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    ∃ e : HA R σ J ≃ₜ* HA R σ J,
      (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J u * (bc (inclR R) g)⁻¹) ∧
      ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J u ∈ HFin R σ J := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hdcE : algebraMap F E l⁻¹ * algebraMap F E l = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hl, map_one]
  have hdcR : inclR (F := F) R (algebraMap F E l⁻¹) * inclR (F := F) R (algebraMap F E l) = 1 := by
    rw [← map_mul, hdcE, map_one]
  have hGR : cT (sigR R σ) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = inclR (F := F) R (algebraMap F E l) • JR R J := by
    rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hg, JR_smul]
  have h₁ : ∀ u ∈ HR R σ J, G * u * G⁻¹ ∈ HR R σ J := fun u hu =>
    conj_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  have h₂ : ∀ u ∈ HR R σ J, G⁻¹ * u * G ∈ HR R σ J := fun u hu =>
    conj_inv_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  refine ⟨GlobalTheory.CompanionTheory.SW.HIsom.conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ J u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ J u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ J u := hwu
    simp only [map_mul, map_inv, this, ← hG]

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (c : E) (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ J ≃ᵐ HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ J u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ J (μ.map He.symm) (He ⁻¹' 𝓕) {X | gramE σ J X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = c • T} := by
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := SWIsom.measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass] <;> try exact hmG.aemeasurable
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Measure.map_sum hmG.aemeasurable, ← SWIsom.sum_reindex (gramEquiv σ J g c hc hg T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) ((gramEquiv σ J g c hc hg T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := SWIsom.act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← SWIsom.ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem theta_simil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ 𝓕 hμ h𝓕 γ l hl hγ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := unitaryConj F E σ hCM M J γ l hl hγ (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M J (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M J (μ.map He.symm) (He ⁻¹' 𝓕) :=
    SWIsom.isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hc : algebraMap F E l ≠ 0 := by
    simpa using hl
  refine ⟨_, _, hμ', h𝓕', ?_⟩
  intro n T T' hT'
  subst hT'
  exact theta_map σ hCM J hJ γ _ hc hγ He hmat μ 𝓕 T

end GlobalTheory.CompanionTheory.SW.SimTheta
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitudeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  first | exact @GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | exact GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | (intros; apply GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup
noncomputable section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotProduct

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul₂ G₁] [MeasurableMul₂ G₂] {T₁ : Subgroup G₁} {T₂ : Subgroup G₂}
  {ν₁ : Measure T₁} [SFinite ν₁] {ν₂ : Measure T₂} [SFinite ν₂] {ν : Measure (T₁.prod T₂)}

def split (t : T₁.prod T₂) : T₁ × T₂ :=
  (⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩)

theorem measurable_split : Measurable (split : T₁.prod T₂ → T₁ × T₂) :=
  ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

theorem lintegral_prod_subgroup (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : Measurable ρ) (g : G₁ × G₂) :
    ∫⁻ h : T₁.prod T₂, ρ ((h : G₁ × G₂) * g) ∂ν =
      ∫⁻ t₁ : T₁, ∫⁻ t₂ : T₂, ρ ((t₁ : G₁) * g.1, (t₂ : G₂) * g.2) ∂ν₂ ∂ν₁ := by
  have hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2) :=
    hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))
  rw [← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]
  rfl

theorem normaliser_fst (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₁ ν₁ fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂)))
    (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩
  have h := hρ.2 (g, 1)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  simpa using h

theorem normaliser_snd (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₂ ν₂ fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1))
    (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩
  have h := hρ.2 (1, g)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  rw [lintegral_lintegral_swap]
  · simpa using h
  · have hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g) :=
      hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk
        ((measurable_subtype_coe.comp measurable_fst).mul_const g))
    exact hm.aemeasurable

theorem normaliser_mul (hν : ν.map split = ν₁.prod ν₂) {ρ₁ : G₁ → ℝ≥0∞} {ρ₂ : G₂ → ℝ≥0∞}
    (h₁ : IsQuotNormaliser T₁ ν₁ ρ₁) (h₂ : IsQuotNormaliser T₂ ν₂ ρ₂) :
    IsQuotNormaliser (T₁.prod T₂) ν fun x => ρ₁ x.1 * ρ₂ x.2 := by
  have hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2 :=
    (h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)
  refine ⟨hm, fun g => ?_⟩
  rw [lintegral_prod_subgroup hν hm]
  have hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ =
      ρ₁ ((t₁ : G₁) * g.1) := fun t₁ => by
    have hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2) :=
      h₂.1.comp (measurable_subtype_coe.mul_const g.2)
    rw [lintegral_const_mul _ hm₂, h₂.2, mul_one]
  simp only [hc]
  exact h₁.2 g.1

end GlobalTheory.CompanionTheory.QuotProduct

namespace GlobalTheory.CompanionTheory.QuotProduct

theorem quotProd_holds : PositivityTheory.Rg.BcB.D4.QuotProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib
  by_cases hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hν' : ν.map split = ν₁.prod ν₂ := hν
    have n₁ := normaliser_fst hν' hρ
    have n₂ := normaliser_snd hν' hρ
    have n := normaliser_mul hν' n₁ n₂
    set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂
    set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁
    rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]
    by_cases hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)
    · rw [integral_prod_symm _ hi]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      have hFx : Measurable fun x₁ => F (x₁, x₂) := hF.comp (measurable_id.prodMk measurable_const)
      have hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂) := fun h hh g => by
        simpa using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)
      have hq := hfib x₂
      rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁] at hq
      have : ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) =
          (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ) := fun x₁ => by
        rw [ENNReal.toReal_mul]; push_cast; ring
      simp only [this, Pi.zero_apply]
      rw [integral_mul_const, hq, zero_mul]
    · exact integral_undef hi
  · simp only [quotIntegral, dif_neg hex]

theorem quotProd_of_normEq : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.D4.QuotProd :=
  fun _ => quotProd_holds

end GlobalTheory.CompanionTheory.QuotProduct

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

private theorem sum_amat_first_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ a, Formalism.REAL.Amat l a j = l j - ((j : ℕ) : ℂ) := by
  have h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0) := by
    intro a
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : a = j
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  simp [sub_eq_add_neg]

private theorem sum_amat_second_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ b, Formalism.REAL.Amat l j b = l j - ((n - 1 - j : ℕ) : ℂ) := by
  have h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0) := by
    intro b
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : j = b
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi]
  simp [sub_eq_add_neg]

private theorem gelfVal_two_eq_sum_sq_sub_sq {n : ℕ} (c : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal c 2 = ∑ j, (c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
  have key : ∀ j : Fin n,
      (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
        (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) =
        c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2 := by
    intro j
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    rw [sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    ring
  calc GlobalTheory.Dec.gelfVal c 2
      = ∑ j, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
          (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) := by
        simp only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => key j

theorem conj_cas_of_isHerm {n : ℕ} {χ : Inf n} (h : IsHerm χ) : conj (cas χ) = cas χ := by
  obtain ⟨σ, hσ⟩ := h
  have hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2 := by
    rw [← Equiv.sum_comp σ (fun a => χ false a ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσ a, neg_sq]
  have hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2 := by
    have h2 := congrArg conj hT
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_pow] using h2.symm
  have hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) := by
    intro j
    simp only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]
  have hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) =
      ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [gelfVal_two_eq_sum_sq_sub_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sub, map_pow, map_pow, hK]
  simp only [cas]
  rw [map_mul, map_add (f := _), hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]
  simp only [Finset.sum_sub_distrib]
  rw [hT, hF]
  ring

theorem conj_cosh_mul_sqrt {c : ℂ} (hc : conj c = c) (t : ℝ) :
    conj (Complex.cosh (t * c ^ (1 / 2 : ℂ))) = Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  have hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    have h := Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero
    simpa [one_div] using h
  have hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [← map_pow, hw2, hc]
  rw [← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · rw [h, mul_neg, Complex.cosh_neg]

theorem conj_coshT_cas : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T →
    conj (coshT g (cas χ)) = coshT g (cas χ) := by
  intro n χ g T hχ _
  have hc := conj_cas_of_isHerm hχ
  simp only [coshT]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirRealStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfRight
noncomputable section

open NumberField Matrix
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.CompanionTheory.NonEll

variable {n : ℕ}

def formB (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)

def nrmC (D : GL (Fin n) ℂ) : GL (Fin n) ℂ := D * thetaR (starRingEnd ℂ) n D

theorem mem_perpD_iff (D : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perpD (starRingEnd ℂ) D W ↔ ∀ x ∈ W, formB D x y = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  constructor
  · rintro hy x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
    have := hu x hx
    simpa [formB, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hiD, dotProduct] using this
  · intro h
    refine Submodule.mem_map.2 ⟨(D⁻¹ : GL (Fin n) ℂ).val *ᵥ y, fun x hx => ?_, ?_⟩
    · simpa [formB, dotProduct] using h x hx
    · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDi]

theorem formB_nrm (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) :
    formB D ((nrmC D).val *ᵥ x) ((nrmC D).val *ᵥ y) = formB D x y := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  have hG : (nrmC D).val = D.val * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
    simp only [nrmC, Units.val_mul, thetaR_val]
    rfl
  have hH : ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ * (D.val)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hK : (nrmC D).valᴴ * (D⁻¹ : GL (Fin n) ℂ).val * (nrmC D).val = (D⁻¹ : GL (Fin n) ℂ).val := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = (D⁻¹ : GL (Fin n) ℂ).val * (D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val * D.val) *
          ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (D⁻¹ : GL (Fin n) ℂ).val * ((D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ) := by
          rw [hiD, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [← Matrix.conjTranspose_mul, hiD, Matrix.conjTranspose_one, Matrix.mul_one]
  unfold formB
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hK]

theorem formB_smul_left (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D (c • x) y = conj c * formB D x y := by
  simp [formB, dotProduct, Finset.mul_sum, mul_assoc]

theorem formB_smul_right (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D x (c • y) = c * formB D x y := by
  simp [formB, Matrix.mulVec_smul, dotProduct_smul]

theorem formB_add_left (D : GL (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    formB D (x + x') y = formB D x y + formB D x' y := by
  simp [formB, star_add, add_dotProduct]

theorem formB_add_right (D : GL (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    formB D x (y + y') = formB D x y + formB D x y' := by
  simp [formB, Matrix.mulVec_add, dotProduct_add]

theorem formB_zero_left (D : GL (Fin n) ℂ) (y : Fin n → ℂ) : formB D 0 y = 0 := by simp [formB]

theorem formB_zero_right (D : GL (Fin n) ℂ) (x : Fin n → ℂ) : formB D x 0 = 0 := by simp [formB]

theorem eq_zero_of_left (D : GL (Fin n) ℂ) (x : Fin n → ℂ) (h : ∀ y, formB D x y = 0) : x = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have h1 := h (D.val *ᵥ x)
  simp only [formB, Matrix.mulVec_mulVec] at h1
  rw [show (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 by simp, Matrix.one_mulVec] at h1
  exact dotProduct_star_self_eq_zero.1 h1

theorem eq_zero_of_right (D : GL (Fin n) ℂ) (y : Fin n → ℂ) (h : ∀ x, formB D x y = 0) : y = 0 := by
  have h1 := h ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)
  have h2 : (D⁻¹ : GL (Fin n) ℂ).val *ᵥ y = 0 := dotProduct_star_self_eq_zero.1 h1
  have h3 := congrArg (fun w => D.val *ᵥ w) h2
  simpa [Matrix.mulVec_mulVec] using h3

abbrev endN (D : GL (Fin n) ℂ) : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' (nrmC D).val

theorem eigen_pair (D : GL (Fin n) ℂ) {μ ν : ℂ} {x y : Fin n → ℂ} (hx : x ∈ (endN D).eigenspace μ)
    (hy : y ∈ (endN D).eigenspace ν) (h : conj μ * ν ≠ 1) : formB D x y = 0 := by
  have e1 : (nrmC D).val *ᵥ x = μ • x := by simpa using Module.End.mem_eigenspace_iff.1 hx
  have e2 : (nrmC D).val *ᵥ y = ν • y := by simpa using Module.End.mem_eigenspace_iff.1 hy
  have := formB_nrm D x y
  rw [e1, e2, formB_smul_left, formB_smul_right, ← mul_assoc] at this
  by_contra h0
  exact h (mul_right_cancel₀ h0 (by rw [this, one_mul]))

def eigSum (D : GL (Fin n) ℂ) (P : ℂ → Prop) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ μ : {μ : ℂ // P μ}, (endN D).eigenspace μ

theorem eigen_le (D : GL (Fin n) ℂ) {P : ℂ → Prop} {μ : ℂ} (h : P μ) :
    (endN D).eigenspace μ ≤ eigSum D P :=
  le_iSup (fun μ : {μ : ℂ // P μ} => (endN D).eigenspace μ) ⟨μ, h⟩

theorem eigSum_orth (D : GL (Fin n) ℂ) {P Q : ℂ → Prop} (h : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1)
    {x y : Fin n → ℂ} (hx : x ∈ eigSum D P) (hy : y ∈ eigSum D Q) : formB D x y = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem ν y hy => exact eigen_pair D hx hy (h _ _ μ.2 ν.2)
    | zero => exact formB_zero_right D x
    | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
  | zero => exact formB_zero_left D y
  | add a b _ _ ha hb => rw [formB_add_left, ha, hb, add_zero]

theorem iSup_eigen (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) :
    ⨆ μ, (endN D).eigenspace μ = ⊤ := by
  have hss : (endN D).IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree ?_
    rw [← Matrix.charpoly_toLin']
    exact LinearMap.aeval_self_charpoly _
  have h1 := Module.End.iSup_maxGenEigenspace_eq_top (endN D)
  simpa only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1

theorem eigSum_sup (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q : ℂ → Prop}
    (h : ∀ μ, P μ ∨ Q μ) : eigSum D P ⊔ eigSum D Q = ⊤ := by
  rw [eq_top_iff, ← iSup_eigen D hs]
  refine iSup_le fun μ => ?_
  rcases h μ with h | h
  · exact (eigen_le D h).trans le_sup_left
  · exact (eigen_le D h).trans le_sup_right

theorem perpD_eigSum (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q R P' : ℂ → Prop}
    (hPQ : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1) (hQR : ∀ μ, Q μ ∨ R μ) (hPP : ∀ μ, P μ ∨ P' μ)
    (hPR : ∀ μ ν, P' μ → R ν → conj μ * ν ≠ 1) :
    perpD (starRingEnd ℂ) D (eigSum D P) = eigSum D Q := by
  apply le_antisymm
  · intro y hy
    rw [mem_perpD_iff] at hy
    have hy' : y ∈ eigSum D Q ⊔ eigSum D R := by rw [eigSum_sup D hs hQR]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
    have hb0 : b = 0 := by
      refine eq_zero_of_right D b fun x => ?_
      have hx : x ∈ eigSum D P ⊔ eigSum D P' := by rw [eigSum_sup D hs hPP]; trivial
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : formB D p b = 0 := by
        have := hy p hp
        rwa [formB_add_right, eigSum_orth D hPQ hp ha, zero_add] at this
      rw [formB_add_left, h1, eigSum_orth D hPR hq hb, add_zero]
    rw [hb0, add_zero]
    exact ha
  · intro y hy
    rw [mem_perpD_iff]
    exact fun x hx => eigSum_orth D hPQ hx hy

theorem conj_mul_ne {μ ν : ℂ} (h : ‖μ‖ * ‖ν‖ ≠ 1) : conj μ * ν ≠ 1 := by
  intro e
  have := congrArg norm e
  rw [norm_mul, Complex.norm_conj, norm_one] at this
  exact h this

theorem locFlag (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {z : ℂ}
    (hz : (nrmC D).val.charpoly.IsRoot z) (hz1 : ‖z‖ ≠ 1) :
    ∃ W₁ W₂ : Submodule ℂ (Fin n → ℂ), W₁ ≠ ⊥ ∧ W₁ ≤ W₂ ∧ perpD (starRingEnd ℂ) D W₁ = W₂ ∧
      perpD (starRingEnd ℂ) D W₂ = W₁ := by
  have n1 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 1 < a → 1 ≤ b → a * b ≠ 1 := fun {a b} _ _ ha hb => by nlinarith
  have n2 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a < 1 → b ≤ 1 → a * b ≠ 1 := fun {a b} h0 h1 ha hb => by nlinarith
  have p1 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 < ‖μ‖)) = eigSum D (fun μ => 1 ≤ ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ < 1) (P' := fun μ => ‖μ‖ ≤ 1)
      (fun μ ν hμ hν => conj_mul_ne (n1 (norm_nonneg _) (norm_nonneg _) hμ hν))
      (fun μ => le_or_gt 1 ‖μ‖) (fun μ => (lt_or_ge 1 ‖μ‖))
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n2 (norm_nonneg _) (norm_nonneg _) hν hμ))
  have p2 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 ≤ ‖μ‖)) = eigSum D (fun μ => 1 < ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ ≤ 1) (P' := fun μ => ‖μ‖ < 1)
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n1 (norm_nonneg _) (norm_nonneg _) hν hμ))
      (fun μ => lt_or_ge 1 ‖μ‖) (fun μ => le_or_gt 1 ‖μ‖)
      (fun μ ν hμ hν => conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hμ hν))
  refine ⟨_, _, ?_, ?_, p1, p2⟩
  · intro hbot
    have hev : (endN D).HasEigenvalue z := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hz
    obtain ⟨e, hee⟩ := hev.exists_hasEigenvector
    have he := hee.1
    have he0 := hee.2
    rcases lt_or_gt_of_ne hz1 with hlt | hgt
    · refine he0 (eq_zero_of_left D e fun y => ?_)
      have hy : y ∈ ⨆ μ, (endN D).eigenspace μ := by rw [iSup_eigen D hs]; trivial
      induction hy using Submodule.iSup_induction' with
      | mem ν y hy =>
        by_cases hν : 1 < ‖ν‖
        · have : y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hν hy
          rw [(Submodule.mem_bot ℂ).1 this]
          exact formB_zero_right D e
        · exact eigen_pair D he hy (conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hlt (not_lt.1 hν)))
      | zero => exact formB_zero_right D e
      | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
    · have : e ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hgt he
      exact he0 ((Submodule.mem_bot ℂ).1 this)
  · exact iSup_le fun μ => eigen_le D (le_of_lt μ.2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjE_emb (σ : E →+* ℂ) (x : E) : σ (conjE E x) = conj (σ x) :=
  IsCMField.complexEmbedding_complexConj E σ x

theorem nrmC_locGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    (nrmC (locGL v d)).val = (nrm d).val.map v.embedding := by
  have h1 : ((locGL v d)⁻¹ : GL (Fin n) ℂ).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := by
    rw [← map_inv]; rfl
  simp only [nrmC, nrm, Units.val_mul, thetaR_val, Matrix.map_mul]
  rw [h1]
  congr 1
  ext i j
  simp [conjE_emb]

theorem nonEllFlag : PositivityTheory.Rg.BcB.D4.NonEllFlag := by
  intro E _ _ _ n d hreg hell
  have hnot : ∃ (τ : E →+* ℂ) (z : ℂ), ((nrm d).val.charpoly.map τ).IsRoot z ∧ ‖z‖ ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hell ⟨hreg, fun τ z hz => hno τ z hz⟩
  obtain ⟨τ, z, hz, hz1⟩ := hnot
  refine ⟨InfinitePlace.mk τ, ?_⟩
  set v := InfinitePlace.mk τ with hv
  have hcp : (nrmC (locGL v d)).val.charpoly = (nrm d).val.charpoly.map v.embedding := by
    rw [nrmC_locGL, Matrix.charpoly_map]
  have hs : (nrmC (locGL v d)).val.charpoly.Separable := by
    rw [hcp]; exact Polynomial.Separable.map hreg
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact locFlag (locGL v d) hs (z := z) (by rw [hcp, hv, h]; exact hz) hz1
  · refine locFlag (locGL v d) hs (z := conj z) ?_ (by rwa [Complex.norm_conj])
    rw [hcp, hv, h]
    have e : (nrm d).val.charpoly.map (ComplexEmbedding.conjugate τ) =
        ((nrm d).val.charpoly.map τ).map (starRingEnd ℂ) := by
      rw [Polynomial.map_map]; rfl
    rw [e]
    exact Polynomial.IsRoot.map (starRingEnd ℂ) hz

end GlobalTheory.CompanionTheory.NonEll

end
end
