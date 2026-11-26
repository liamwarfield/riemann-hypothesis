module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherian
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGenerators
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobject
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainment
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LimitOfFinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Present

def toModPullZPowIso {X Y : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hL : L.IsLB) (f : Y ⟶ X) (m : ℤ) :
    GlobalTheory.LB.toMod ((GlobalTheory.lbZPow L m).pull f) ≅ GlobalTheory.LB.toMod (GlobalTheory.lbZPow (L.pull f) m) :=
  (GlobalTheory.Twist.unitTwistIso _).symm ≪≫ (GlobalTheory.Twist.twistZPullIso f hL _ m).symm ≪≫ GlobalTheory.Twist.unitTwistIso _

theorem exists_coherent_epi_restrict {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (O : X.Opens) (E : (O : Scheme.{0}).Modules) (hE : IsCoherent E) :
    ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  haveI : CompactSpace (O : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  haveI : GlobalTheory.QCoh.IsFiniteQC E := ⟨hE.1, hE.2⟩
  have hA := hH.pull_of_isOpenImmersion O.ι
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := GlobalTheory.Twist.isLB_lbZPow hH.isLB (-n)
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  let P : X.Modules := ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))
  have hP : GlobalTheory.QCoh.IsFiniteQC P := inferInstance
  let e : P.restrict O.ι ≅ ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow (H.pull O.ι) (-n)) :=
    (Scheme.Modules.restrictFunctorIsoPullback O.ι).app P ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback O.ι) _ ≪≫
      Sigma.mapIso (fun _ => GlobalTheory.LB.pullbackIso hL O.ι ≪≫ toModPullZPowIso hH.isLB O.ι (-n))
  exact ⟨P, ⟨hP.1, hP.2⟩, e.hom ≫ φ, epi_comp _ _⟩

end GlobalTheory.CompanionTheory.GE.Present
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_extension_surjection_open : ∀ {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ (O : X.Opens) (E : (O : Scheme.{0}).Modules), IsCoherent E → ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  first | exact @GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | exact GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | (intros; apply GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGenerators
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimit
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

theorem exists_limit_of_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) :=
  _root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf

theorem finite_twisted_sections {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (n : ℤ)
    [Module A Γ(GlobalTheory.twistZ P H n, ⊤)]
    (hs : ∀ (a : A) (x : Γ(GlobalTheory.twistZ P H n, ⊤)), a • x = algebraMap A Γ(X, ⊤) a • x) :
    Module.Finite A Γ(GlobalTheory.twistZ P H n, ⊤) := by
  haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) :=
    GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)
  have h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0) :=
    GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0
  exact Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans
    (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by
      rw [hs, GlobalTheory.restrictGlobal_top]))

theorem exists_limit_twPow : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  intro A _ _ I hI X _ _ H hH P hP n f hf
  letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))
  haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) :=
    ⟨fun a r x => by
      change (a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)
  have hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)),
      y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤)) := by
    intro m y
    have hfun : toFunctions (X := X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by
      ext a
      simp [toFunctions, restrictTop]
    have h := Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤))
      (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤
    rw [Submodule.restrictScalars_top] at h
    rw [← h]
    simp only [twPow, hfun]
    rfl
  obtain ⟨L, hL⟩ := exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)
  exact ⟨L, fun m => (hmem m _).2 (hL m)⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimitStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_cauchy_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_limit_twPow | exact GlobalTheory.CompanionTheory.GE.exists_limit_twPow | (intros; apply GlobalTheory.CompanionTheory.GE.exists_limit_twPow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGenerators
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twSecs_sub_mem {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) {x y : Γ(GlobalTheory.twistZ P H n, ⊤)} (hx : x ∈ twSecs H n S)
    (hy : y ∈ twSecs H n S) : x - y ∈ twSecs H n S := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ a b⟩

theorem twSecs_mono {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    {S T : Subobject P} (h : S ≤ T) : twSecs H n S ⊆ twSecs H n T := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (Subobject.ofLE S T h)).app ⊤ a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp,
    Subobject.ofLE_arrow]

theorem zero_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : (0 : Γ(GlobalTheory.twistZ P H n, ⊤)) ∈ twPow I H n P m :=
  Submodule.zero_mem _

end GlobalTheory.CompanionTheory.GE.TwLim

namespace GlobalTheory.CompanionTheory.GE.TwLim

theorem twPow_sub_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := GlobalTheory.T.twisted_ideal_power_le_sections

theorem twPow_complete : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := GlobalTheory.T.twisted_sections_cauchy_limit

theorem antitone_closedSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P} (hS : ClosedSys I P S) :
    Antitone S :=
  antitone_nat_of_succ_le fun m => (hS.succ m).symm ▸ le_sup_left

theorem exists_compat_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  intro A _ _ I hI X _ _ H hH P hP S hS n hstep
  refine ⟨⋂ e, twSecs H n (S e), fun e => Set.iInter_subset _ e, ?_⟩
  intro e x hx
  have hpow : ∀ m, twPow I H n P (m + 1) ⊆ twSecs H n (S m) := fun m =>
    (twPow_sub_twSecs I H hH hP n (m + 1)).trans (twSecs_mono H n (hS.pow_le m))
  let seq : ∀ k : ℕ, {y // y ∈ twSecs H n (S (e + k))} := fun k =>
    Nat.rec ⟨x, hx⟩ (fun k y => ⟨(hstep (e + k) y.1 y.2).choose, (hstep (e + k) y.1 y.2).choose_spec.1⟩) k
  have hseq : ∀ k, (seq k).1 - (seq (k + 1)).1 ∈ twPow I H n P (e + k + 1) := fun k =>
    (hstep (e + k) (seq k).1 (seq k).2).choose_spec.2
  have hcg : ∀ a b : ℕ, a = b → (seq a).1 = (seq b).1 := by rintro _ _ rfl; rfl
  have hs0 : (seq 0).1 = x := rfl
  let f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤) := fun j => (seq (j - (e + 1))).1
  have hf : ∀ j, f j - f (j + 1) ∈ twPow I H n P j := by
    intro j
    by_cases hj : j < e + 1
    · have h1 : f j = f (j + 1) := hcg _ _ (by omega)
      rw [h1, sub_self]
      exact zero_mem_twPow I H n P j
    · obtain ⟨k, rfl⟩ : ∃ k, j = e + 1 + k := ⟨j - (e + 1), by omega⟩
      have h1 : f (e + 1 + k) = (seq k).1 := hcg _ _ (by omega)
      have h2 : f (e + 1 + k + 1) = (seq (k + 1)).1 := hcg _ _ (by omega)
      rw [h1, h2]
      have := hseq k
      rwa [show e + k + 1 = e + 1 + k by omega] at this
  obtain ⟨L, hL⟩ := twPow_complete I hI H hH hP n f hf
  have hk : ∀ k, L ∈ twSecs H n (S (e + k)) := by
    intro k
    have h1 : f (e + k + 1) = (seq k).1 := hcg _ _ (by omega)
    have hd : (seq k).1 - L ∈ twSecs H n (S (e + k)) := h1 ▸ hpow (e + k) (hL (e + k + 1))
    have := twSecs_sub_mem H n _ (seq k).2 hd
    rwa [sub_sub_cancel] at this
  refine ⟨L, Set.mem_iInter.2 fun m => ?_, ?_⟩
  · rcases le_or_gt e m with hm | hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hk k
    · exact twSecs_mono H n (antitone_closedSys I hS hm.le) (by simpa using hk 0)
  · have h1 : f (e + 1) = x := (hcg (e + 1 - (e + 1)) 0 (by omega)).trans hs0
    simpa [h1] using hL (e + 1)

end GlobalTheory.CompanionTheory.GE.TwLim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_finite_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | exact GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | (intros; apply GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Extend

section Defs

variable {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}

def extMap (f : P.restrict O.ι ⟶ E) (S : Subobject E) :
    P ⟶ (Scheme.Modules.pushforward O.ι).obj (cokernel S.arrow) :=
  (Scheme.Modules.restrictAdjunction O.ι).homEquiv P _ (f ≫ cokernel.π S.arrow)

def extSub (f : P.restrict O.ι ⟶ E) (S : Subobject E) : Subobject P :=
  kernelSubobject (extMap O f S)

lemma extMap_app (f : P.restrict O.ι ⟶ E) (S : Subobject E) (V : X.Opens) (x : Γ(P, V)) :
    (extMap O f S).app V x = (f ≫ cokernel.π S.arrow).app (O.ι ⁻¹ᵁ V)
      ((P.restrictAppIso O.ι _).inv (P.presheaf.map (homOfLE (O.ι.image_preimage_le V)).op x)) := by
  rfl

lemma mem_secs_extSub (f : P.restrict O.ι ⟶ E) (S : Subobject E) (V : X.Opens) (x : Γ(P, V)) :
    x ∈ secs (extSub O f S) V ↔ (extMap O f S).app V x = 0 := by
  constructor
  · rintro ⟨k, rfl⟩
    change ((kernelSubobject (extMap O f S)).arrow.app V ≫ (extMap O f S).app V) k = 0
    rw [← Scheme.Modules.Hom.comp_app, kernelSubobject_arrow_comp, Scheme.Modules.Hom.zero_app]
    rfl
  · intro hx
    obtain ⟨k, hk⟩ := kernel_ι_app_exact (extMap O f S) V x hx
    refine ⟨(kernelSubobjectIso (extMap O f S)).inv.app V k, ?_⟩
    rw [← hk, ← kernelSubobject_arrow' (extMap O f S)]
    rfl

end Defs

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

lemma isNoetherian_of_proper {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] : IsNoetherian X := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  first | infer_instance | exact {}

lemma isClosed_image {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ T : (O : Scheme.{0}).IdealSheafData,
      IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) →
      IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro T hT
  have e : T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A)) =
      (T.subschemeι ≫ O.ι) ≫ (X ↘ Spec (.of A)) := by
    rw [Category.assoc]; rfl
  haveI : UniversallyClosed ((T.subschemeι ≫ O.ι) ≫ (X ↘ Spec (.of A))) := by
    rw [← e]; infer_instance
  haveI : UniversallyClosed (T.subschemeι ≫ O.ι) :=
    UniversallyClosed.of_comp_of_isSeparated _ (X ↘ Spec (.of A))
  have hc : IsClosed (Set.range (T.subschemeι ≫ O.ι)) :=
    (T.subschemeι ≫ O.ι).isClosedMap.isClosed_range
  have hr : Set.range (T.subschemeι ≫ O.ι) = O.ι '' (T.support : Set (O : Scheme.{0})) := by
    rw [← T.range_subschemeι, ← Set.range_comp]
    rfl
  rwa [hr] at hc

lemma map_injective_of_le_of_le {Y : Scheme.{0}} (M : Y.Modules) {U U' : Y.Opens} (h : U ≤ U')
    (h' : U' ≤ U) : Function.Injective (M.presheaf.map (homOfLE h).op) := by
  intro a b hab
  have e : ∀ z, M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op z) = z := by
    intro z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rw [show (homOfLE h).op ≫ (homOfLE h').op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
    rfl
  rw [← e a, hab, e b]

variable {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}

lemma extMap_app_image (f : P.restrict O.ι ⟶ E) (S : Subobject E) (W : (O : Scheme.{0}).Opens)
    (x : Γ(P, O.ι ''ᵁ W)) :
    (extMap O f S).app (O.ι ''ᵁ W) x = 0 ↔
      (cokernel.π S.arrow).app W (f.app W ((P.restrictAppIso O.ι W).inv x)) = 0 := by
  have h1 : W ≤ O.ι ⁻¹ᵁ (O.ι ''ᵁ W) := (O.ι.preimage_image_eq W).ge
  have h2 : O.ι ⁻¹ᵁ (O.ι ''ᵁ W) ≤ W := (O.ι.preimage_image_eq W).le
  set y := (P.restrictAppIso O.ι _).inv
    (P.presheaf.map (homOfLE (O.ι.image_preimage_le (O.ι ''ᵁ W))).op x) with hy
  have hres : (P.restrict O.ι).presheaf.map (homOfLE h1).op y = (P.restrictAppIso O.ι W).inv x := by
    rw [hy, Scheme.Modules.restrictAppIso_inv_map_apply]
    change P.presheaf.map _ (P.presheaf.map _ x) = x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hid : ∀ g : Opposite.op (O.ι ''ᵁ W) ⟶ Opposite.op (O.ι ''ᵁ W), P.presheaf.map g x = x := by
      intro g
      rw [show g = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
      rfl
    exact hid _
  have key : (cokernel S.arrow).presheaf.map (homOfLE h1).op
      ((f ≫ cokernel.π S.arrow).app (O.ι ⁻¹ᵁ (O.ι ''ᵁ W)) y) =
      (cokernel.π S.arrow).app W (f.app W ((P.restrictAppIso O.ι W).inv x)) := by
    have nat := ConcreteCategory.congr_hom
      ((f ≫ cokernel.π S.arrow).mapPresheaf.naturality (homOfLE h1).op) y
    refine nat.symm.trans ?_
    change (f ≫ cokernel.π S.arrow).app W ((P.restrict O.ι).presheaf.map (homOfLE h1).op y) = _
    rw [hres, Scheme.Modules.Hom.comp_app]
    rfl
  rw [extMap_app, ← key]
  constructor
  · intro h
    rw [h]
    exact AddMonoidHom.map_zero _
  · intro h
    exact map_injective_of_le_of_le _ h1 h2 (h.trans (map_zero _).symm)

lemma extMap_app_eq_zero_of_disjoint (f : P.restrict O.ι ⟶ E) (S : Subobject E)
    {T : Set (O : Scheme.{0})} (hT : Scheme.Modules.SupportedIn (cokernel S.arrow) T) (V : X.Opens)
    (hV : Disjoint (V : Set X) (O.ι '' T)) (x : Γ(P, V)) : (extMap O f S).app V x = 0 := by
  rw [extMap_app]
  refine hT _ ?_ _
  rw [Set.disjoint_left]
  intro y hy hyT
  exact Set.disjoint_left.1 hV hy ⟨y, hyT, rfl⟩

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

lemma qc_extSub {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} [P.IsQuasicoherent] (hE : IsCoherent E)
    (f : P.restrict O.ι ⟶ E) (S : Subobject E) (hS : (S : (O : Scheme.{0}).Modules).IsQuasicoherent) :
    ((extSub O f S : Subobject P) : X.Modules).IsQuasicoherent := by
  haveI := hS
  haveI : IsNoetherian X := isNoetherian_of_proper (A := A)
  haveI := (isCoherent_cokernel S.arrow hE).1
  haveI := isQuasicoherent_pushforward_of_qcqs O.ι (cokernel S.arrow)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubobjectIso (extMap O f S)).symm (isQuasicoherent_kernel _)

lemma exists_powSub_lift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent →
      ∀ (f : P.restrict O.ι ⟶ E), Epi f → ∀ (n : ℕ) (W : (O : Scheme.{0}).Opens), IsAffineOpen W →
      ∀ y : Γ(E, W), y ∈ secs (powSub I E n) W →
        ∃ t ∈ secs (powSub I P n) (O.ι ''ᵁ W), f.app W ((P.restrictAppIso O.ι W).inv t) = y := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf n W hW y hy
  haveI := hP
  haveI := hE
  haveI := hf
  haveI : (P.restrict O.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  rw [secs_powSub I E hE n W hW] at hy
  simp only [secs_powSub I P hP n _ hW']
  have hmul : ∀ (a : Γ(X, O.ι ''ᵁ W)) (m : Γ(P, O.ι ''ᵁ W)),
      f.app W ((P.restrictAppIso O.ι W).inv (a • m)) =
        (O.ι.appIso W).hom a • f.app W ((P.restrictAppIso O.ι W).inv m) := by
    intro a m
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
  let JP : Submodule Γ(X, O.ι ''ᵁ W) Γ(P, O.ι ''ᵁ W) :=
    Ideal.map (toFunctions (A := A) (O.ι ''ᵁ W)) (I ^ n) • ⊤
  let N : Submodule Γ((O : Scheme.{0}), W) Γ(E, W) :=
    { carrier := {y | ∃ t ∈ JP, f.app W ((P.restrictAppIso O.ι W).inv t) = y}
      add_mem' := by
        rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
        exact ⟨t + t', JP.add_mem ht ht', by rw [map_add (f := _), map_add (f := _)]⟩
      zero_mem' := ⟨0, JP.zero_mem, by rw [map_zero, map_zero]⟩
      smul_mem' := by
        rintro r _ ⟨t, ht, rfl⟩
        refine ⟨(O.ι.appIso W).inv r • t, JP.smul_mem _ ht, ?_⟩
        rw [hmul]
        congr 1
        rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
        rfl }
  have hJ : Ideal.map (toFunctions (A := A) W) (I ^ n) =
      Ideal.map (O.ι.appIso W).hom.hom (Ideal.map (toFunctions (A := A) (O.ι ''ᵁ W)) (I ^ n)) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    exact (ImageOpen.toFunctions_open O W r).symm
  have hsurj : Function.Surjective (O.ι.appIso W).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (O.ι.appIso W).hom).2
  have hle : (Ideal.map (toFunctions (A := A) W) (I ^ n) • ⊤ : Submodule Γ((O : Scheme.{0}), W) Γ(E, W))
      ≤ N := by
    refine Submodule.smul_le.2 fun a ha m _ => ?_
    rw [hJ] at ha
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 ha
    obtain ⟨z, rfl⟩ := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen f hW m
    obtain ⟨z', rfl⟩ : ∃ z', (P.restrictAppIso O.ι W).inv z' = z := ⟨z, rfl⟩
    exact ⟨b • z', Submodule.smul_mem_smul hb Submodule.mem_top, hmul b z'⟩
  exact hle hy

lemma le_of_cover {X : Scheme.{0}} (O : X.Opens) {Z : Set X} (hZ : IsClosed Z)
    (hZO : Z ⊆ (O : Set X)) {P : X.Modules} [P.IsQuasicoherent] (S S' : Subobject P)
    (hS : (S : X.Modules).IsQuasicoherent) (hS' : (S' : X.Modules).IsQuasicoherent)
    (h1 : ∀ W : (O : Scheme.{0}).Opens, IsAffineOpen W → secs S (O.ι ''ᵁ W) ⊆ secs S' (O.ι ''ᵁ W))
    (h2 : ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) Z → secs S U ⊆ secs S' U) :
    S ≤ S' := by
  let V : (O : Scheme.{0}).affineOpens ⊕ {U : X.affineOpens // Disjoint ((U : X.Opens) : Set X) Z} →
      X.Opens := Sum.elim (fun W => O.ι ''ᵁ (W : (O : Scheme.{0}).Opens)) (fun U => (U.1 : X.Opens))
  refine le_of_secs_subset_cover S S' hS hS' V ?_ ?_ ?_
  · rintro (W | U)
    · exact W.2.image_of_isOpenImmersion O.ι
    · exact U.1.2
  · rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ (O : Set X)
    · rw [← Scheme.Opens.range_ι] at hx
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
        (O : Scheme.{0}).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl ⟨W, hW⟩, ⟨y, hyW, rfl⟩⟩
    · have hxZ : x ∈ Zᶜ := fun h => hx (hZO h)
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUZ⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxZ hZ.isOpen_compl
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨Sum.inr ⟨⟨U, hU⟩, Set.subset_compl_iff_disjoint_right.1 hUZ⟩, hxU⟩
  · rintro (W | U)
    · exact h1 W.1 W.2
    · exact h2 U.1.1 U.1.2 U.2

end GlobalTheory.CompanionTheory.GE.Extend

namespace GlobalTheory.CompanionTheory.GE.Extend

theorem extend : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ T : (O : Scheme.{0}).IdealSheafData, IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) → Scheme.Modules.SupportedIn (cokernel (S 0).arrow) (T.support : Set (O : Scheme.{0})) → IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) ∧ ∃ Sb : ℕ → Subobject P, ClosedSys I P Sb ∧ (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) ∧ ∀ e (V : X.Opens), Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs (Sb e) V = Set.univ := by
  intro A _ _ I X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf S hS T hT hsupp
  haveI := hP.1
  haveI := hE.1
  have hZ := isClosed_image (A := A) O T hT
  set Z : Set X := O.ι '' (T.support : Set (O : Scheme.{0})) with hZdef
  have hZO : Z ⊆ (O : Set X) := by
    rintro _ ⟨y, -, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩

  have hsuppe : ∀ e, Scheme.Modules.SupportedIn (cokernel (S e).arrow) (T.support : Set (O : Scheme.{0})) :=
    fun e => Comb.supportedIn_of_secs_eq_univ hE.1 (hS.qcoh e) fun U hU hd =>
      Comb.secs_sys_univ hS hE.1 hU (Comb.secs_eq_univ_of_supportedIn hE.1 (hS.qcoh 0) hsupp hU hd) e
  let Sb : ℕ → Subobject P := fun e => extSub O f (S e)
  have hq : ∀ e, ((Sb e : Subobject P) : X.Modules).IsQuasicoherent :=
    fun e => qc_extSub (A := A) O hE f (S e) (hS.qcoh e)
  have hchar : ∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W),
      x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W := by
    intro e W hW x
    haveI := hS.qcoh e
    rw [mem_secs_extSub, extMap_app_image]
    exact (mem_range_app_iff (S e).arrow hW _).symm
  have huniv : ∀ e (V : X.Opens), Disjoint (V : Set X) Z → secs (Sb e) V = Set.univ := by
    intro e V hV
    refine Set.eq_univ_of_forall fun x => ?_
    rw [mem_secs_extSub]
    exact extMap_app_eq_zero_of_disjoint O f (S e) (hsuppe e) V hV x
  have hpowq : ∀ e, ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    fun e => (closedSys_pow I P).qcoh e
  have hpow : ∀ e, powSub I P (e + 1) ≤ Sb e := by
    intro e
    refine le_of_cover O hZ hZO _ _ (hpowq e) (hq e) (fun W hW x hx => ?_)
      (fun U _ hU x _ => by rw [huniv e U hU]; trivial)
    rw [hchar e W hW]
    exact Comb.secs_mono (hS.pow_le e) W (ImageOpen.map_mem_secs_powSub I O hP.1 hE.1 f (e + 1) W hW x hx)
  have hsup : ∀ e, (((Sb (e + 1) ⊔ powSub I P (e + 1)) : Subobject P) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V → secs (Sb (e + 1) ⊔ powSub I P (e + 1)) V =
        {x | ∃ s ∈ secs (Sb (e + 1)) V, ∃ t ∈ secs (powSub I P (e + 1)) V, x = s + t} :=
    fun e => supsecs hP.1 _ _ (hq (e + 1)) (hpowq e)
  refine ⟨hZ, Sb, ⟨hq, hpow, fun e => le_antisymm ?_ ?_⟩, hchar, huniv⟩
  · refine le_of_cover O hZ hZO _ _ (hq e) (hsup e).1 (fun W hW x hx => ?_) (fun U hU hd x _ => ?_)
    · have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
      rw [hchar e W hW, hS.succ e,
        (supsecs hE.1 _ _ (hS.qcoh (e + 1)) ((closedSys_pow I E).qcoh e)).2 W hW] at hx
      obtain ⟨s, hs, t, ht, hst⟩ := hx
      obtain ⟨t', ht', hft'⟩ := exists_powSub_lift I O hP.1 hE.1 f hf (e + 1) W hW t ht
      rw [(hsup e).2 _ hW']
      refine ⟨x - t', ?_, t', ht', by abel⟩
      rw [hchar (e + 1) W hW, map_sub, map_sub, hft', hst, add_sub_cancel_right]
      exact hs
    · rw [(hsup e).2 U hU]
      refine ⟨x, by rw [huniv (e + 1) U hd]; trivial, 0, ⟨0, map_zero _⟩, (add_zero x).symm⟩
  · refine sup_le ?_ (hpow e)
    refine le_of_cover O hZ hZO _ _ (hq (e + 1)) (hq e) (fun W hW x hx => ?_)
      (fun U _ hU x _ => by rw [huniv e U hU]; trivial)
    rw [hchar e W hW]
    rw [hchar (e + 1) W hW] at hx
    exact Comb.secs_mono ((hS.succ e).symm ▸ le_sup_left) W hx

end GlobalTheory.CompanionTheory.GE.Extend
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_restriction_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ T : (O : Scheme.{0}).IdealSheafData, IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) → Scheme.Modules.SupportedIn (cokernel (S 0).arrow) (T.support : Set (O : Scheme.{0})) → IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) ∧ ∃ Sb : ℕ → Subobject P, ClosedSys I P Sb ∧ (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) ∧ ∀ e (V : X.Opens), Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs (Sb e) V = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Extend.extend | exact GlobalTheory.CompanionTheory.GE.Extend.extend | (intros; apply GlobalTheory.CompanionTheory.GE.Extend.extend <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherian
set_option autoImplicit false

noncomputable section

open DirectSum

namespace GlobalTheory.CompanionTheory.GE.GNoeth

variable {R : Type} [CommRing R] {M : ℕ → Type} [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)]

def shiftOp (T : ∀ e, M e →ₗ[R] M (e + 1)) : Module.End R (⨁ e, M e) :=
  DirectSum.toModule R ℕ _ (fun e => DirectSum.lof R ℕ M (e + 1) ∘ₗ T e)

theorem shiftOp_lof (T : ∀ e, M e →ₗ[R] M (e + 1)) (e : ℕ) (x : M e) :
    shiftOp T (DirectSum.lof R ℕ M e x) = DirectSum.lof R ℕ M (e + 1) (T e x) := by
  simp only [shiftOp, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem shiftOp_succ (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) (e : ℕ) :
    shiftOp T y (e + 1) = T e (y e) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    by_cases h : i = e
    · subst h; simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (by omega), map_zero]
  | add a b ha hb => simp only [map_add (f := _), DirectSum.add_apply, ha, hb]

theorem shiftOp_zero (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) :
    shiftOp T y 0 = 0 := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  | add a b ha hb => simp only [map_add (f := _), DirectSum.add_apply, ha, hb, add_zero]

theorem eventually_zero (f : ⨁ e, M e) : ∃ n : ℕ, ∀ e, n ≤ e → f e = 0 := by
  induction f using DirectSum.induction_on with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | of i x =>
    refine ⟨i + 1, fun e he => DirectSum.of_eq_of_ne _ _ _ (by omega)⟩
  | add a b ha hb =>
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    exact ⟨max n m, fun e he => by
      rw [DirectSum.add_apply, hn e (le_of_max_le_left he), hm e (le_of_max_le_right he), add_zero]⟩

theorem lof_mem {L : ∀ e, Submodule R (M e)} (i : ℕ) {x : M i} (hx : x ∈ L i) (j : ℕ) :
    DirectSum.lof R ℕ M i x j ∈ L j := by
  rw [DirectSum.lof_eq_of]
  by_cases h : i = j
  · subst h; simpa [DirectSum.of_eq_same] using hx
  · rw [DirectSum.of_eq_of_ne _ _ _ (by omega)]; exact zero_mem _

theorem gradedNoeth : GradedNoeth := by
  classical
  intro R _ _ k M _ _ _ T hT d hgen L hL
  have hEc : ∀ i j, shiftOp (T i) * shiftOp (T j) = shiftOp (T j) * shiftOp (T i) := by
    intro i j
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Module.End.mul_apply, shiftOp_lof]
    rw [hT i j e x]
  let Sset : Finset (Module.End R (⨁ e, M e)) := Finset.univ.image (fun i => shiftOp (T i))
  have hSset : ∀ a, a ∈ (Sset : Set (Module.End R (⨁ e, M e))) → ∃ i, shiftOp (T i) = a := by
    intro a ha
    simpa [Sset] using ha
  have hcomm : ∀ a ∈ (Sset : Set (Module.End R (⨁ e, M e))),
      ∀ b ∈ (Sset : Set (Module.End R (⨁ e, M e))), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hSset a ha
    obtain ⟨j, rfl⟩ := hSset b hb
    exact hEc i j
  let S := Algebra.adjoin R (Sset : Set (Module.End R (⨁ e, M e)))
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    intro a ha b hb _
    exact hcomm a ha b hb)
  letI : CommRing S := { (inferInstance : Ring S) with mul_comm := mul_comm' }
  haveI : Algebra.FiniteType R S :=
    (Subalgebra.fg_iff_finiteType S).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hEmem : ∀ i, shiftOp (T i) ∈ S := fun i => Algebra.subset_adjoin (by simp [Sset])
  have hfin : ∀ e, ∃ g : Finset (M e), Submodule.span R (g : Set (M e)) = ⊤ := fun e =>
    Module.Finite.fg_top (R := R) (M := M e)
  choose gens hgens using hfin
  let G0 : Set (⨁ e, M e) :=
    ⋃ e ∈ Finset.range (d + 1), DirectSum.lof R ℕ M e '' (gens e : Set (M e))
  have hG0 : G0.Finite :=
    (Finset.finite_toSet _).biUnion fun e _ => (Finset.finite_toSet _).image _
  let P : Submodule S (⨁ e, M e) := Submodule.span S G0
  have hbase : ∀ e, e ≤ d → ∀ m : M e, DirectSum.lof R ℕ M e m ∈ P := by
    intro e he m
    have hm : m ∈ Submodule.span R (gens e : Set (M e)) := by rw [hgens e]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem P c hx
  have hall : ∀ e (m : M e), DirectSum.lof R ℕ M e m ∈ P := by
    intro e
    induction e with
    | zero => exact hbase 0 (Nat.zero_le _)
    | succ e ih =>
      by_cases he : e + 1 ≤ d
      · exact hbase _ he
      · intro m
        have hm : m ∈ ⨆ i, LinearMap.range (T i e) := by rw [hgen e (by omega)]; trivial
        refine Submodule.iSup_induction _ (motive := fun m => DirectSum.lof R ℕ M (e + 1) m ∈ P)
          hm ?_ ?_ ?_
        · intro i x hx
          obtain ⟨y, rfl⟩ := hx
          have h1 : DirectSum.lof R ℕ M (e + 1) (T i e y) =
              (⟨shiftOp (T i), hEmem i⟩ : S) • DirectSum.lof R ℕ M e y :=
            (shiftOp_lof (T i) e y).symm
          rw [h1]
          exact P.smul_mem _ (ih y)
        · simp
        · intro x y hx hy
          rw [map_add (f := _)]
          exact P.add_mem hx hy
  have hP : ∀ y : ⨁ e, M e, y ∈ P := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => exact P.zero_mem
    | of i x => rw [← DirectSum.lof_eq_of R]; exact hall i x
    | add a b ha hb => exact P.add_mem ha hb
  have htop : P = ⊤ := eq_top_iff.2 fun y _ => hP y
  haveI : Module.Finite S (⨁ e, M e) := ⟨Submodule.fg_def.2 ⟨G0, hG0, htop⟩⟩
  have hstab : ∀ x ∈ S, ∀ y : ⨁ e, M e, (∀ e, y e ∈ L e) → ∀ e, x y e ∈ L e := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      intro y hy e
      cases e with
      | zero => rw [shiftOp_zero]; exact zero_mem _
      | succ e => rw [shiftOp_succ]; exact hL i e (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      intro y hy e
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply]
      exact (L e).smul_mem r (hy e)
    | add x x' _ _ hx hx' =>
      intro y hy e
      rw [LinearMap.add_apply, DirectSum.add_apply]
      exact (L e).add_mem (hx y hy e) (hx' y hy e)
    | mul x x' _ _ hx hx' =>
      intro y hy e
      rw [Module.End.mul_apply]
      exact hx _ (hx' y hy) e
  let N : Submodule S (⨁ e, M e) :=
    { carrier := {y | ∀ e, y e ∈ L e}
      add_mem' := fun {a b} ha hb e => by
        rw [DirectSum.add_apply]; exact (L e).add_mem (ha e) (hb e)
      zero_mem' := fun e => by rw [DirectSum.zero_apply]; exact zero_mem _
      smul_mem' := fun s y hy => hstab s.1 s.2 y hy }
  have hQ : ∀ e, ∀ x ∈ S, ∃ c : R, ∀ y : ⨁ e, M e, (∀ e', y e' ∈ L e') →
      x y (e + 1) - c • y (e + 1) ∈ ⨆ i, (L e).map (T i e) := by
    intro e x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      refine ⟨0, fun y hy => ?_⟩
      rw [zero_smul, sub_zero, shiftOp_succ]
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      refine ⟨r, fun y hy => ?_⟩
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply, sub_self]
      exact zero_mem _
    | add x x' _ _ hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c + c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc y hy) (hc' y hy)
      convert h2 using 1
      rw [LinearMap.add_apply, DirectSum.add_apply, add_smul]
      abel
    | mul x x' _ hx'S hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c * c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc _ (hstab x' hx'S y hy)) (Submodule.smul_mem _ c (hc' y hy))
      convert h2 using 1
      rw [Module.End.mul_apply, smul_sub, mul_smul]
      abel
  obtain ⟨F, hF⟩ := IsNoetherian.noetherian N
  choose nf hnf using (eventually_zero : ∀ f : ⨁ e, M e, ∃ n : ℕ, ∀ e, n ≤ e → f e = 0)
  refine ⟨F.sup nf, fun e he => le_antisymm (iSup_le fun i => hL i e) ?_⟩
  intro x hx
  let Ne : Submodule S (⨁ e, M e) :=
    { carrier := {y | y ∈ N ∧ y (e + 1) ∈ ⨆ i, (L e).map (T i e)}
      add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
        rw [DirectSum.add_apply]; exact Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨N.zero_mem, by rw [DirectSum.zero_apply]; exact zero_mem _⟩
      smul_mem' := fun s y hy => by
        obtain ⟨c, hc⟩ := hQ e s.1 s.2
        refine ⟨N.smul_mem s hy.1, ?_⟩
        have h3 := Submodule.add_mem _ (hc y hy.1) (Submodule.smul_mem _ c hy.2)
        rw [sub_add_cancel] at h3
        exact h3 }
  have hNle : N ≤ Ne := by
    rw [← hF, Submodule.span_le]
    intro f hf
    refine ⟨by rw [← hF]; exact Submodule.subset_span hf, ?_⟩
    have h4 : nf f ≤ F.sup nf := Finset.le_sup hf
    rw [hnf f (e + 1) (by omega)]
    exact zero_mem _
  have hxN : DirectSum.lof R ℕ M (e + 1) x ∈ N := fun j => lof_mem (e + 1) hx j
  have h5 := (hNle hxN).2
  rwa [DirectSum.lof_eq_of, DirectSum.of_eq_same] at h5

end GlobalTheory.CompanionTheory.GE.GNoeth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_noetherian : GradedNoeth := by
  first | exact @GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | exact GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem exists_sub_of_ample {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (S : ℕ → Subobject P) (hS : ClosedSys I P S) :
    ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hV : UniformVanishing := @GlobalTheory.T.uniform_vanishing_of_graded_noetherian GlobalTheory.T.graded_noetherian
  have hG : UniformGen := @GlobalTheory.T.uniform_generation_of_vanishing GlobalTheory.T.graded_noetherian (@hV)
  obtain ⟨n₁, h₁⟩ := GlobalTheory.T.ample_twisted_sections_approximation (@hG) I H hH hP S hS
  have hW : ∀ n : ℤ, ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧
      (n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1)) := fun n => by
    by_cases hn : n₁ ≤ n
    · obtain ⟨W, a, b⟩ := GlobalTheory.T.twisted_sections_finite_generators I hI H hH hP S hS n (h₁ n hn)
      exact ⟨W, a, fun _ => b⟩
    · exact ⟨∅, fun _ => Set.empty_subset _, fun h => absurd h hn⟩
  choose W a b using hW
  exact GlobalTheory.T.twisted_sections_uniform_generators I H hH hP S hS n₁ W a b

theorem statement_open_projective : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  intro A _ _ I hI N Y i hi O
  letI : Y.Over (Spec (.of A)) := ⟨i ≫ ProjSpace.toSpecBase A N⟩
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (Y ↘ Spec (.of A))⟩
  have hpr : IsProper (ProjSpace.toSpecBase A N) := by
    open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjSpace in exact isProper_str A N
  have hp : IsProper (Y ↘ Spec (.of A)) := (inferInstance : IsProper (i ≫ ProjSpace.toSpecBase A N))
  have hln : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of A))
  have hcs : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of A))
  have hno : IsNoetherian Y := ⟨⟩
  have hH : GlobalTheory.IsAmpleLB ((GlobalTheory.ProjSpace.O1 A N).pull i) := (GlobalTheory.isAmple_projective_O_one A N).pull_of_isAffineHom i
  intro E hE S hS _ hP
  obtain ⟨P, hPc, f, hf⟩ := GlobalTheory.T.coherent_extension_surjection_open _ hH O E hE
  obtain ⟨T, hT, hTs⟩ := hP
  obtain ⟨hcl, Sb, hSb, hb, hc⟩ := GlobalTheory.T.closed_system_restriction_open I O hPc hE f hf S hS T hT hTs
  obtain ⟨Bb, hBq, hBb⟩ := exists_sub_of_ample I hI _ hH hPc Sb hSb
  obtain ⟨B, hBq', hB, hBs⟩ := GlobalTheory.T.closed_system_restriction_subobject I O hPc hE f hf S hS Sb hb Bb hBq hBb
  exact ⟨B, hBq', GlobalTheory.T.closed_system_open_ideal_containment I hI O hPc hE f hf (Sb 0) T hcl (hc 0) Bb hBq (hBb 0) B hBs, hB⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_projective_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.statement_open_projective | exact GlobalTheory.CompanionTheory.GE.statement_open_projective | (intros; apply GlobalTheory.CompanionTheory.GE.statement_open_projective <;> assumption)
end
