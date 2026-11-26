module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.Step

variable {X : Scheme.{0}} {P : X.Modules}

def lvl (S : ℕ → Subobject P) : ℕ → Subobject P
  | 0 => ⊤
  | e + 1 => S e

lemma lvl_succ_le {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    lvl S (e + 1) ≤ lvl S e := by
  cases e with
  | zero => exact le_top
  | succ e => exact hS e

def incl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S (e + 1) : X.Modules) ⟶ (lvl S e : X.Modules) :=
  Subobject.ofLE _ _ (lvl_succ_le hS e)

@[reassoc (attr := simp)]
lemma incl_arrow {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ (lvl S e).arrow = (lvl S (e + 1)).arrow :=
  Subobject.ofLE_arrow _

def gr {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) : X.Modules :=
  cokernel (incl hS e)

def grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ gr hS e :=
  cokernel.π _

lemma incl_grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ grπ hS e = 0 :=
  cokernel.condition _

def MapsDown (S : ℕ → Subobject P) (r : Γ(X, ⊤)) : Prop :=
  ∀ e, (lvl S (e + 1)).Factors ((lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r)

def mulLvl {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ (lvl S (e + 1) : X.Modules) :=
  (lvl S (e + 1)).factorThru _ (hr e)

@[reassoc (attr := simp)]
lemma mulLvl_arrow {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    mulLvl hr e ≫ (lvl S (e + 1)).arrow = (lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r :=
  Subobject.factorThru_arrow _ _ _

lemma incl_mulLvl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    incl hS e ≫ mulLvl hr e = mulLvl hr (e + 1) ≫ incl hS (e + 1) := by
  rw [← cancel_mono (lvl S (e + 1)).arrow]
  simp only [Category.assoc, mulLvl_arrow, incl_arrow, incl_arrow_assoc]

def grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)} (hr : MapsDown S r)
    (e : ℕ) : gr hS e ⟶ gr hS (e + 1) :=
  cokernel.desc _ (mulLvl hr e ≫ grπ hS (e + 1)) (by
    rw [← Category.assoc, incl_mulLvl, Category.assoc, incl_grπ, comp_zero])

@[reassoc (attr := simp)]
lemma grπ_grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    grπ hS e ≫ grT hS hr e = mulLvl hr e ≫ grπ hS (e + 1) :=
  cokernel.π_desc _ _ _

lemma grT_comm {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r s : Γ(X, ⊤)}
    (hr : MapsDown S r) (hs : MapsDown S s) (e : ℕ) :
    grT hS hr e ≫ grT hS hs (e + 1) = grT hS hs e ≫ grT hS hr (e + 1) := by
  apply coequalizer.hom_ext
  change grπ hS e ≫ _ = grπ hS e ≫ _
  simp only [grπ_grT_assoc, grπ_grT]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (lvl S (e + 2)).arrow]
  simp only [Category.assoc, mulLvl_arrow, mulLvl_arrow_assoc]
  rw [smulHom_comp_smulHom, smulHom_comp_smulHom, mul_comm]

lemma anti {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} [X.Over (Spec (.of A))]
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) : S (e + 1) ≤ S e := by
  rw [hS.succ e]
  exact le_sup_left

lemma twist_smulHom_app (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (F : X.Modules) (r : Γ(X, ⊤))
    (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom F r)).app V s = restrictTop V r • s := by
  ext i
  rw [GlobalTheory.Twist.coord_map_app, GlobalTheory.Twist.coord_smul, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
  congr 1
  exact (restrictTop_restrict (homOfLE inf_le_left) r).symm

def Lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {S : ℕ → Subobject P} (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) :
    Prop :=
  ∀ y : Γ(GlobalTheory.twistZ (gr (anti hS) e) H n, ⊤), ∃ c : Γ(GlobalTheory.twistZ (lvl S e : X.Modules) H n, ⊤),
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) e)).app ⊤ c = y ∧
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (lvl S e).arrow).app ⊤ c ∈ twPow I H n P e

end GlobalTheory.CompanionTheory.GE.Step
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma restrictTop_top_self {X : Scheme.{0}} (r : Γ(X, ⊤)) : restrictTop (⊤ : X.Opens) r = r := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_comp_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {F G K : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ K) (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (φ ≫ ψ)).app V s = (GlobalTheory.Twist.map L ψ).app V ((GlobalTheory.Twist.map L φ).app V s) := by
  rw [GlobalTheory.Twist.map_comp]
  rfl

lemma smul_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (e : ℕ) {a : A} (ha : a ∈ I)
    {m : Γ(GlobalTheory.twistZ P H n, ⊤)} (hm : m ∈ twPow I H n P e) :
    toFunctions (X := X) (A := A) ⊤ a • m ∈ twPow I H n P (e + 1) := by
  have hm' : m ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ e) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm
  change _ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  have hmem : toFunctions (X := X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I :=
    Ideal.mem_map_of_mem _ ha
  rw [pow_succ', Ideal.map_mul, mul_smul]
  exact Submodule.smul_mem_smul hmem hm'

theorem lifts_succ : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  intro A _ _ I X _ H P S hS k g hg hr n e hspan hL y
  have hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) := by
    rw [hspan]; trivial
  have hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m →
      a + b ∈ twPow I H n P m := fun m a b ha hb =>
    Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, y', rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨c', rfl, hc'⟩ := hL y'
    refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩
    · rw [← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]
    · rw [← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app,
        restrictTop_top_self]
      exact smul_mem_twPow I H n P e (hg i) hc'
  | zero =>
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  | add x y _ _ hx hy =>
    obtain ⟨c₁, rfl, h₁⟩ := hx
    obtain ⟨c₂, rfl, h₂⟩ := hy
    refine ⟨c₁ + c₂, map_add _ _ _, ?_⟩
    rw [map_add (f := _)]
    exact hsub _ _ _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, rfl, h⟩ := hx
    refine ⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h

end GlobalTheory.CompanionTheory.GE.Step
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_graded_generation_global_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_succ | exact GlobalTheory.CompanionTheory.GE.Step.lifts_succ | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_succ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDown
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDown
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step.Maps

section Pull

variable {X : Scheme.{0}} {P : X.Modules}

lemma le_pullback_of_factors {Y T : Subobject P} (φ : P ⟶ P) (h : T.Factors (Y.arrow ≫ φ)) :
    Y ≤ (Subobject.pullback φ).obj T := by
  rw [Subobject.pullback_obj]
  exact Subobject.le_mk_of_comm
    (pullback.lift (T.factorThru (Y.arrow ≫ φ) h) Y.arrow (Subobject.factorThru_arrow _ _ _))
    (pullback.lift_snd _ _ _)

lemma factors_of_le_pullback {Y T : Subobject P} (φ : P ⟶ P)
    (h : Y ≤ (Subobject.pullback φ).obj T) : T.Factors (Y.arrow ≫ φ) := by
  rw [Subobject.pullback_obj] at h
  have e : Y.arrow ≫ φ = (Y.ofLE _ h ≫ (Subobject.underlyingIso (pullback.snd T.arrow φ)).hom ≫
      pullback.fst T.arrow φ) ≫ T.arrow := by
    rw [← Subobject.ofLE_arrow h, ← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, pullback.condition]
  rw [e]
  exact Subobject.factors_comp_arrow _

lemma restrictTop_whole (r : Γ(X, ⊤)) : restrictTop (X := X) ⊤ r = r := by
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  simp

end Pull

section Mul

attribute [local instance] algebraOfOver

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
  [X.Over (Spec (.of A))]

lemma exists_smulHom_eq (P : X.Modules) {a : A} (ha : a ∈ I ^ 1) :
    ∃ m : P ⟶ idealPow I P 1, m ≫ idealPowι I P 1 = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
  rw [← span_idealGen (I ^ 1)] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
  have ht : (∑ i, GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c i)) ≫
      biproduct.ι (fun _ : Fin (idealGenNum (I ^ 1)) => P) i) ≫ idealSumMap P (I ^ 1) =
      GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    unfold idealSumMap
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, biproduct.ι_desc, smulHom_comp_smulHom]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← smulHom_sum, ← hc, map_sum]
    simp only [smul_eq_mul, map_mul]
  refine ⟨kernel.lift _ (GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) ?_, ?_⟩
  · rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  · exact kernel.lift_ι _ _ _

lemma factors_powSub (P : X.Modules) (n : ℕ) {a : A} (ha : a ∈ I ^ 1) :
    (powSub I P (n + 1)).Factors ((powSub I P n).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) := by
  show (Subobject.mk (idealPowι I P (n + 1))).Factors _
  rw [Subobject.mk_factors_iff]
  refine ⟨(Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha, ?_⟩
  show ((Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha) ≫
    idealPowι I P (n + 1) = _
  rw [Category.assoc, idealPowMul_ι, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  rfl

theorem mapsDown_toFunctions {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} (_ : P.IsQuasicoherent)
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (a : A) (ha : a ∈ I) :
    MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  have hr : toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
    simp only [GroundTheory.Arith.SchemeCoh.toFunctions, RingHom.comp_apply]
    exact restrictTop_whole _
  rw [hr]
  intro e
  cases e with
  | zero =>
    show (S 0).Factors ((⊤ : Subobject P).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply Subobject.factors_of_le _ (hS.pow_le 0)
    obtain ⟨m, hm⟩ := exists_smulHom_eq I P ha1
    show (Subobject.mk (idealPowι I P 1)).Factors _
    rw [Subobject.mk_factors_iff]
    refine ⟨(⊤ : Subobject P).arrow ≫ m, ?_⟩
    show ((⊤ : Subobject P).arrow ≫ m) ≫ idealPowι I P 1 = _
    rw [Category.assoc, hm]
  | succ e =>
    show (S (e + 1)).Factors ((S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply factors_of_le_pullback
    rw [hS.succ e]
    apply sup_le
    · apply le_pullback_of_factors
      rw [← GroundTheory.Arith.SchemeCoh.smulHom_comp]
      exact Subobject.factors_comp_arrow _
    · apply le_pullback_of_factors
      apply Subobject.factors_of_le _ (hS.pow_le (e + 1))
      exact factors_powSub I P (e + 1) ha1

end Mul

end GlobalTheory.CompanionTheory.GE.Step.Maps
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDownStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_element_maps_closed_system_down : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ a ∈ I, MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | exact GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | (intros; apply GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomology
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem serre_vanishing_coh_one : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  intro A _ _ X _ _ H hH F hF
  letI : Algebra A ↑(X.presheaf.obj (Opposite.op ⊤)) :=
    ((X ↘ Spec (.of A)).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  obtain ⟨hq, hfin⟩ := hF
  haveI : GlobalTheory.QCoh.IsFiniteQC F := GlobalTheory.QCoh.IsFiniteQC.mk hq hfin
  haveI : IsProper ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A) := ‹IsProper (X ↘ Spec (.of A))›
  have hev := GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (fun _ => rfl) F hH
  obtain ⟨n₂, hn⟩ := Filter.eventually_atTop.1 hev
  exact ⟨n₂, fun n hn' => hn n hn' 1 Nat.one_pos⟩

end GlobalTheory.CompanionTheory.GE.Step
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomologyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_first_cohomology : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one | exact GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one | (intros; apply GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGenerators
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGenerators
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

def liftSub {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e)
    (e : ℕ) (V : X.Opens) (W : Submodule Γ(X, V) Γ(gr hS e, V)) : Submodule Γ(X, V) Γ(P, V) where
  carrier := {t | ∃ x : Γ((lvl S e : X.Modules), V),
    (lvl S e).arrow.app V x = t ∧ (grπ hS e).app V x ∈ W}
  add_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, map_add _ _ _, by rw [map_add (f := _)]; exact W.add_mem hx hy⟩
  zero_mem' := ⟨0, map_zero _, by rw [map_zero]; exact W.zero_mem⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl, hx⟩
    exact ⟨c • x, Scheme.Modules.Hom.app_smul _ _ _,
      by rw [Scheme.Modules.Hom.app_smul]; exact W.smul_mem c hx⟩

lemma incl_arrow_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (lvl S e).arrow.app V ((incl hS e).app V y) = (lvl S (e + 1)).arrow.app V y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_arrow]

lemma incl_grπ_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (grπ hS e).app V ((incl hS e).app V y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_grπ]
  rfl

lemma pow_smul_le_secs_lvl {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) (e : ℕ) (U : X.affineOpens) {n : Γ(P, U)}
    (hn : n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U))) : n ∈ secs (lvl S e) (U : X.Opens) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      change IsIso (⊤ : Subobject P).arrow
      infer_instance
    refine ⟨(inv (lvl S 0).arrow).app (U : X.Opens) n, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id]
    simp
  | succ e =>
    have h1 : n ∈ secs (powSub I P (e + 1)) (U : X.Opens) := by
      rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2]
      exact hn
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le e) U h1

theorem span_grT_eq_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) (S : ℕ → Subobject P)
    (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A) (hg : Ideal.span (Set.range g) = I)
    (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  set W := Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) with hW
  have hgen : ∀ i, ∀ n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)),
      toFunctions (A := A) (U : X.Opens) (g i) • n ∈ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    intro i n hn
    obtain ⟨v, hv⟩ := pow_smul_le_secs_lvl I hP (S := S) hS e U hn
    rw [← hv]
    refine ⟨(mulLvl (hr i) e).app (U : X.Opens) v, ?_, ?_⟩
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, mulLvl_arrow,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
      congr 1
      exact restrictTop_restrict (homOfLE le_top) _
    · refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (grπ (anti hS) e).app (U : X.Opens) v, ?_⟩)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, grπ_grT,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hle : (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (e + 1)) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)) ≤ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    rw [pow_succ', Ideal.map_mul, Submodule.mul_smul, Submodule.smul_le]
    intro r hr' n hn
    rw [← hg, Ideal.map_span] at hr'
    induction hr' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := h
      exact hgen i n hn
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb
  haveI : ((lvl S (e + 1 + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh (e + 1)
  haveI : ((lvl S (e + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh e
  have hsur : Function.Surjective ((grπ (anti hS) (e + 1)).app (U : X.Opens)) :=
    surjective_cokernel_π_app (incl (anti hS) (e + 1)) U.2
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hsur s
  have hq : ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    haveI := hP
    (closedSys_pow I P).qcoh e
  have hx : (lvl S (e + 1)).arrow.app (U : X.Opens) x ∈
      secs (S (e + 1) ⊔ powSub I P (e + 1)) (U : X.Opens) := by
    rw [← hS.succ e]
    exact ⟨x, rfl⟩
  rw [(GlobalTheory.T.quasicoherent_sup_sections hP _ _ (hS.qcoh (e + 1)) hq).2 U U.2] at hx
  obtain ⟨_, ⟨y, rfl⟩, t, ht, hxy⟩ := hx
  rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2] at ht
  obtain ⟨x', hx't, hx'W⟩ := hle ht
  have hdec : x = (incl (anti hS) (e + 1)).app (U : X.Opens) y + x' := by
    apply injective_app_of_mono (lvl S (e + 1)).arrow (U : X.Opens)
    rw [map_add (f := _), hx't, hxy]
    exact congrArg (· + t) (incl_arrow_app (anti hS) (e + 1) (U : X.Opens) y).symm
  have hz : ∀ z : Γ((lvl S (e + 1 + 1) : X.Modules), (U : X.Opens)),
      (grπ (anti hS) (e + 1)).app (U : X.Opens)
        ((incl (anti hS) (e + 1)).app (U : X.Opens) z + x') =
      (grπ (anti hS) (e + 1)).app (U : X.Opens) x' := fun z => by
    rw [map_add (f := _), incl_grπ_app, zero_add]
  rw [hdec]
  exact Eq.mpr (congrArg (· ∈ W) (hz y)) hx'W

end GlobalTheory.CompanionTheory.GE.Step
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_pieces_generated_by_ideal_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), Ideal.span (Set.range g) = I → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | exact GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top | (intros; apply GlobalTheory.CompanionTheory.GE.Step.span_grT_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_of_lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB) {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) (hL : Lifts I H hS n (e + 1)) :
    ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  rintro x ⟨c0, rfl⟩
  have hLB : (GlobalTheory.lbZPow H n).IsLB := GlobalTheory.Twist.isLB_lbZPow hH n
  let S0 : ShortComplex X.Modules :=
    ShortComplex.mk (incl (anti hS) (e + 1)) (grπ (anti hS) (e + 1)) (incl_grπ (anti hS) (e + 1))
  have hex0 : S0.Exact := S0.exact_of_g_is_cokernel (cokernelIsCokernel _)
  have hex1 : (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).Exact :=
    (GlobalTheory.Twist.exact_map_iff hLB S0).mpr hex0
  have hmono0 : Mono (incl (anti hS) (e + 1)) := mono_of_mono_fac (incl_arrow (anti hS) (e + 1))
  have hmono1 : Mono (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).f :=
    (GlobalTheory.Twist.mono_map_iff hLB (incl (anti hS) (e + 1))).mpr hmono0
  have hexΓ := GlobalTheory.QCoh.exact_app_of_exact_of_mono hex1 ⊤
  let c1 : Γ(GlobalTheory.twistZ (lvl S (e + 1) : X.Modules) H n, ⊤) := c0
  obtain ⟨c, hc1, hc2⟩ := hL ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ c1)
  have hker : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ (c1 - c) = 0 := by
    rw [map_sub, hc1, sub_self]
  obtain ⟨d, hd⟩ := (hexΓ (c1 - c)).mp hker
  let d1 : Γ(GlobalTheory.twistZ (S (e + 1) : X.Modules) H n, ⊤) := d
  have hd' : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1))).app ⊤ d1 = c1 - c := hd
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1, ⟨d1, rfl⟩, ?_⟩
  have harr0 : incl (anti hS) (e + 1) ≫ (S e).arrow = (S (e + 1)).arrow :=
    incl_arrow (anti hS) (e + 1)
  have harr : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) :=
    (congrArg (fun φ => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) φ).app ⊤ d1) harr0.symm).trans
      ((congrArg (fun f => f.app ⊤ d1)
          (GlobalTheory.Twist.map_comp (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1)) (S e).arrow)).trans
        ((GlobalTheory.QCoh.app_app _ _ ⊤ d1).symm.trans
          (congrArg (fun s => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ s) hd')))
  have hfin : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c := by
    calc _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) := by rw [harr]
      _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c1 -
            (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c) :=
          congrArg (fun t => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 - t)
            (map_sub (ConcreteCategory.hom ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤)) c1 c)
      _ = _ := sub_sub_cancel _ _
  rw [hfin]
  exact hc2

end GlobalTheory.CompanionTheory.GE.Step
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_inductive_successive_approximation : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ), Lifts I H hS n (e + 1) → ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | exact GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_of_lifts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma isCoherent_lvl {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules} (hP : IsCoherent P)
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) :
    IsCoherent (lvl S e : X.Modules) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      exact (Subobject.isIso_arrow_iff_eq_top _).2 rfl
    exact IsCoherent.of_iso (asIso (lvl S 0).arrow).symm hP
  | succ e => exact GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)

theorem isCoherent_gr : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P →
    ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  intro A _ _ I X _ _ P hP S hS e
  have := (isCoherent_lvl hP hS (e + 1)).1
  exact isCoherent_cokernel (incl (anti hS) e) (isCoherent_lvl hP hS e)

end GlobalTheory.CompanionTheory.GE.Step
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_closed_system_coherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | exact GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | (intros; apply GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Step

theorem shortExact_lvl_zero {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) :
    (ShortComplex.mk (incl (anti hS) 0) (grπ (anti hS) 0) (incl_grπ (anti hS) 0)).ShortExact := by
  have : Mono (incl (anti hS) 0) := by
    unfold incl
    infer_instance
  have : Epi (grπ (anti hS) 0) := by
    exact coequalizer.π_epi
  exact { exact := ShortComplex.exact_cokernel (incl (anti hS) 0) }

theorem lifts_zero : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ),
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  intro A _ _ I X _ H hH P S hS n hv y
  have hsurj : Function.Surjective
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) 0)).app ⊤) :=
    GlobalTheory.cohOn.app_surjective
      (GlobalTheory.Twist.shortExact_map (GlobalTheory.Twist.isLB_lbZPow hH n) (shortExact_lvl_zero hS)) ⊤ hv
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨c, hc, ?_⟩
  have htop : Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ 0) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  simp only [twPow, htop, Submodule.top_smul]
  trivial

end GlobalTheory.CompanionTheory.GE.Step
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomologyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_base_of_vanishing_cohomology : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ), Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_zero | exact GlobalTheory.CompanionTheory.GE.Step.lifts_zero | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_uniform : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  intro hG A _ _ I X _ _ H hH P hP S hS
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hPq : P.IsQuasicoherent := hP.1
  have hL : H.IsLB := hH.isLB
  obtain ⟨k, g, hg⟩ := exists_fin_generators I
  have hgI : ∀ i, g i ∈ I := fun i => hg ▸ Ideal.subset_span ⟨i, rfl⟩
  have hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i)) :=
    fun i => GlobalTheory.T.ideal_element_maps_closed_system_down I hPq S hS (g i) (hgI i)
  have hO : OpSeq k (fun e => gr (anti hS) e) (fun i e => grT (anti hS) (hr i) e) 0 :=
    ⟨fun e => GlobalTheory.T.graded_closed_system_coherent I hP S hS e, fun i j e => grT_comm _ _ _ _,
      fun e _ U => GlobalTheory.T.graded_pieces_generated_by_ideal_generators I hPq S hS g hg hr e U⟩
  obtain ⟨n₁, h₁⟩ := @hG A _ _ X _ _ H hH k _ _ 0 hO
  have hS0 : IsCoherent (S 0 : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S 0) (hS.qcoh 0)
  obtain ⟨n₂, h₂⟩ := GlobalTheory.T.serre_vanishing_first_cohomology A H hH hS0
  refine ⟨max n₁ n₂, fun n hn e => ?_⟩
  have hl : ∀ e, Lifts I H hS n e := by
    intro e
    induction e with
    | zero => exact GlobalTheory.T.lifting_base_of_vanishing_cohomology I H hL S hS n (h₂ n (le_of_max_le_right hn))
    | succ e ih => exact GlobalTheory.T.twisted_graded_generation_global_sections I H S hS g hgI hr n e (h₁ n (le_of_max_le_left hn) e (Nat.zero_le _)) ih
  exact GlobalTheory.T.lifting_inductive_successive_approximation I H hL S hS n e (hl (e + 1))

end GlobalTheory.CompanionTheory.GE.Step
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twisted_sections_approximation : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_uniform | exact GlobalTheory.CompanionTheory.GE.Step.step_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_uniform <;> assumption)
end
