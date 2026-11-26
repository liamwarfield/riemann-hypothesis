module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegVanishing
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefPullbackIsNef
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem isNef_pull_of_isProjOver : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  intro k _ X Y p s hp N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (s ≫ p)
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨pull_isLB hN.isLB s, fun C hC => ?_⟩
  rcases interNumRed_pull_curve p s C hC with h | ⟨C', hC', d, hd⟩
  · rw [h N hN.isLB]
  · rw [hd N hN.isLB]
    exact mul_nonneg (Int.natCast_nonneg d) (hN.nonneg C' hC')

end GlobalTheory.NumPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTwistNonzeroLocusMaps
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TwistCube

open Twist

variable {X : Scheme.{0}} (F : X.Modules) {L : LB X}

theorem mulSecOfEq_zpowSec_comp (σ : LB.Sec (lbZPow L 1)) {n d e : ℤ} (a b : ℕ)
    (h₁ : n + a * 1 = d) (h₂ : d + b * 1 = e) (h₃ : n + ((a + b : ℕ) : ℤ) * 1 = e) :
    mulSecOfEq F (zpowSec σ a) h₁ ≫ mulSecOfEq F (zpowSec σ b) h₂ =
      mulSecOfEq F (zpowSec σ (a + b)) h₃ := by
  ext V s : 3
  exact mulSecOfEq_zpowSec_app σ rfl h₁ h₂ h₃ s

def powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) : F ⟶ twistZ F L c :=
  (twistZZeroIso F hL).hom ≫ mulSecOfEq F (zpowSec σ c) (by omega)

theorem powMap_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ) (h : c + j = d)
    (h' : (c : ℤ) + (j : ℤ) * 1 = d) :
    powMap F hL σ c ≫ mulSecOfEq F (zpowSec σ j) h' = powMap F hL σ d := by
  subst h
  rw [powMap, powMap, Category.assoc, mulSecOfEq_zpowSec_comp F σ c j _ _ (by push_cast; ring)]

theorem bijective_powMap_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {W : X.Opens}
    (hW : W ≤ nonzeroLocus σ) : Function.Bijective ((powMap F hL σ c).app W) := by
  rw [powMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.coe_comp]
  exact (bijective_mulSecOfEq_app hL _ (by omega) (hW.trans (nonzeroLocus_le_zpowSec hL σ c))).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app W))

variable {ι : Type} (U : ι → X.Opens)

theorem isIso_cechCubeMap_powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : IsIso (cechCubeMap ℤ V U (powMap F hL σ c)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun s => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_powMap_app F hL σ c ((cechOpen_le V U s).trans hV)

theorem cechCubeRes_naturality {G : X.Modules} (φ : F ⟶ G) {V : X.Opens} :
    cechCubeMap ℤ ⊤ U φ ≫ cechCubeRes ℤ G (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) =
      cechCubeRes ℤ F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫ cechCubeMap ℤ V U φ :=
  presheafCubeRes_naturality (sectionsPresheafMap ℤ φ) _

def cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F V U :=
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫
    inv (cechCubeMap ℤ V U (powMap F hL σ c))

theorem cubeDiv_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cubeDiv F U hL σ c hV ≫ cechCubeMap ℤ V U (powMap F hL σ c) =
      cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  simp [cubeDiv]

theorem cubeDiv_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) (s : Finset ι) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s) :
    (cechCubeMap ℤ V U (powMap F hL σ c)).app s ((cubeDiv F U hL σ c hV).app s a) =
      (cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)).app s a := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cubeDiv_comp]

theorem cechCubeMap_mul_comp_cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ)
    (h : c + j = d) (h' : (c : ℤ) + (j : ℤ) * 1 = d) {V : X.Opens} (hV : V ≤ nonzeroLocus σ) :
    cechCubeMap ℤ ⊤ U (mulSecOfEq F (zpowSec σ j) h') ≫ cubeDiv F U hL σ d hV =
      cubeDiv F U hL σ c hV := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  haveI := isIso_cechCubeMap_powMap F U hL σ d hV
  unfold cubeDiv
  rw [← Category.assoc, cechCubeRes_naturality, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
  exact congrArg (cechCubeMap ℤ V U) (powMap_comp F hL σ j c d h h')

end TwistCube

end GlobalTheory

theorem GlobalTheory.cechCube_nonzeroLocus_colimit : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  intro X F _ L hL σ₀ ι _ _ U hU
  have hVσ : nonzeroLocus σ₀ ≤ nonzeroLocus (Twist.zofSec σ₀) := (Twist.nonzeroLocus_zofSec hL σ₀).ge
  refine ⟨fun j c d h => cechCubeMap ℤ ⊤ U
      (Twist.mulSecOfEq F (Twist.zpowSec (Twist.zofSec σ₀) j) (by omega)),
    fun c => TwistCube.cubeDiv F U hL (Twist.zofSec σ₀) c hVσ, ?_, ?_, ?_, ?_⟩
  · intro j c d h
    exact TwistCube.cechCubeMap_mul_comp_cubeDiv F U hL _ j c d h _ hVσ
  · intro j j' c d e h h' h''
    exact congrArg (cechCubeMap ℤ ⊤ U) (TwistCube.mulSecOfEq_zpowSec_comp F _ j j' (by omega) _ _)
  · intro s hs b
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    obtain ⟨k, hk⟩ := (Twist.eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (Twist.zofSec σ₀)
      hA.isCompact hA.isQuasiSeparated hle hV ((Twist.twistZZeroIso F hL).hom.app _ b)).exists
    obtain ⟨a, ha⟩ := hk k (by omega)
    exact ⟨k, a, (TwistCube.bijective_powMap_app F hL _ k ((cechOpen_le _ U s).trans hVσ)).1
      ((TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) k hVσ s a).trans ha)⟩
  · intro s hs c a ha
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    have h0 : Twist.resM _ hle a = 0 := by
      have e := TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) c hVσ s a
      rw [ha, map_zero] at e
      exact e.symm
    obtain ⟨k, hk⟩ := (Twist.eventually_mulSecOfEq_zpowSec_eq_zero hL (Twist.zofSec σ₀)
      hA.isCompact hle hV.ge a h0).exists
    exact ⟨k, hk _ (by push_cast; ring)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexDirectLimit
open CategoryTheory Limits Filter

namespace GlobalTheory

namespace CubeColim

variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem termMap_comp {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := rfl

theorem trans_congr {A : ℕ → Cube.{0} ι ℤ} (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d))
    {j j' c d : ℕ} (h : c + j = d) (h' : c + j' = d) (e : j = j') : μ j c d h = μ j' c d h' := by
  subst e; rfl

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; exact hm)

theorem exists_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) :
    ∃ C, ∃ a : Cube.Term (A C) m, Cube.termMap (ρ C) m a = z := by
  choose c a ha using fun s : {s : Finset ι // s.card = m} => h3 s.1 (nonempty_of_card hm s) (z s)
  have hc : ∀ s, c s + (Finset.univ.sup c - c s) = Finset.univ.sup c := fun s => by
    have := Finset.le_sup (f := c) (Finset.mem_univ s); omega
  refine ⟨Finset.univ.sup c,
    fun s => ((μ _ (c s) _ (hc s)).app s.1).hom (a s), funext fun s => ?_⟩
  have e := congrArg (fun f => (f.app s.1).hom (a s)) (h1 _ (c s) _ (hc s))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [Cube.termMap_apply, e]
  exact ha s

theorem exists_kill {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by
  choose j hj using fun s : {s : Finset ι // s.card = m} =>
    h4 s.1 (nonempty_of_card hm s) c (x s) (congrFun hx s)
  refine ⟨Finset.univ.sup j, funext fun s => ?_⟩
  have hle := Finset.le_sup (f := j) (Finset.mem_univ s)
  have hcomp := h2 (j s) (Finset.univ.sup j - j s) c (c + j s) (c + Finset.univ.sup j) rfl
    (by omega) (by omega)
  have e : μ (Finset.univ.sup j) c (c + Finset.univ.sup j) rfl =
      μ (j s + (Finset.univ.sup j - j s)) c (c + Finset.univ.sup j) (by omega) :=
    trans_congr μ _ _ (by omega)
  rw [Cube.termMap_apply, e, ← hcomp]
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e : ((μ (j s) c (c + j s) rfl).app s.1).hom (x s) = 0 := hj s
  rw [e, map_zero]
  rfl

theorem exists_cocycle_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) (hz : Cube.d B m z = 0) :
    ∃ C, ∀ c, C ≤ c → ∃ a : Cube.Term (A c) m,
      Cube.termMap (ρ c) m a = z ∧ Cube.d (A c) m a = 0 := by
  obtain ⟨C₀, a, ha⟩ := exists_lift μ ρ h1 h3 hm z
  have hda : Cube.termMap (ρ C₀) (m + 1) (Cube.d (A C₀) m a) = 0 := by
    rw [Cube.termMap_d, ha, hz]
  obtain ⟨J, hJ⟩ := exists_kill μ ρ h2 h4 (Nat.succ_pos m) C₀ _ hda
  refine ⟨C₀ + J, fun c hc => ⟨Cube.termMap (μ (c - C₀) C₀ c (by omega)) m a, ?_, ?_⟩⟩
  · rw [← termMap_comp, h1, ha]
  · rw [← Cube.termMap_d]
    have e : μ (c - C₀) C₀ c (by omega) =
        μ J C₀ (C₀ + J) rfl ≫ μ (c - C₀ - J) (C₀ + J) c (by omega) := by
      rw [h2 J (c - C₀ - J) C₀ (C₀ + J) c rfl (by omega) (by omega)]
      exact trans_congr μ _ _ (by omega)
    rw [e, termMap_comp, hJ, map_zero]

end CubeColim

theorem cechComplex_homology_isZero_of_colimit :
    ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  intro ι _ _ A B μ ρ h1 h2 h3 h4 n hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d B 0]
    change Function.Injective (Cube.d B 1)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 one_pos z hz
    obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hN (max C N) (le_max_right _ _))
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d _ 0] at hex
    change Function.Injective (Cube.d (A (max C N)) 1) at hex
    rw [injective_iff_map_eq_zero] at hex
    rw [← ha, hex a hda, map_zero]
  | succ p =>
    rw [cechComplex_exactAt_succ_iff]
    intro z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 (m := p + 2) (by omega) z hz
      obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
      have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (hN (max C N) (le_max_right _ _))
      rw [cechComplex_exactAt_succ_iff] at hex
      obtain ⟨y, hy⟩ := (hex a).1 hda
      exact ⟨Cube.termMap (ρ _) (p + 1) y, by rw [← Cube.termMap_d, hy, ha]⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d B (p + 1) y

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwist
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecomposition
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecomposition
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Div.SncBoundary

noncomputable def multHom {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (z : X) :
    CartierDiv X →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) fun D E => CartierDiv.mult_add D E z

private theorem regAt_of_ord_eq_zero_of_normal {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    {z : X} (hz : Order.coheight z = 1) {f : X.functionField} (hf : f ≠ 0)
    (h0 : Scheme.ord f z = 0) : RegAt z f := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨hD, hI⟩ := hN z
  have hnf : ¬ IsField (X.presheaf.stalk z) := by
    intro hF
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [ringKrullDim_eq_zero_of_isField hF, hz] at h1
    norm_num at h1
  haveI : Ring.DimensionLEOne (X.presheaf.stalk z) :=
    ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  have hDD : IsDedekindDomain (X.presheaf.stalk z) :=
    (isDedekindDomain_iff _ X.functionField).mpr
      ⟨hD, inferInstance, inferInstance, fun hx => (isIntegrallyClosed_iff X.functionField).mp hI hx⟩
  have hTF := IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf
  have hV : ValuationRing (X.presheaf.stalk z) := (hTF.out 3 2).mp hDD
  have hord : Ring.ordFrac (X.presheaf.stalk z) f = 1 := by
    have := (Scheme.ord_eq_iff hz hf).1 h0
    simpa [Scheme.ordHom] using this
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) f with ⟨a, ha⟩ | ⟨r, hr⟩
  · exact ⟨a, ha⟩
  · have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [map_zero] at hr
      exact hf (inv_eq_zero.mp hr.symm)
    have h2 : Ring.ordMonoidWithZeroHom (X.presheaf.stalk z) r = 1 := by
      rw [← Ring.ordFrac_eq_ord (K := X.functionField) _, hr, map_inv₀, hord, inv_one]
    have hmem : r ∈ nonZeroDivisors (X.presheaf.stalk z) := mem_nonZeroDivisors_of_ne_zero hr0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hmem)
    rw [Ring.ordMonoidWithZeroHom_eq_coe _ hmem hn.symm] at h2
    have hn1 : Multiplicative.ofAdd (n : ℤ) = 1 := by exact_mod_cast h2
    have hn0 : n = 0 := by
      have : (n : ℤ) = 0 := by simpa using hn1
      exact_mod_cast this
    have h3 : Ring.ord (X.presheaf.stalk z) r = 0 := by rw [← hn, hn0]; rfl
    have hsub : Subsingleton (X.presheaf.stalk z ⧸ Ideal.span {r}) :=
      Module.length_eq_zero_iff.mp h3
    have hu : IsUnit r :=
      Ideal.span_singleton_eq_top.mp (Ideal.Quotient.subsingleton_iff.mp hsub)
    refine ⟨↑hu.unit⁻¹, ?_⟩
    have hm : algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹ : X.presheaf.stalk z) *
        algebraMap (X.presheaf.stalk z) X.functionField r = 1 := by
      rw [← map_mul]
      simp
    rw [hr] at hm
    exact (mul_inv_eq_one₀ hf).1 hm

private theorem cartierDiv_eff_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E.Eff := by
  haveI : GlobalTheory.IsNormalScheme X := ⟨fun x => (hN x).1, fun x => (hN x).2⟩
  rw [CartierDiv.eff_iff]
  intro x g hg
  apply GlobalTheory.Discrepancy.regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz : E.IsEqn z g := hU z (hzx.mem_open U.isOpen hxU)
  refine regAt_of_ord_eq_zero_of_normal hN hz g.ne_zero ?_
  rw [← hgz.mult_eq]
  exact h z

private theorem cartierDiv_eq_zero_of_mult_eq_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (E : CartierDiv X)
    (h : ∀ z, E.mult z = 0) : E = 0 := by
  refine CartierDiv.Eff.eq_zero (cartierDiv_eff_of_mult_eq_zero hN E h) (cartierDiv_eff_of_mult_eq_zero hN (-E) fun z => ?_)
  show multHom z (-E) = 0
  rw [map_neg]
  exact neg_eq_zero.mpr (h z)

private theorem cartierDiv_mult_nonneg_of_eff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {D : CartierDiv X} (hD : D.Eff) (z : X) : 0 ≤ D.mult z := by
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  rw [hg.mult_eq]
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, ha⟩ := CartierDiv.eff_iff.mp hD z g hg
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp only [map_zero] at ha
      exact g.ne_zero ha.symm
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    rw [Scheme.le_ord_iff hz g.ne_zero, ← ha]
    have := Ring.ordFrac_ge_one_of_ne_zero (R := X.presheaf.stalk z) (K := X.functionField) ha0
    simpa [Scheme.ordHom] using this
  · simp [Scheme.ord_eq_zero_of_coheight_neq_one hz]

theorem vanishing_ample_snc_cartier : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ Y _ _ q n _ hp Kc Q A hQ hA B Γ e hB hΓ hsupp hmult heq i hi
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth (n := n) (f := q)
  obtain ⟨-, hN, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y q hsm
  obtain ⟨r, w, D, σ, hw, hD, hBw, hrel⟩ := SncComp.relSnc_components k Y q n hp B hB
  have hnn : ∀ z, 0 ≤ Γ.mult z := cartierDiv_mult_nonneg_of_eff hΓ
  let b : Fin r → ℕ := fun j => (Γ.mult (w j)).toNat
  have hdec : Γ = ∑ j, b j • D j := by
    refine sub_eq_zero.mp (cartierDiv_eq_zero_of_mult_eq_zero (fun x => ⟨hN.1 x, hN.2 x⟩) _ fun z => ?_)
    show multHom z (Γ - ∑ j, b j • D j) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_nsmul]
    show Γ.mult z - ∑ j, b j • (D j).mult z = 0
    by_cases hz : ∃ j, z = w j
    · obtain ⟨j, rfl⟩ := hz
      rw [Finset.sum_eq_single j]
      · rw [(hD j).1]
        simp only [b, nsmul_eq_mul, mul_one]
        have := hnn (w j)
        omega
      · intro l _ hl
        rw [(hD l).2 (w j) (fun h => hl (hw h.symm)), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · push_neg at hz
      rw [Finset.sum_eq_zero fun j _ => by rw [(hD j).2 z (hz j), smul_zero], sub_zero]
      by_contra hne
      obtain ⟨j, hj⟩ := hBw z (CartierDiv.coheight_eq_one_of_mult_ne_zero hne)
        (hsupp (CartierDiv.mem_supp_of_mult_ne_zero hne))
      exact hz j hj
  have he : 0 < e := by
    have h1 := hmult (genericPoint Y)
    have h2 := hnn (genericPoint Y)
    omega
  have hb : ∀ j, b j < e := by
    intro j
    have h1 := hmult (w j)
    have h2 := hnn (w j)
    simp only [b]
    omega
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum] at heq
  simp only [map_nsmul, toPic_apply] at heq
  exact GlobalTheory.Div.vanishing_ample_snc_charZero k Y q n hp r (fun j => toLB (D j)) σ hrel Kc Q A hQ hA
    e b he hb heq i hi

end GlobalTheory.Div.SncBoundary
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncBoundaryAmpleDecompositionStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_boundary_ample_decomposition : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Kc : CanonLB q n) (Q A : LB Y) (hQ : Q.IsLB) (hA : IsAmpleLB A) (B : Closeds Y) (Γ : CartierDiv Y) (e : ℕ), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → Γ.Eff → Γ.supp ≤ B → (∀ z, Γ.mult z < e) → e • cls Q hQ = e • cls Kc.bundle Kc.isLB + toPic Γ + cls A hA.isLB → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  first | exact @_root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | exact _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier | (intros; apply _root_.GlobalTheory.Div.SncBoundary.vanishing_ample_snc_cartier <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultipleBelowThreshold
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_multiple_below_threshold : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  first | exact @_root_.GlobalTheory.CoefBound.coef_lt_of_large | exact _root_.GlobalTheory.CoefBound.coef_lt_of_large | (intros; apply _root_.GlobalTheory.CoefBound.coef_lt_of_large <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AmpleAddNefIsAmple
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ample_add_nef_is_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  first | exact @_root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | exact _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef | (intros; apply _root_.GlobalTheory.isAmpleLB_of_cls_eq_ample_add_nef <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NefPullbackIsNef
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.nef_pullback_is_nef : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  first | exact @_root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver | exact _root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver | (intros; apply _root_.GlobalTheory.NumPull.isNef_pull_of_isProjOver <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwist
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResVanish

open GlobalTheory.Cartier.CartierDiv in
private theorem mult_zero₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    (0 : CartierDiv Y).mult z = 0 := by
  have h := CartierDiv.mult_add (0 : CartierDiv Y) 0 z
  rw [add_zero] at h
  linarith

private theorem mult_nsmul₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D : CartierDiv Y) (n : ℕ) (z : Y) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero₀]; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

private theorem mult_sub₀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  linarith

private theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) (n : ℕ) :
    (n • D).supp ≤ D.supp := by
  induction n with
  | zero => rw [zero_nsmul, (CartierDiv.supp_eq_bot_iff).2 rfl]; exact bot_le
  | succ n ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

private theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

end GlobalTheory.LogResVanish


open GlobalTheory.LogResVanish in
theorem GlobalTheory.Discrepancy.vanishing_logRes_floor : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm h hF N M T hN hM r hT hr hTc hMn a Fd A hA hAF Q hQ hQc i hi
  obtain ⟨ha, hFd, hFdB, hAc⟩ := hAF
  have hTlb : T.IsLB := by letI := algebraΓOfHom p; exact hT.isLB
  haveI := h.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : CompactSpace Y := compactSpace_of_projOver h.proj
  haveI : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  set Γ := pullCart s G - m • K with hΓ
  set R := Γ - m • F with hR
  have hRm : ∀ z, R.mult z = Γ.mult z % (m : ℤ) := fun z => by
    rw [hR, mult_sub₀, mult_nsmul₀, hF z, Int.emod_def]
  have hR0 : ∀ z, 0 ≤ R.mult z := fun z => (hRm z).symm ▸ Int.emod_nonneg _ hm0
  have hRlt : ∀ z, R.mult z < m := fun z =>
    (hRm z).symm ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hReff : R.Eff := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).1).2 hR0
  have hRB : R.supp ≤ B := fun x hx => by
    obtain ⟨z, hzx, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y R).2.1 x).1 hx
    refine h.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 x).2 ⟨z, hzx, fun e => hz ?_⟩)
    rw [hRm, e, Int.zero_emod]

  obtain ⟨b, hab, hb⟩ := GlobalTheory.T.exists_multiple_below_threshold Y R Fd m r a hr hRlt
  set Γ' := (r * b) • R + m • Fd with hΓ'
  have hΓ'eff : Γ'.Eff := (eff_nsmul hReff _).add (eff_nsmul hFd _)
  have hΓ'B : Γ'.supp ≤ B := (CartierDiv.supp_add_le _ _).trans
    (sup_le ((supp_nsmul_le _ _).trans hRB) ((supp_nsmul_le _ _).trans hFdB))

  have hAm : IsAmpleLB (lbPow A m) := (isAmpleLB_pow_iff hA.isLB hm).2 hA
  letI := algebraΓOfHom (s ≫ p)
  have hTp : IsNef k (T.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp T hT
  have hMp : IsNef k (M.pull s) := GlobalTheory.T.nef_pullback_is_nef k X Y p s hp M hMn
  obtain ⟨P, hP, hPc⟩ := cls_surj (b • cls (T.pull s) hTp.isLB + (m * (b - a)) • cls (M.pull s) hMp.isLB)
  have hPn : IsNef k P := (hTp.pow hA b).of_cls_eq_add (hMp.pow hA (m * (b - a))) hA hP
    (by rw [hPc, cls_lbPow hTp.isLB, cls_lbPow hMp.isLB])
  obtain ⟨A', hA'lb, hA'c⟩ := cls_surj (cls (lbPow A m) hAm.isLB + cls P hPn.isLB)
  have hA' : IsAmpleLB A' := GlobalTheory.T.ample_add_nef_is_ample k Y (s ≫ p) h.proj (lbPow A m) P A' hAm hPn hA'lb hA'c

  let Kc := CanonLB.all (s ≫ p) n
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := fun e =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s h.bir n).1 (e.trans (map_zero _).symm))
  have hK : toPic K = cls Kc.bundle Kc.isLB := (GlobalTheory.T.canonical_divisor_of_form k Y (s ≫ p) n _ hne).2 K h.div Kc
  refine GlobalTheory.T.snc_boundary_ample_decomposition k Y (s ≫ p) n h.proj Kc Q A' hQ hA' B Γ' (m * r * b) h.snc hΓ'eff hΓ'B hb ?_ i hi

  rw [hA'c, cls_lbPow hA.isLB, hPc, cls_pull hTlb, cls_pull hM, hTc, ← hK, hQc]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have e1 : toPic Γ' = (r * (a + c)) • (toPic (pullCart s G) - m • toPic K - m • toPic F) +
      m • toPic Fd := by
    rw [hΓ', hR, hΓ]; simp only [map_add (f := _), map_nsmul, map_sub]
  have e2 : m • toPic Fd = m • (a • CechPic.pull s (cls M hM) - cls A hA.isLB) := by
    rw [hAc, add_sub_cancel_left]
  rw [e1, add_assoc, e2, toPic_pullCart]
  simp only [map_sub, map_nsmul, Nat.add_sub_cancel_left]
  module
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_vanishing_nef_twist : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  first | exact @_root_.GlobalTheory.Discrepancy.vanishing_logRes_floor | exact _root_.GlobalTheory.Discrepancy.vanishing_logRes_floor | (intros; apply _root_.GlobalTheory.Discrepancy.vanishing_logRes_floor <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffine
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingIntersections
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechTwistNonzeroLocusMaps
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory
theorem _root_.GlobalTheory.T.cech_twist_nonzero_locus_maps : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  first | exact @_root_.GlobalTheory.cechCube_nonzeroLocus_colimit | exact _root_.GlobalTheory.cechCube_nonzeroLocus_colimit | (intros; apply _root_.GlobalTheory.cechCube_nonzeroLocus_colimit <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechComplexDirectLimit
open CategoryTheory Limits Filter GlobalTheory
theorem _root_.GlobalTheory.T.cech_complex_direct_limit : ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  first | exact @_root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | exact _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | (intros; apply _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit <;> assumption)
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory

theorem isZero_cechH_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec)
    {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens),
    (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∀ n : ℕ,
    (∀ᶠ c : ℕ in atTop, IsZero (cechH ℤ (twistZ F L c) ⊤ U n)) → IsZero (cechH ℤ F (nonzeroLocus σ) U n) := by
  intro X F _ L hL σ ι _ _ U hU n h
  obtain ⟨μ, ρ, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.cech_twist_nonzero_locus_maps X F L hL σ U hU
  exact GlobalTheory.T.cech_complex_direct_limit (fun c => cechCube ℤ (twistZ F L c) ⊤ U) (cechCube ℤ F (nonzeroLocus σ) U) μ ρ h₁ h₂ h₃ h₄ n h

theorem subsingleton_cohOn_nonzeroLocus_of_eventually_twist : ∀ (X : Scheme.{0}) [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) (i : ℕ), (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow L c)) i)) → Subsingleton (cohOn F (nonzeroLocus σ) i) := by
  intro X _ _ F _ L hL σ i h
  obtain ⟨κ, hκ, T, c, hT, -, hTc, hcov⟩ :=
    Twist.exists_finite_affine_chart_cover hL (W := ⊤) (isCompact_univ (X := X))
  letI : Fintype κ := Fintype.ofFinite κ
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hsep : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ a ∈ s, T a) :=
    (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl inferInstance) κ T hT
  have hc : ⨆ a, T a = ⊤ := eq_top_iff.2 hcov
  have hV : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (cechOpen (nonzeroLocus σ) T s) := by
    rintro s ⟨a, ha⟩
    have hle : ⨅ b ∈ s, T b ≤ L.U (c a) := (biInf_le T ha).trans (hTc a)
    have e := Twist.basicOpen_resG_zfun (Twist.zofSec σ) (c a) hle
    rw [Twist.nonzeroLocus_zofSec hL] at e
    have e' : cechOpen (nonzeroLocus σ) T s = X.basicOpen (resG X hle (Twist.zfun (Twist.zofSec σ) (c a))) := by
      rw [e, cechOpen, inf_comm]
    rw [e']
    exact (hsep s ⟨a, ha⟩).basicOpen _
  have hVc : nonzeroLocus σ ≤ ⨆ a, T a := hc ▸ le_top
  have eV := cechHEquivCohOn ℤ hVc (cechAcyclicMod_of_isAffineOpen hV F) i
  have hZ : IsZero (cechH ℤ F (nonzeroLocus σ) T i) := by
    refine isZero_cechH_nonzeroLocus_of_eventually_twist X F L hL σ T hsep i (h.mono fun k hk => ?_)
    haveI hq : (twistZ F L k).IsQuasicoherent := Twist.isQuasicoherent_twist (Twist.isLB_lbZPow hL k)
    have e2 := cechHEquivCoh ℤ hc hsep (twistZ F L k) i
    haveI : Subsingleton (coh (twistZ F L k) i) := by rw [Twist.twistZ_natCast]; exact hk
    haveI : Subsingleton (cechH ℤ (twistZ F L k) ⊤ T i) := e2.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  haveI : Subsingleton (cechH ℤ F (nonzeroLocus σ) T i) := ModuleCat.subsingleton_of_isZero hZ
  exact eV.symm.injective.subsingleton

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory

private theorem exists_sec_lbPow_add_nonzeroLocus_eq_inf {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {m n : ℕ} (s : (lbPow L m).Sec) (s' : (lbPow L n).Sec) :
    ∃ τ : (lbPow L (m + n)).Sec, nonzeroLocus τ = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine ⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩
  · intro i j
    rw [map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]
    ring
  · rw [nonzeroLocus_powSecMk]
    simp_rw [Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]
    apply le_antisymm
    · exact iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      have hx' : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩

theorem exists_sec_lbPow_nonzeroLocus_eq_iInf {X : Scheme.{0}} {H : LB X} (hH : H.IsLB)
    {r : ℕ} (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec) (he : ∀ a, 0 < e a)
    (t : Finset (Fin r)) (ht : t.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : (lbPow H N).Sec, nonzeroLocus τ = ⨅ a ∈ t, nonzeroLocus (σ a) := by
  induction t using Finset.cons_induction with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨e a, he a, σ a, ?_⟩
      simp
    · obtain ⟨N, hN, τ, hτ⟩ := ih hs
      obtain ⟨τ', hτ'⟩ := exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ
      refine ⟨e a + N, by omega, τ', ?_⟩
      rw [hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]

theorem subsingleton_cohOn_preimage_iInf_nonzeroLocus : ∀ (X Y : Scheme.{0}) [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), H.IsLB → ∀ j : ℕ, (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → ∀ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec), (∀ a, 0 < e a) → ∀ t : Finset (Fin r), t.Nonempty → Subsingleton (cohOn F (s ⁻¹ᵁ (⨅ a ∈ t, nonzeroLocus (σ a))) j) := by
  intro X Y _ _ s F _ H hH j hev r e σ he t ht
  obtain ⟨N, hN, τ, hτ⟩ := exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht
  rw [← hτ, ← nonzeroLocus_secPowPull τ s]
  have hM : (H.pull s).IsLB := LB.isLB_pull hH s
  have hL : (lbPow (H.pull s) N).IsLB := isLB_lbPow hM N
  apply subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨c0, fun c hc => ?_⟩
  have hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c)
      = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c)) := by
    rw [CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]
  obtain ⟨iso⟩ := nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls
  have hsub := hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))
  exact (cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffine
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PassageDown

theorem exists_cover_of_isCompact {X : Scheme.{0}} {H : LB X} (h : IsAmpleLB H) {V : X.Opens}
    (hV : IsCompact (V : Set X)) : ∃ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec),
      (∀ a, 0 < e a) ∧ (∀ a, IsAffineOpen (nonzeroLocus (σ a))) ∧ ⨆ a, nonzeroLocus (σ a) = V := by
  classical
  have key : ∀ x : V, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (lbPow H n).Sec, (x : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ V ∧ IsAffineOpen (nonzeroLocus s) := fun x => h.exists_affine_le x.2
  choose n hn s hxs hsV hsA using key
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V => (nonzeroLocus (s x) : Set X))
    (fun x => (nonzeroLocus (s x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxs _⟩)
  refine ⟨t.card, fun a => n (t.equivFin.symm a), fun a => s (t.equivFin.symm a),
    fun a => hn _, fun a => hsA _, ?_⟩
  apply le_antisymm
  · exact iSup_le fun a => hsV _
  · intro y hy
    have hy' := ht hy
    simp only [Set.mem_iUnion] at hy'
    obtain ⟨i, hi, hyi⟩ := hy'
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨j, hj⟩ : ∃ j, t.equivFin.symm j = ⟨i, hi⟩ := ⟨_, Equiv.symm_apply_apply _ _⟩
    refine ⟨j, ?_⟩
    show y ∈ nonzeroLocus (s ↑(t.equivFin.symm j))
    rw [hj]
    exact hyi

end GlobalTheory.PassageDown

private theorem passage_cohOn_lemma {X Y : Scheme.{0}} (s : Y ⟶ X) (F : Y.Modules) (V : X.Opens)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hV : V ≤ ⨆ i, U i)
    (hP : CechAcyclicMod V U ((Scheme.Modules.pushforward s).obj F))
    (hF : CechAcyclicMod (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) F) (n : ℕ) :
    Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
  have hV' : s ⁻¹ᵁ V ≤ ⨆ i, s ⁻¹ᵁ U i := by
    intro y hy
    have hy' := hV hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy' ⊢
    exact hy'
  let φ := cechCubePushforwardIso V U (R := ℤ) F (g := s) (fun r => by simp)
  haveI : IsIso (cechComplexMap φ.hom) :=
    isIso_cechComplexMap _ (fun t _ => ConcreteCategory.bijective_of_isIso (φ.hom.app t))
  let e1 := cechAbHEquivH' hV (cechAcyclicMod_iff.1 hP) n
  let e2 := cechAbHEquivH' hV' (cechAcyclicMod_iff.1 hF) n
  let e3 := cechAbHEquiv ℤ ((Scheme.Modules.pushforward s).obj F) V U n
  let e4 := cechAbHEquiv ℤ F (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) n
  let e5 := (HomologicalComplex.homologyMapIso (asIso (cechComplexMap φ.hom)) n).toLinearEquiv.toAddEquiv
  exact ⟨e1.symm.trans (e3.trans (e5.trans (e4.symm.trans e2)))⟩

theorem GlobalTheory.passage_down_of_twist_vanishing : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  intro X Y _ _ _ _ s F _ H hH hvan
  haveI : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward s).obj F) :=
    GlobalTheory.QCoh.isQuasicoherent_pushforward s F
  have key : ∀ V : X.Opens, IsCompact (V : Set X) → ∀ n,
      Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
    intro V hV n
    obtain ⟨r, e, σ, he, hA, hcov⟩ := GlobalTheory.PassageDown.exists_cover_of_isCompact hH hV
    have hle : ∀ a, nonzeroLocus (σ a) ≤ V := fun a => hcov ▸ le_iSup (fun a => nonzeroLocus (σ a)) a
    have hint : ∀ t : Finset (Fin r), t.Nonempty → IsAffineOpen (⨅ a ∈ t, nonzeroLocus (σ a)) :=
      fun t ht => GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated (R := Γ(X, ⊤)) X.toSpecΓ hA t ht
    apply passage_cohOn_lemma s F V (fun a => nonzeroLocus (σ a)) hcov.ge
    · exact cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le hle hint) _
    · intro t ht q
      rw [← preimage_cechOpen, cechOpen_of_nonempty hle ht]
      exact subsingleton_cohOn_preimage_iInf_nonzeroLocus X Y s F H hH.isLB (q + 1)
        (hvan _ (Nat.succ_pos q)) r e σ he t ht
  refine ⟨fun i => ?_, fun U hU j hj => ?_⟩
  · obtain ⟨f⟩ := key ⊤ (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) i
    exact ⟨f⟩
  · obtain ⟨f⟩ := key U hU.isCompact j
    haveI : Subsingleton (cohOn ((Scheme.Modules.pushforward s).obj F) U j) := by
      refine subsingleton_cohOn_of_cechAcyclic (ι := Unit) (U := fun _ => U)
        (le_iSup (fun _ : Unit => U) ()) ?_ (by rw [Fintype.card_unit]; exact hj)
      refine cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le (fun _ => le_rfl) ?_) _
      intro t ht
      obtain ⟨i, hi⟩ := ht
      rwa [show (⨅ _ ∈ t, U) = U from le_antisymm (biInf_le _ hi) (le_iInf₂ fun _ _ => le_rfl)]
    exact f.symm.toEquiv.subsingleton
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffineStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_cohomology_affine : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  first | exact @_root_.GlobalTheory.passage_down_of_twist_vanishing | exact _root_.GlobalTheory.passage_down_of_twist_vanishing | (intros; apply _root_.GlobalTheory.passage_down_of_twist_vanishing <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmple
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.LogResVanish

theorem isSeparated_of_isProjOver {k : Type} [Field k] {Z : Scheme.{0}} {f : Z ⟶ Sp k}
    (h : IsProjOver f) : Z.IsSeparated := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str k N) := by unfold PSpace.str; infer_instance
  exact ⟨by rw [← terminal.comp_from (i ≫ PSpace.str k N)]; infer_instance⟩

end GlobalTheory.LogResVanish


open GlobalTheory.LogResVanish in
theorem GlobalTheory.vanishing_logRes_pushforward_and_local : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → (∀ i, 0 < i → Subsingleton (coh (twist ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB (-F)))) N) i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (s ⁻¹ᵁ U) j) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF N M T hN hM r hT hr hcl hMnef a Fd A hA hAF
  letI := algebraΓOfHom p
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  have hHl : H.IsLB := hH.isLB
  have : CompactSpace X := hH.compactSpace
  have : CompactSpace Y := hA.compactSpace
  have : X.IsSeparated := isSeparated_of_isProjOver hp
  have : Y.IsSeparated := isSeparated_of_isProjOver hres.proj
  have hA0 : (toLB (-F)).IsLB := isLB_toLB _

  have key : ∀ (N' T' : LB X) (hN' : N'.IsLB) (hT' : IsNef k T'),
      cls T' hT'.isLB = (m * r) • cls N' hN' - r • toPic G - m • cls M hM →
      ∀ i, 0 < i → Subsingleton (coh (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N'.pull s)) i) := by
    intro N' T' hN' hT' e i hi
    obtain ⟨Q, hQ, eQ⟩ := cls_surj (CechPic.pull s (cls N' hN') - toPic F)
    have h := GlobalTheory.T.multiplier_vanishing_nef_twist k X p n hp η m G Y s K B F hη hm hres hF N' M T' hN' hM r hT' hr e hMnef
      a Fd A hA hAF Q hQ eQ i hi
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) hA0 (pull_isLB hN' s) hQ
      (by rw [eQ, cls_pull hN' s, ← toPic_apply, map_neg]; abel)
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ i iso).toEquiv.subsingleton_congr.2 h
  have hev : ∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist (twist (twist
      (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (lbPow (H.pull s) c)) j) := by
    intro j hj
    refine Eventually.of_forall fun c => ?_
    have hNc : (tens N (lbPow H c)).IsLB := isLB_tens hN (isLB_lbPow hHl c)
    have hTc : IsNef k (tens T (lbPow H (m * r * c))) :=
      hT.tens ((IsAmpleLB.isNef (k := k) hH).pow hH _) hH
    have ec : cls _ hTc.isLB = (m * r) • cls _ hNc - r • toPic G - m • cls M hM := by
      rw [cls_tens hT.isLB (isLB_lbPow hHl _), cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl,
        cls_lbPow hHl, hcl, smul_add, smul_smul]
      abel
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq
      (twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
      (isLB_lbPow (pull_isLB hHl s) c) (pull_isLB hNc s)
      (by rw [cls_pull hNc s, cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl, cls_pull hN s,
        cls_lbPow (pull_isLB hHl s), cls_pull hHl s, map_add, map_nsmul])
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ j iso).toEquiv.subsingleton_congr.2 (key _ _ hNc hTc ec j hj)
  have : (GlobalTheory.structureModule Y).IsQuasicoherent := inferInstance
  have := Twist.isQuasicoherent_twist (F := GlobalTheory.structureModule Y) hA0
  have := Twist.isQuasicoherent_twist (F := twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
  have hdown := GlobalTheory.T.pushforward_cohomology_affine X Y s _ H hH hev
  refine ⟨fun i hi => ?_, hdown.2⟩
  obtain ⟨e⟩ := hdown.1 i
  have h0 := key N T hN hT hcl i hi
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ i (Twist.projIso N s _).symm).toEquiv.subsingleton_congr.2
    (e.toEquiv.subsingleton_congr.2 h0)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmpleStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_vanishing_nef_twist_ample : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → (∀ i, 0 < i → Subsingleton (coh (twist ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB (-F)))) N) i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (s ⁻¹ᵁ U) j) := by
  first | exact @_root_.GlobalTheory.vanishing_logRes_pushforward_and_local | exact _root_.GlobalTheory.vanishing_logRes_pushforward_and_local | (intros; apply _root_.GlobalTheory.vanishing_logRes_pushforward_and_local <;> assumption)
end
