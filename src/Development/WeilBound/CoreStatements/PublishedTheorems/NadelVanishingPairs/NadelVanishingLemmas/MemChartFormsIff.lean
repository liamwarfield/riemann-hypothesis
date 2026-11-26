module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ChartFormsDifferentialClosed
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsEqChartForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.mem_chart_forms_iff : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K), η ∈ chartForms A x J t a ↔ ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧ (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I := by
  first | exact @_root_.GlobalTheory.LogDR.mem_chartForms_iff | exact _root_.GlobalTheory.LogDR.mem_chartForms_iff | (intros; apply _root_.GlobalTheory.LogDR.mem_chartForms_iff <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosed
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosed
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory.LogDR

theorem extD_mem_logSec_roundedTwist : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (q : ℕ) (W : X.Opens) (η : abelian₂ X.functionField), η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) q W → extD _ η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) (q + 1) W := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr q W η hη
  simp only [logSec, latSec, AddSubgroup.mem_iInf] at hη ⊢
  intro y hy
  have hcov : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := (Opens.mem_iSup).1 hcov
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨-, hloc⟩ := GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr
  obtain ⟨ρ, -, hρ⟩ := hloc i
  have heq := hρ y hi t ht
  have hstalk := GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) (p • G + ∑ c, r c • E c) y
    (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j)
  have h1 := hη y hy
  rw [hstalk q (𝒜.chart i) hi heq] at h1
  rw [hstalk (q + 1) (𝒜.chart i) hi heq]
  exact GlobalTheory.T.chart_forms_differential_closed X.functionField p (locRing y) n (𝒜.x i) (𝒜.J i) t ρ
    ((𝒜.chart i).chart y hi) q η h1

end GlobalTheory.LogDR
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.log_sections_differential_closed : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (q : ℕ) (W : X.Opens) (η : abelian₂ X.functionField), η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) q W → extD _ η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) (q + 1) W := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_logSec_roundedTwist | exact _root_.GlobalTheory.LogDR.extD_mem_logSec_roundedTwist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_logSec_roundedTwist <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLatticeCohomologyVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLatticeCohomologyVanish
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatCech

variable {ι : Type} [LinearOrder ι] {V : Type} [AddCommGroup V]
  (A : Cube.{0} ι ℤ) (φ : ∀ s : Finset ι, A.obj s →+ V)

def toFam (m : ℕ) (x : Cube.Term A m) : Finset ι → V :=
  fun s => if h : s.card = m then φ s (x ⟨s, h⟩) else 0

variable {A φ}

theorem toFam_zero (m : ℕ) : toFam A φ m 0 = 0 := by
  funext s; unfold toFam; split_ifs <;> simp

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) {s : Finset ι} (h : s.card = m) : s.Nonempty :=
  Finset.card_pos.1 (by rw [h]; exact hm)

theorem delta_toFam {m : ℕ} (hm : 0 < m)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x)
    (x : Cube.Term A m) : DI.delta (toFam A φ m x) = toFam A φ (m + 1) (Cube.d A m x) := by
  funext t
  unfold DI.delta toFam
  by_cases ht : t.card = m + 1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_left ht, Cube.d_apply, map_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (t.erase i.1).card = m := by rw [Finset.card_erase_of_mem i.2, ht]; rfl
    rw [dite_eq_left hc, map_zsmul, hres _ _ _ (nonempty_of_card hm hc)]
  · rw [dite_eq_right ht]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ m := by
      have := Finset.card_pos.2 ⟨i, hi⟩
      rw [Finset.card_erase_of_mem hi]; omega
    rw [dite_eq_right hc, smul_zero]

theorem toFam_inCech {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) (x : Cube.Term A m) :
    DI.InCech N m (toFam A φ m x) := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold toFam; rw [dite_eq_right (by simp; omega)]
  · unfold toFam
    split_ifs with h
    · rw [← hrange s (nonempty_of_card hm h)]; exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · exact zero_mem _
  · unfold toFam; rw [dite_eq_right hs]

theorem toFam_injective {m : ℕ} (hm : 0 < m) (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    {x y : Cube.Term A m} (h : toFam A φ m x = toFam A φ m y) : x = y := by
  funext s
  have := congrFun h s.1
  unfold toFam at this
  rw [dite_eq_left s.2, dite_eq_left s.2] at this
  exact hinj _ (nonempty_of_card hm s.2) this

theorem exists_toFam {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) {c : Finset ι → V} (hc : DI.InCech N m c) :
    ∃ x : Cube.Term A m, toFam A φ m x = c := by
  have hex : ∀ s : {s : Finset ι // s.card = m}, ∃ y, φ s.1 y = c s.1 := fun s =>
    AddMonoidHom.mem_range.1 (by rw [hrange _ (nonempty_of_card hm s.2)]; exact hc.2.1 s.1)
  choose g hg using hex
  refine ⟨g, funext fun s => ?_⟩
  unfold toFam
  split_ifs with h
  · exact hg ⟨s, h⟩
  · exact (hc.2.2 s h).symm

theorem exact_iff_cechZero {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x) :
    Function.Exact (Cube.d A m) (Cube.d A (m + 1)) ↔ DI.CechZero N m := by
  have hm1 : 0 < m + 1 := Nat.succ_pos m
  constructor
  · intro hex c hc hdc
    obtain ⟨x, rfl⟩ := exists_toFam (A := A) hm1 hrange hc
    have hdx : Cube.d A (m + 1) x = 0 := toFam_injective (Nat.succ_pos _) hinj
      (by rw [← delta_toFam hm1 hres, hdc, toFam_zero])
    obtain ⟨y, hy⟩ := (hex x).1 hdx
    exact ⟨toFam A φ m y, toFam_inCech hm hrange y, by rw [delta_toFam hm hres, hy]⟩
  · intro hcz x
    constructor
    · intro hdx
      obtain ⟨y', hy'c, hy'd⟩ := hcz (toFam A φ (m + 1) x) (toFam_inCech hm1 hrange x)
        (by rw [delta_toFam hm1 hres, hdx, toFam_zero])
      obtain ⟨y, rfl⟩ := exists_toFam (A := A) hm hrange hy'c
      exact ⟨y, toFam_injective hm1 hinj (by rw [← delta_toFam hm hres, hy'd])⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d A m y

end GlobalTheory.LatCech

namespace GlobalTheory

theorem cechZero_latSec_iff_subsingleton_coh : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated]
    {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F →
    (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b →
    (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  intro X _ hsepX V _ _ M F _ ι _ _ U hL hA hg hc b hb
  letI : X.IsSeparated := hsepX
  have hsep : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) :=
    isAffineOpen_finset_biInf hA
  let e := fun (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) => cechHEquivCoh ℤ hc hsep F n
  have hO : ∀ s : Finset ι, cechOpen ⊤ U s = inter U s := fun s => by
    simp [cechOpen, inter, Finset.inf_eq_iInf]
  have hgen : ∀ s : Finset ι, genericPoint X ∈ cechOpen ⊤ U s := fun s => by
    rw [hO, ← SetLike.mem_coe, inter, Opens.coe_finset_inf]
    simp [hg]
  let φ : ∀ s : Finset ι, (cechCube ℤ F ⊤ U).obj s →+ V := fun s =>
    (hL.val (cechOpen ⊤ U s) (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).toAddMonoidHom
  have hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ s) := fun s _ =>
    (hL.inj _ (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).injective
  have hrange : ∀ s : Finset ι, s.Nonempty → (φ s).range = latSec M (inter U s) := by
    intro s _
    rw [← hO s, ← hL.range _ (hgen s)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨(sectionsOn.toΓ F (cechOpen ⊤ U s)).symm z,
        congrArg (hL.val _ (hgen s)) ((sectionsOn.toΓ F (cechOpen ⊤ U s)).apply_symm_apply z)⟩
  have hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty →
      ∀ x, φ t (Cube.res (cechCube ℤ F ⊤ U) h x) = φ s x := by
    intro s t h _ x
    show hL.val _ _ (sectionsOn.toΓ F _ (sectionsOn.res ℤ F (cechOpen_anti ⊤ U h) x)) =
      hL.val _ _ (sectionsOn.toΓ F _ x)
    exact hL.res (cechOpen ⊤ U s) (cechOpen ⊤ U t) (cechOpen_anti ⊤ U h) (hgen t)
      (sectionsOn.toΓ F _ x)
  obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
  have e' := e F (p + 1)
  rw [show Subsingleton (coh F (p + 1)) ↔ Subsingleton (cechH ℤ F ⊤ U (p + 1)) from
    ⟨fun h => haveI := h; e'.injective.subsingleton,
      fun h => haveI := h; e'.symm.injective.subsingleton⟩,
    ← ModuleCat.isZero_iff_subsingleton, cechH_def, cech_def,
    ← HomologicalComplex.exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]
  exact (LatCech.exact_iff_cechZero (φ := φ) (Nat.succ_pos p) hinj hrange hres).symm

end GlobalTheory
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.cech_lattice_cohomology_vanish : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules) [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F → (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b → (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  first | exact @_root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh | exact _root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh | (intros; apply _root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh <;> assumption)
end
