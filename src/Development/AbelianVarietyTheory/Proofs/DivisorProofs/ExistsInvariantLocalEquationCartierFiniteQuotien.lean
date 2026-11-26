module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinset
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.CommonEqnOpen

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_pow_mul_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) (t : Γ(X, U))
    (ht : genericPoint X ∈ X.basicOpen t) {f : X.functionField}
    (h : ∀ z ∈ X.basicOpen t, RegAt z f) :
    ∃ (n : ℕ) (a : Γ(X, U)), fnOf U hg t ^ n * f = fnOf U hg a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := hU.isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) =
      fnOf U hg c := fnOf_resG (X.basicOpen_le t) ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨W, hW, hgW⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htW, ht⟩ := hU.exists_basicOpen_le ⟨x, hW⟩ hxU
  obtain ⟨t', htV, ht'⟩ := hU.exists_basicOpen_le ⟨y, hV⟩ hyU
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n)) := by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n
  refine ⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩
  have := (regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt
  rw [← e] at this
  convert this using 1
  have h0 := hu.ne_zero
  rw [map_pow] at h0
  rw [map_mul, map_pow, map_pow, mul_pow]
  field_simp

theorem exists_vanishesAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U)
    (hxy : x ∉ closure ({y} : Set X)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hU hxU hg hyU
  obtain ⟨t, htU, ht⟩ := hU.exists_basicOpen_le
    (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU
  have hz : ZeroAt y (fnOf U (gen_mem hxU) t) := zeroAt_iff.2 ⟨regAt_fnOf hyU _ _,
    fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U →
    ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  intro X _ U hU D x hxU T hTU hT
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff hxU _ _).2 hs
  have key (y : X) (hyU : y ∈ U) (s t : Γ(X, U))
      (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf hyU (gen_mem hxU) t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simpa using hxU, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz))
      fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    have hyU := hTU y (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ hyU _ _ h'
    · exact key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)

end GlobalTheory.Cartier.CommonEqnOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinsetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierSection_generatesAt_vanishesAt_finset : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  first | exact @GlobalTheory.Cartier.CommonEqnOpen.exists_generatesAt_vanishesAt | exact GlobalTheory.Cartier.CommonEqnOpen.exists_generatesAt_vanishesAt | (intros; apply GlobalTheory.Cartier.CommonEqnOpen.exists_generatesAt_vanishesAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharIndepAt

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

def liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    X.presheaf.stalk x →+* X.presheaf.stalk x where
  toFun s := (h _ ⟨s, rfl⟩).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_one, map_one])
  map_mul' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_mul, map_mul, map_mul, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_zero, map_zero])
  map_add' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_add (f := _), map_add (f := _), map_add (f := _), (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])

theorem algebraMap_liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f))
    (s : X.presheaf.stalk x) :
    algebraMap _ X.functionField (liftStalk σ h s) = σ (algebraMap _ X.functionField s) :=
  (h _ ⟨s, rfl⟩).choose_spec

theorem residue_liftStalk_eq_iff (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp (liftStalk σ h) = IsLocalRing.residue (X.presheaf.stalk x) ↔
      ∀ f, RegAt x f → ZeroAt x (σ f - f) := by
  constructor
  · rintro e f ⟨s, rfl⟩
    refine ⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact RingHom.congr_fun e s
  · intro H
    ext s
    obtain ⟨m, hm, e⟩ := H _ ⟨s, rfl⟩
    have : m = liftStalk σ h s - s := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
      rw [e, map_sub, algebraMap_liftStalk])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    exact hm

end GlobalTheory.CharIndepAt


open GlobalTheory.CharIndepAt in
theorem GlobalTheory.CharIndepAt.main : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by

  intro X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6
  classical
  let R := X.presheaf.stalk x
  let res := IsLocalRing.residue R
  let g : Γ(X, U) →+* R := (X.presheaf.germ U x hx).hom
  let ψ : ι → (R →+* IsLocalRing.ResidueField R) := fun i => res.comp (liftStalk (σ i) (h1 i))
  let χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R) := fun i => ((ψ i).comp g : Γ(X, U) →+* _)
  let χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R := (res.comp g : Γ(X, U) →+* _)
  letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hext : ∀ i, χ i = χ₀ → ψ i = res := by
    intro i e
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_
    ext a
    exact DFunLike.congr_fun e a
  choose t ht using h3
  have hone : ∀ j, χ j = χ₀ → res (t j) = 1 := by
    intro j e
    obtain ⟨m, hm, em⟩ := h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))
    have : m = t j - 1 := IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  obtain ⟨i₀, hi₀⟩ := h6
  have h0 : χ i₀ = χ₀ := by
    have := (residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀
    ext a
    exact RingHom.congr_fun this (g a)
  by_contra hne
  push_neg at hne
  have hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0 := by
    intro a
    by_contra hz
    refine hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
      intro h
      apply hz
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_comm]
      rfl
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_liftStalk, ht]
      congr 2
      exact algebraMap_germ hx a
  have hli := linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)
  rw [linearIndependent_iff'] at hli
  let c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R :=
    fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)
  have hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0 := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hc := hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))
  have hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R) := by
    change ∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _
    rw [Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]
  have hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'
  obtain ⟨s, hs, es⟩ := h5 _ hn
  have : s = ((Finset.univ.filter fun i => χ i = χ₀).card : R) :=
    IsFractionRing.injective R X.functionField (by rw [es, map_natCast])
  subst this
  have := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs
  rw [map_natCast, ← hc'] at this
  exact this hc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAtStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by
  first | exact @GlobalTheory.CharIndepAt.main | exact GlobalTheory.CharIndepAt.main | (intros; apply GlobalTheory.CharIndepAt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotien
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : RegAt (φ x) f) :
    RegAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨φ.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

theorem zeroAt_map (φ : X ⟶ X) [IsDominant φ] {x : X} {f : X.functionField} (h : ZeroAt (φ x) f) :
    ZeroAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, map_nonunit (φ.stalkMap x).hom a ha,
    (GlobalTheory.functionFieldMap_algebraMap φ x a).symm⟩

theorem map_genericPoint (φ : X ⟶ X) [IsDominant φ] : φ (genericPoint X) = genericPoint X := by
  have := (genericPoint_spec X).image φ.continuous
  rw [Set.image_univ, φ.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec X)

theorem functionFieldMap_comp (φ ψ : X ⟶ X) [IsDominant φ] [IsDominant ψ] [IsDominant (φ ≫ ψ)]
    (f : X.functionField) :
    GlobalTheory.functionFieldMap (φ ≫ ψ) f = GlobalTheory.functionFieldMap φ (GlobalTheory.functionFieldMap ψ f) := by
  have hz : (φ ≫ ψ) (genericPoint X) = genericPoint X := map_genericPoint _
  have hr : RegAt (ψ (φ (genericPoint X))) f := by
    rw [show ψ (φ (genericPoint X)) = (φ ≫ ψ) (genericPoint X) from rfl, hz]
    exact regAt_genericPoint f
  obtain ⟨a, rfl⟩ := hr
  rw [GlobalTheory.functionFieldMap_algebraMap ψ, GlobalTheory.functionFieldMap_algebraMap φ]
  have := GlobalTheory.functionFieldMap_algebraMap (φ ≫ ψ) (genericPoint X) a
  refine this.trans ?_
  rw [Scheme.Hom.stalkMap_comp]
  rfl

theorem UnitAt.add_zeroAt {x : X} {f f' : X.functionField} (h : UnitAt x f) (h' : ZeroAt x f') :
    UnitAt x (f + f') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  refine ⟨a + b, ?_, map_add _ a b⟩
  by_contra hu
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact ((IsLocalRing.mem_maximalIdeal _).1 (by simpa using sub_mem h1 hb)) ha

variable {Γ : Type} [Group Γ]

def sig (ρ : Γ →* Aut X) (γ : Γ) : X.functionField →+* X.functionField :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  GlobalTheory.functionFieldMap (ρ γ).asIso.hom

theorem fnAct_val (ρ : Γ →* Aut X) (γ : Γ) (g : X.functionFieldˣ) :
    ((fnAct ρ γ g : X.functionFieldˣ) : X.functionField) = sig ρ γ g := rfl

theorem regAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : RegAt ((ρ γ).asIso.hom x) f) : RegAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  regAt_map _ h

theorem zeroAt_sig (ρ : Γ →* Aut X) (γ : Γ) {x : X} {f : X.functionField}
    (h : ZeroAt ((ρ γ).asIso.hom x) f) : ZeroAt x (sig ρ γ f) :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  zeroAt_map _ h

theorem sig_sig (ρ : Γ →* Aut X) (γ δ : Γ) (f : X.functionField) :
    sig ρ γ (sig ρ δ f) = sig ρ (δ * γ) f := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI : IsIso (ρ δ).asIso.hom := Iso.isIso_hom (ρ δ).asIso
  haveI : IsIso (ρ (δ * γ)).asIso.hom := Iso.isIso_hom (ρ (δ * γ)).asIso
  have e : (ρ (δ * γ)).asIso.hom = (ρ γ).asIso.hom ≫ (ρ δ).asIso.hom := by rw [map_mul]; rfl
  have key : ∀ (φ : X ⟶ X) (h : φ = (ρ γ).asIso.hom ≫ (ρ δ).asIso.hom) [IsDominant φ],
      GlobalTheory.functionFieldMap φ f = GlobalTheory.functionFieldMap (ρ γ).asIso.hom (GlobalTheory.functionFieldMap (ρ δ).asIso.hom f) := by
    intro φ h _
    subst h
    exact functionFieldMap_comp _ _ f
  exact (key _ e).symm

theorem sig_one (ρ : Γ →* Aut X) (f : X.functionField) : sig ρ 1 f = f := by
  have := sig_sig ρ 1 1 f
  rw [mul_one] at this
  exact (sig ρ 1).injective this

theorem eq_of_mem_closure [Finite Γ] (ρ : Γ →* Aut X) (γ : Γ) (x : X)
    (h : x ∈ closure ({(ρ γ).asIso.hom x} : Set X)) : (ρ γ).asIso.hom x = x := by
  set a : ℕ → X := fun k => (ρ (γ ^ k)).asIso.hom x with ha
  have hs : ∀ k, a (k + 1) = (ρ γ).asIso.hom (a k) := fun k => by
    simp only [ha, pow_succ', map_mul]; rfl
  have h0 : a 0 = x := by simp only [ha, pow_zero, map_one]; rfl
  have h1 : a 1 ⤳ a 0 := by
    rw [h0, hs, h0, specializes_iff_mem_closure]; exact h
  have hstep : ∀ k, a (k + 1) ⤳ a k := fun k => by
    induction k with
    | zero => exact h1
    | succ k ih =>
      have e := ih.map (ρ γ).asIso.hom.continuous
      rw [← hs, ← hs] at e
      exact e
  have hge : ∀ k, a (k + 1) ⤳ a 1 := fun k => by
    induction k with
    | zero => exact specializes_rfl
    | succ k ih => exact (hstep (k + 1)).trans ih
  have hn : 0 < orderOf γ := orderOf_pos γ
  have hx : a (orderOf γ) = x := by simp only [ha, pow_orderOf_eq_one, map_one]; rfl
  obtain ⟨m, hm⟩ : ∃ m, orderOf γ = m + 1 := ⟨orderOf γ - 1, by omega⟩
  have e1 : x ⤳ a 1 := by rw [← hx, hm]; exact hge m
  have e2 : a 1 ⤳ x := h0 ▸ h1
  have : a 1 = x := (e2.antisymm e1).eq
  calc (ρ γ).asIso.hom x = a 1 := by rw [hs 0, h0]
    _ = x := this

theorem exists_invariant_isEqn : ∀ (F : Type) [Field F] [CharZero F] (X W : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp F)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W), IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ γ x g, D.IsEqn ((ρ γ).asIso.hom x) g → D.IsEqn x (fnAct ρ γ g)) →
    (∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)) →
    ∀ x : X, ∃ g : X.functionFieldˣ, (∀ γ, fnAct ρ γ g = g) ∧ D.IsEqn x g := by
  intro F _ _ X W _ s Γ _ _ ρ q hq D hinv hin x
  classical
  haveI := Fintype.ofFinite Γ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  have := hq.isAffineHom
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hxU : x ∈ q ⁻¹ᵁ V := hxV
  have horb (γ : Γ) : (ρ γ).asIso.hom x ∈ q ⁻¹ᵁ V := by
    have e : q ((ρ γ).asIso.hom x) = q x := congr($(hq.comp_eq γ) x)
    show q _ ∈ V
    rw [e]; exact hxV
  let T : Finset X := Finset.univ.image fun γ : Γ => (ρ γ).asIso.hom x
  have hT (y : X) : y ∈ T ↔ ∃ γ, (ρ γ).asIso.hom x = y := by simp [T]
  obtain ⟨e₀, he₀, hv⟩ := GlobalTheory.T.exists_cartierSection_generatesAt_vanishesAt_finset X (q ⁻¹ᵁ V) hU D x hxU T
    (fun y hy => by obtain ⟨γ, rfl⟩ := (hT y).1 hy; exact horb γ)
    (fun y hy hne hc => by
      obtain ⟨γ, rfl⟩ := (hT y).1 hy
      exact hne (eq_of_mem_closure ρ γ x hc))
  have he0 : e₀ ≠ 0 := he₀.ne_zero
  set g : X.functionFieldˣ := (Units.mk0 e₀ he0)⁻¹ with hgdef
  have hgv : (g : X.functionField) = e₀⁻¹ := by simp [hgdef]
  have hg : D.IsEqn x g := CartierDiv.isEqn_iff_generatesAt_inv.2 (by rw [hgv, inv_inv]; exact he₀)

  have hgs (γ : Γ) (hγ : (ρ γ).asIso.hom x = x) : D.IsEqn x (fnAct ρ γ g) :=
    hinv γ x g (by rw [hγ]; exact hg)
  let ι := {γ : Γ // (ρ γ).asIso.hom x = x}
  let σ : ι → X.functionField →+* X.functionField := fun i => sig ρ i.1
  let u : ι → X.functionField := fun i => (g : X.functionField) / sig ρ i.1 g
  have hu (i : ι) : UnitAt x (u i) := by
    have := (hg.iff_unitAt.1 (hgs i.1 i.2)).inv
    rw [fnAct_val, inv_div] at this
    exact this
  have hnat (n : ℕ) (hn : n ≠ 0) : UnitAt x (n : X.functionField) := by
    let φF := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ s.appTop ≫ X.presheaf.germ ⊤ x trivial
    refine ⟨(n : X.presheaf.stalk x), ?_, map_natCast _ n⟩
    rw [← map_natCast φF.hom n]
    exact (IsUnit.mk0 (n : F) (Nat.cast_ne_zero.2 hn)).map _
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_affineFunction_weighted_translates_unitAt X (q ⁻¹ᵁ V) hU x hxU ι σ u
    (fun i f hf => regAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i f hf => zeroAt_sig ρ i.1 (by rw [i.2]; exact hf))
    (fun i => (hu i).regAt)
    (fun i hi => by
      have hfr : X.fromSpecResidueField x ≫ (ρ i.1).asIso.hom = X.fromSpecResidueField x := by
        haveI : IsIso (ρ i.1).asIso.hom := Iso.isIso_hom (ρ i.1).asIso
        set φ := (ρ i.1).asIso.hom
        have key : (X.residueFieldCongr i.2.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
          rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
            Scheme.residue_residueFieldMap]
          ext a
          change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq i.2.symm)).hom a)) =
            IsLocalRing.residue _ a
          set b := (X.presheaf.stalkCongr (.of_eq i.2.symm)).hom a with hb
          change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
          rw [Ideal.Quotient.eq]
          by_cases ha : a = 0
          · rw [hb, ha, map_zero, map_zero, sub_zero]
            exact zero_mem _
          · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
              (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
            obtain ⟨c, hc, e⟩ := hi (Units.mk0 _ hne) ⟨a, rfl⟩
            have e2 : σ i (Units.mk0 _ hne) =
                GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
            have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
                algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
              have hc' : ∀ {y z : X} (h : y = z) (d : X.presheaf.stalk y),
                  algebraMap (X.presheaf.stalk z) X.functionField
                    ((X.presheaf.stalkCongr (.of_eq h)).hom d) =
                    algebraMap (X.presheaf.stalk y) X.functionField d := by
                intro y z h d
                subst h
                simp
              have hc : algebraMap (X.presheaf.stalk ((ρ i.1).asIso.hom x)) X.functionField b =
                  algebraMap (X.presheaf.stalk x) X.functionField a := by
                rw [hb]
                exact hc' i.2.symm a
              rw [← hc]
              exact GlobalTheory.functionFieldMap_algebraMap φ x b
            rw [e2, Units.val_mk0, e4, ← map_sub] at e
            rwa [← IsFractionRing.injective _ _ e]
        rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
          ← X.residueFieldCongr_fromSpecResidueField i.2.symm, ← Category.assoc, ← Spec.map_comp, key,
          Spec.map_id, Category.id_comp]
      have h1 := hin i.1 x g hfr hg
      rw [Units.val_mul, fnAct_val, Units.val_inv_eq_inv_val g] at h1
      have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
      have hg0 : (g : X.functionField) ≠ 0 := Units.ne_zero _
      have e : u i - 1 = (sig ρ i.1 g * (g : X.functionField)⁻¹ - 1) * ((-1) * u i) := by
        simp only [u]; field_simp; ring
      rw [e]
      exact h1.mul (RegAt.mul (⟨-1, by rw [map_neg, map_one]⟩ : RegAt x (-1)) (hu i).regAt))
    hnat
    ⟨⟨1, by rw [map_one]; rfl⟩, fun f _ => by
      simp only [σ, sig_one, sub_self]; exact zeroAt_zero x⟩
  set af := fnOf (q ⁻¹ᵁ V) (gen_mem hxU) a with haf
  set h : X.functionField := ∑ γ : Γ, sig ρ γ (af * e₀) with hh

  have hinvh (δ : Γ) : sig ρ δ h = h := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hh, map_sum]
    simp only [sig_sig]
    exact Equiv.sum_comp (Equiv.mulRight δ) (fun γ => sig ρ γ (af * e₀))

  have hsplit : h * g = ∑ i : ι, σ i af * u i +
      ∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).asIso.hom x = x), sig ρ γ (af * e₀) * g := by
    rw [hh, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun γ : Γ => (ρ γ).asIso.hom x = x)]
    congr 1
    rw [Finset.sum_subtype (p := fun γ : Γ => (ρ γ).asIso.hom x = x) _ (fun γ => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs0 : sig ρ i.1 g ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    simp only [σ, u, map_mul, hgv, map_inv₀]
    rw [← hgv]
    field_simp
  have hrest : ZeroAt x (∑ γ ∈ Finset.univ.filter (fun γ : Γ => ¬ (ρ γ).asIso.hom x = x),
      sig ρ γ (af * e₀) * g) := by
    refine Finset.sum_induction _ (ZeroAt x) (fun _ _ h h' => h.add h') (zeroAt_zero x)
      fun γ hγ => ?_
    have hne : (ρ γ).asIso.hom x ≠ x := (Finset.mem_filter.1 hγ).2
    obtain ⟨g', hg', hz⟩ := hv _ ((hT _).2 ⟨γ, rfl⟩) hne
    have hz' : ZeroAt ((ρ γ).asIso.hom x) (af * e₀ * g') := by
      have e : af * e₀ * g' = e₀ * g' * af := by ring
      rw [e]
      exact hz.mul (regAt_fnOf (horb γ) _ a)
    have h2 := zeroAt_sig ρ γ hz'
    have h3 : UnitAt x ((g : X.functionField) / fnAct ρ γ g') :=
      (hinv γ x g' hg').iff_unitAt.1 hg
    rw [fnAct_val] at h3
    have hs0 : sig ρ γ g' ≠ 0 := by rw [← fnAct_val]; exact Units.ne_zero _
    have e : sig ρ γ (af * e₀) * g = sig ρ γ (af * e₀ * g') * ((g : X.functionField) / sig ρ γ g') := by
      rw [map_mul (sig ρ γ) (af * e₀)]; field_simp
    rw [e]
    exact h2.mul h3.regAt
  have hunit : UnitAt x (h * g) := by
    rw [hsplit]; exact UnitAt.add_zeroAt ha hrest
  have hh0 : h ≠ 0 := fun e => by
    have := hunit.ne_zero; rw [e, zero_mul] at this; exact this rfl
  refine ⟨(Units.mk0 h hh0)⁻¹, fun δ => ?_, ?_⟩
  · rw [map_inv]
    congr 1
    ext
    rw [fnAct_val, Units.val_mk0, hinvh]
  · rw [CartierDiv.isEqn_iff_generatesAt_inv, Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
    exact hg.generatesAt_iff.2 hunit

end GlobalTheory.InvEqn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotienStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient : ∀ (F : Type) [Field F] [CharZero F] (X W : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp F)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W), IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ γ x g, D.IsEqn ((ρ γ).asIso.hom x) g → D.IsEqn x (fnAct ρ γ g)) →
    (∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)) →
    ∀ x : X, ∃ g : X.functionFieldˣ, (∀ γ, fnAct ρ γ g = g) ∧ D.IsEqn x g := by
  first | exact @GlobalTheory.InvEqn.exists_invariant_isEqn | exact GlobalTheory.InvEqn.exists_invariant_isEqn | (intros; apply GlobalTheory.InvEqn.exists_invariant_isEqn <;> assumption)
end
