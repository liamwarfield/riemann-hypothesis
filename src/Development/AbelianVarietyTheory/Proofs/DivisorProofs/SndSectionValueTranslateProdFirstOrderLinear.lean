module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSLin

theorem valR_eq_evAt {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR x U f = GlobalTheory.TanDeriv.evAt x U h f := dif_pos h

theorem valR_spMap_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (x : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  rw [valR_eq_evAt x U h, valR_eq_evAt _ U (GlobalTheory.TanDeriv.comp_top_le φ x U h)]
  exact GlobalTheory.TanDeriv.evAt_comp φ x U h _ f

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem top_le_of_fst (z : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left) ⁻¹ᵁ O) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine GlobalTheory.TanDeriv.top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ O h
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]

theorem fst_comp_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (z : overAt x0 (DualNumber S) ⟶ G)
    (hz : smT x0 0 z = g') : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left = g₀ := by
  have h1 : (smT x0 0 z).left = spMap (epsMul 0) ≫ z.left := rfl
  have h2 := congrArg (fun φ => spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ φ) (hz ▸ h1)
  rw [hg, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap] at h2
  have e1 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext; simp
  have e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul (0 : S)) =
      (TrivSqZeroExt.fstHom S S S).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  rw [e1, e2] at h2
  rw [← h2]
  simp [spMap]

theorem smT_const (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (a : S) : smT x0 a g' = g' := by
  apply Over.OverMorphism.ext
  have h1 : (smT x0 a g').left = spMap (epsMul a) ≫ g'.left := rfl
  rw [h1, hg, ← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun x => by simp [epsMul]

theorem valR_smT (a : S) (w : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (hw : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from w.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (smT x0 a w).left O f).snd = a * (valR w.left O f).snd := by
  have h1 : (smT x0 a w).left = spMap (epsMul a) ≫ w.left := rfl
  rw [h1, valR_spMap_comp _ _ O hw f]
  simp [epsMul]

theorem valR_const_snd (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : (valR g'.left O f).snd = 0 := by
  rw [hg, valR_spMap_comp _ _ O hO f]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_valR_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hv0 : smT x0 0 v = 1) (O : G.left.Opens)
    (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (u * v).left O f).snd = (valR u.left O f).snd + (valR (smT x0 0 u * v).left O f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = smT x0 0 u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    rfl
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left =
      (smT x0 0 u * v).left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ O := by
    refine GlobalTheory.TanDeriv.top_le_of_comp
      (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ O ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  have k1 := valR_spMap_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k2 := valR_spMap_comp (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k3 := valR_spMap_comp (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  rw [f1] at k1
  rw [f2] at k2
  rw [f3] at k3
  rw [k1, k2, k3]
  simp

theorem top_le_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (z : overAt x0 (DualNumber S) ⟶ G) (hz : smT x0 0 z = g') :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine top_le_of_fst z O ?_
  rw [fst_comp_of_smT_zero g₀ g' hg z hz]
  exact hO

theorem snd_sectionValue_translate_list_prod_induction (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : ∀ (m : ℕ) (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S),
    (∀ c, smT x0 0 (y c) = 1) →
    smT x0 0 (List.ofFn fun c => smT x0 (r c) (y c)).prod = 1 ∧
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  have hg0 : smT x0 0 g' = g' := smT_const g₀ g' hg 0
  intro m
  induction m with
  | zero =>
    intro y r _
    rw [List.ofFn_zero, List.prod_nil, smT_one', _root_.mul_one, valR_const_snd g₀ g' hg O hO f]
    simp
  | succ n ih =>
    intro y r hy
    obtain ⟨h0, hs⟩ := ih (fun c => y c.succ) (fun c => r c.succ) (fun c => hy c.succ)
    have ha : smT x0 0 (smT x0 (r 0) (y 0)) = 1 := by rw [smT_smT, zero_mul, hy 0]
    rw [List.ofFn_succ, List.prod_cons]
    refine ⟨by rw [smT_mul, ha, h0, _root_.mul_one], ?_⟩
    have hu : smT x0 0 (g' * smT x0 (r 0) (y 0)) = g' := by rw [smT_mul, hg0, ha, _root_.mul_one]
    have hy0 : smT x0 0 (g' * y 0) = g' := by rw [smT_mul, hg0, hy 0, _root_.mul_one]
    have hgy : g' * smT x0 (r 0) (y 0) = smT x0 (r 0) (g' * y 0) := by
      rw [smT_mul, smT_const g₀ g' hg]
    rw [← _root_.mul_assoc, snd_valR_mul _ _ h0 O (top_le_of_smT_zero g₀ g' hg O hO _ hu) f, hu, hs, hgy,
      valR_smT _ _ O (top_le_of_smT_zero g₀ g' hg O hO _ hy0) f, Fin.sum_univ_succ]

theorem snd_valR_translate_prod : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  intro X0 S _ x0 G _ g₀ g' hg m y r hy O f hO
  exact (snd_sectionValue_translate_list_prod_induction g₀ g' hg O hO f m y r hy).2

end GlobalTheory.KSLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinearStatement
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  first | exact @GlobalTheory.KSLin.snd_valR_translate_prod | exact GlobalTheory.KSLin.snd_valR_translate_prod | (intros; apply GlobalTheory.KSLin.snd_valR_translate_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrime
namespace GlobalTheory.Desc

open scoped TensorProduct

theorem finiteType_away_of_pow_mul_mem {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by
  classical
  let φ := IsScalarTower.toAlgHom R C (Localization.Away x)
  let u : Localization.Away x := IsLocalization.Away.invSelf x
  have hu : φ x * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨⟨insert u (s.image φ), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  have hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) :=
    Algebra.subset_adjoin (by simp)
  have hB : ∀ b ∈ Algebra.adjoin R (s : Set C),
      φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) := by
    intro b hb
    have : φ b ∈ (Algebra.adjoin R (s : Set C)).map φ := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_mono ?_ this
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_image]
    exact Or.inr hz
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x y
  obtain ⟨n, hn⟩ := h c
  have hc' : y * φ x ^ m = φ c := hc
  have : y = φ (x ^ n * c) * u ^ (n + m) := by
    rw [map_mul, map_pow, ← hc']
    calc y = y * (φ x * u) ^ (n + m) := by rw [hu]; simp
      _ = _ := by ring
  rw [this]
  exact mul_mem (hB _ hn) (pow_mem hU _)

theorem exists_pow_mul_mem_of_finiteType_away {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  set x := algebraMap R C f with hx
  let φ := algebraMap C (Localization.Away x)
  obtain ⟨t, ht⟩ := h.out
  choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y
  refine ⟨t.image a, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB
  have hxB : x ∈ B := B.algebraMap_mem f
  have key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)),
      ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩
    | algebraMap r =>
      exact ⟨0, algebraMap R C r, B.algebraMap_mem r, by
        rw [pow_zero, mul_one]; exact IsScalarTower.algebraMap_apply R C _ r⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * x ^ k + d * x ^ n,
        add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e, ← e']
      ring
    | mul y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e']
      ring
  obtain ⟨n, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_pow, ← map_mul] at e
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x e
  refine ⟨k + n, ?_⟩
  have : x ^ (k + n) * c = x ^ k * b := by rw [← hk]; ring
  rw [this]
  exact mul_mem (pow_mem hxB _) hb

theorem exists_smul_mem_of_finiteType_tensor {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (M : Submonoid R) (h : Algebra.FiniteType (Localization M) (Localization M ⊗[R] C)) :
    ∃ s : Finset C, ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  let φ : C →ₐ[R] Localization M ⊗[R] C := Algebra.TensorProduct.includeRight
  have hloc : IsLocalizedModule M (TensorProduct.mk R (Localization M) C 1) :=
    (isLocalizedModule_iff_isBaseChange M (Localization M) _).2
      (TensorProduct.isBaseChange R C (Localization M))
  have hφ : ∀ c, TensorProduct.mk R (Localization M) C 1 c = φ c := fun _ => rfl
  obtain ⟨t, ht⟩ := h.out
  choose p hp using fun y => IsLocalizedModule.surj M (TensorProduct.mk R (Localization M) C 1) y
  refine ⟨t.image fun y => (p y).1, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image (fun y => (p y).1) : Finset C) : Set C) with hB
  have key : ∀ y ∈ Algebra.adjoin (Localization M) (t : Set (Localization M ⊗[R] C)),
      ∃ r ∈ M, ∃ b ∈ B, r • y = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨(p y).2, (p y).2.2, (p y).1, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), hp y⟩
    | algebraMap q =>
      obtain ⟨⟨a, r⟩, e⟩ := IsLocalization.surj M q
      refine ⟨r, r.2, algebraMap R C a, B.algebraMap_mem a, ?_⟩
      rw [φ.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization M),
        IsScalarTower.algebraMap_apply R (Localization M) _ a, ← map_mul, mul_comm]
      exact congrArg _ e
    | add y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, k • b + n • d,
        add_mem (B.smul_mem hb _) (B.smul_mem hd _), ?_⟩
      rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm k n]
    | mul y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e', smul_mul_smul_comm]
  obtain ⟨r, hr, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_smul, ← hφ, ← hφ] at e
  obtain ⟨k, hk⟩ := IsLocalizedModule.exists_of_eq (S := M) e
  refine ⟨k * r, mul_mem k.2 hr, ?_⟩
  have : algebraMap R C (k * r) * c = (k : R) • b := by
    rw [← Algebra.smul_def, mul_smul]; exact hk
  rw [this]
  exact B.smul_mem hb _

theorem exists_mul_mem_of_mul_mem {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by
  classical
  let J : Ideal B := (Ideal.span {x}).comap B.val
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  choose r hrM hr using h
  have hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c := by
    intro b
    by_cases hb : b ∈ J
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
      exact ⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose q hq using hJ
  refine ⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩
  set g := ∏ b ∈ t, r (q b) with hg
  have key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩
      rw [hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]
      exact mul_mem (B.algebraMap_mem _) (hr _)
    | zero => exact ⟨0, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, e, hc⟩ := hy
      obtain ⟨d, e', hd⟩ := hz
      exact ⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩
    | smul a y _ hy =>
      obtain ⟨c, e, hc⟩ := hy
      refine ⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩
      rw [mul_left_comm]
      exact mul_mem a.2 hc
  intro c hc
  obtain ⟨d, e, hd⟩ := key ⟨x * c, hc⟩ (by
    rw [ht]
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
  rw [mul_left_cancel₀ hx e]
  exact hd

theorem exists_finiteType_away_of_atPrime (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_pow_mul_mem_of_finiteType_away f h₁
  obtain ⟨s₂, hs₂⟩ := exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂
  let B := Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)
  have hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have : IsNoetherianRing B := isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩
  obtain ⟨g, hg, hgB⟩ := exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c =>
    (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩
  refine ⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩
  have key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, mul_assoc] at hc
      have h := ih _ hc
      rw [mul_left_comm] at h
      rw [pow_succ', mul_assoc]
      exact hgB _ h
  obtain ⟨n, hn⟩ := hs₁ c
  exact ⟨n, key n c (hB₁ hn)⟩

end GlobalTheory.Desc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime : ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime], algebraMap R C f ≠ 0 → Algebra.FiniteType R (Localization.Away (algebraMap R C f)) → Algebra.FiniteType (Localization.AtPrime 𝔭) (TensorProduct R (Localization.AtPrime 𝔭) C) → ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  first | exact @GlobalTheory.Desc.exists_finiteType_away_of_atPrime | exact GlobalTheory.Desc.exists_finiteType_away_of_atPrime | (intros; apply GlobalTheory.Desc.exists_finiteType_away_of_atPrime <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualApprox

variable (R : Type) [CommRing R]

abbrev spO (C : Type) [CommRing C] [Algebra R C] : Over (Sp R) := Over.mk (spMap (algebraMap R C))

variable {R}

def spOMap {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    spO R C' ⟶ spO R C :=
  Over.homMk (spMap f.toRingHom) (Spread.spMap_algHom_comp f)

@[simp]
theorem spOMap_left {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    (spOMap f).left = spMap f.toRingHom := rfl

theorem spOMap_comp {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] [Algebra R C] [Algebra R C']
    [Algebra R C''] (f : C →ₐ[R] C') (g : C' →ₐ[R] C'') : spOMap g ≫ spOMap f = spOMap (g.comp f) := by
  ext1
  simp only [Over.comp_left, spOMap_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (R) (C : Type) [CommRing C] [Algebra R C]

abbrev stage (s : Finset C) : Over (Sp R) := spO R (Algebra.adjoin R (s : Set C))

def toStage (s : Finset C) : spO R C ⟶ stage R C s := spOMap (Algebra.adjoin R (s : Set C)).val

variable {R C}

def stageMap {s t : Finset C} (h : s ⊆ t) : stage R C t ⟶ stage R C s :=
  spOMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h)))

theorem toStage_stageMap {s t : Finset C} (h : s ⊆ t) : toStage R C t ≫ stageMap h = toStage R C s := by
  rw [toStage, stageMap, spOMap_comp, toStage]
  rfl

theorem whiskerLeft_toStage_left (X : Over (Sp R)) (s : Finset C) :
    (X ◁ toStage R C s).left = Spread.bcMap X.hom (Algebra.adjoin R (s : Set C)).val :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

theorem whiskerLeft_stageMap_left (X : Over (Sp R)) {s t : Finset C} (h : s ⊆ t) :
    (X ◁ stageMap h).left = Spread.bcMap X.hom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))) :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

instance (s : Finset C) : IsAffine (stage R C s).left := by
  dsimp; infer_instance

theorem locallyOfFiniteType_stage (s : Finset C) : LocallyOfFiniteType (stage R C s).hom := by
  dsimp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  show RingHom.FiniteType (algebraMap R (Algebra.adjoin R (s : Set C)))
  rw [RingHom.finiteType_algebraMap, ← Subalgebra.fg_iff_finiteType]
  exact Subalgebra.fg_adjoin_finset s


open GlobalTheory.CechPic in
theorem exists_lb_stage (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (N : LB (X ⊗ spO R C).left) (hN : N.IsLB) :
    ∃ (s : Finset C) (M : LB (X ⊗ stage R C s).left), M.IsLB ∧ LBIso N (M.pull (X ◁ toStage R C s).left) := by
  classical
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  obtain ⟨s, M, hM, hiso, -⟩ := LBLimit.exists_lb_of_isLimit _ ρ w hc N hN
  refine ⟨s.unop, M, hM, ?_⟩
  rw [whiskerLeft_toStage_left]
  exact hiso


open GlobalTheory.CechPic in
theorem exists_stage_pull_eq (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (s : Finset C) (c c' : Pic (X ⊗ stage R C s).left)
    (h : CechPic.pull (X ◁ toStage R C s).left c = CechPic.pull (X ◁ toStage R C s).left c') :
    ∃ (t : Finset C) (hst : s ⊆ t),
      CechPic.pull (X ◁ stageMap hst).left c = CechPic.pull (X ◁ stageMap hst).left c' := by
  classical
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  have h' : LBIso (L.pull (X ◁ toStage R C s).left) (L'.pull (X ◁ toStage R C s).left) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).1 h
  rw [whiskerLeft_toStage_left] at h'
  have e : LBIso (L.pull (ρ (.op s))) (L'.pull (ρ (.op s))) := h'
  obtain ⟨j, f, hf⟩ := exists_lbIso_of_isLimit _ ρ w hc (i := .op s) L L' hL hL' e
  refine ⟨j.unop, f.unop.le, ?_⟩
  rw [whiskerLeft_stageMap_left]
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 hf

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

variable {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C]

theorem whiskerLeft_eq_lift' {X Y Z : Over (Sp R)} (g : Y ⟶ Z) : X ◁ g = lift (fst X Y) (snd X Y ≫ g) := by
  ext1 <;> simp

theorem exists_fam_stage (A : Over (Sp R)) [GrpObj A] [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (N : LB (A ⊗ spO R C).left) (hF : Fam A N) :
    ∃ (t : Finset C) (N₀ : LB (A ⊗ stage R C t).left), Fam A N₀ ∧ Same A N N₀ (𝟙 _) (toStage R C t) := by
  classical
  have hN := hF.isLB
  obtain ⟨s, M, hM, hiso⟩ := exists_lb_stage A N hN
  have H1 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R C), evc hN x y = evc hM x (y ≫ toStage R C s) := by
    intro Y x y
    have e : cls N hN = cls _ (pull_isLB hM (A ◁ toStage R C s).left) := (cls_eq_iff hN (pull_isLB hM _)).2 hiso
    have e2 : cls _ (pull_isLB hM (A ◁ toStage R C s).left) = evc hM (fst A _) (snd A _ ≫ toStage R C s) := by
      rw [whiskerLeft_eq_lift']; rfl
    rw [evc, e, e2, pull_evc, lift_fst, lift_snd_assoc]
  have : QuasiCompact (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have : QuasiSeparated (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  let D : ∀ U : Over (Sp R), (M : LB (A ⊗ U).left) → M.IsLB → Pic ((A ⊗ A) ⊗ U).left := fun U M hM =>
    evc hM (fst (A ⊗ A) U ≫ fst A A * fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U) -
      evc hM (fst (A ⊗ A) U ≫ fst A A) (snd (A ⊗ A) U) - evc hM (fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U)
  have hD : CechPic.pull ((A ⊗ A) ◁ toStage R C s).left (D _ M hM) = CechPic.pull ((A ⊗ A) ◁ toStage R C s).left 0 := by
    rw [map_zero]
    simp only [D, map_sub, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst, whiskerLeft_snd]
    rw [← H1, ← H1, ← H1, (isAdditive_iff hN).1 hF.add]
    abel
  obtain ⟨t, hst, ht⟩ := exists_stage_pull_eq (A ⊗ A) s _ _ hD
  rw [map_zero] at ht
  let N₀ : LB (A ⊗ stage R C t).left := ev M (fst A _) (snd A _ ≫ stageMap hst)
  have hN₀ : N₀.IsLB := pull_isLB hM _
  have H2 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ stage R C t), evc hN₀ x y = evc hM x (y ≫ stageMap hst) := by
    intro Y x y
    rw [evc_ev hM, lift_fst, lift_snd_assoc]
  refine ⟨t, N₀, ⟨hN₀, (isAdditive_iff hN₀).2 fun Y a a' y => ?_⟩, ?_⟩
  · rw [H2, H2, H2]
    have e := congrArg (CechPic.pull (lift (lift a a') y).left) ht
    simp only [D, map_sub, map_zero, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd] at e
    simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc] at e
    rw [sub_sub, sub_eq_zero] at e
    exact e
  · rw [same_iff hN hN₀, H2, Category.assoc, toStage_stageMap, ← H1, Category.comp_id]

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

theorem exists_fam_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  intro R _ _ A _ hA T _ N hF
  have : IsProper A.hom := hA.proper
  letI : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom.toAlgebra
  let e : T ≅ spO R Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom) = T.hom
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    simp only [Scheme.isoSpec, asIso_hom]
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])
  have hN := hF.isLB
  let N' : LB (A ⊗ spO R Γ(T.left, ⊤)).left := ev N (fst A _) (snd A _ ≫ e.inv)
  have hN' : N'.IsLB := pull_isLB hN _
  have H : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R Γ(T.left, ⊤)),
      evc hN' x y = evc hN x (y ≫ e.inv) := by
    intro Y x y
    rw [evc_ev hN, lift_fst, lift_snd_assoc]
  have hF' : Fam A N' := ⟨hN', (isAdditive_iff hN').2 fun Y a a' y => by
    rw [H, H, H]
    exact (isAdditive_iff hN).1 hF.add _ _ _ _⟩
  obtain ⟨t, N₀, h₀, hs⟩ := exists_fam_stage A N' hF'
  refine ⟨stage R _ t, e.hom ≫ toStage R _ t, N₀, inferInstance, locallyOfFiniteType_stage t, h₀, ?_⟩
  rw [same_iff hN' h₀.isLB] at hs
  rw [same_iff hN h₀.isLB]
  have k := congrArg (CechPic.pull (A ◁ e.hom).left) hs
  rw [pull_evc, pull_evc, whiskerLeft_fst, ← Category.assoc, whiskerLeft_snd, Category.comp_id, H,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Category.assoc, whiskerLeft_snd,
    Category.assoc] at k
  rw [Category.comp_id]
  exact k

end GlobalTheory.DualApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_additiveLineBundleFamily_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  first | exact @GlobalTheory.DualApprox.exists_fam_finiteType | exact GlobalTheory.DualApprox.exists_fam_finiteType | (intros; apply GlobalTheory.DualApprox.exists_fam_finiteType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineChar
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

namespace GlobalTheory.GenFracChart

theorem isFractionRing_and_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens)
    (hUV : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (hρ : spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι) :
    (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧
      ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  set V := barComp TF.Y Z
  set W : (X₀ TF.Y Z).Opens := V.ι ⁻¹ᵁ U.1 with hWdef
  have hU : IsAffineOpen U.1 := U.2
  have hWU : V.ι ''ᵁ W = U.1 := by
    rw [hWdef, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUV
  have hW : IsAffineOpen W := by
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, hWU]; exact hU
  have hch : LogKS.chart U = hU.fromSpec := rfl
  have hcomp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g) x = g (f x) := fun _ _ _ => rfl
  have hη : genericPoint (X₀ TF.Y Z) ∈ W := by
    obtain ⟨p⟩ : Nonempty (Sp (X₀ TF.Y Z).functionField) := inferInstance
    have h1 : (spMap ρ ≫ LogKS.chart U) p ∈ U.1 := by
      rw [hcomp, hch]; show _ ∈ (U.1 : Set TF.Y.X); rw [← hU.range_fromSpec]; exact Set.mem_range_self _
    rw [hρ, hcomp] at h1
    exact GlobalTheory.Cartier.gen_mem (x := GlobalTheory.LogKSDiv.genPt TF Z p) h1
  set σ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField :=
    ((X₀ TF.Y Z).presheaf.germ W _ hη).hom.comp (V.ι.appLE U.1 W le_rfl).hom with hσ
  have key : spMap ρ ≫ hU.fromSpec = spMap σ ≫ hU.fromSpec := by
    rw [← hch, hρ, GlobalTheory.LogKSDiv.genPt, ← hW.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec V.ι hU hW le_rfl, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hρe : ρ = σ := by
    have := Spec.map_injective ((cancel_mono hU.fromSpec).1 key)
    exact congrArg CommRingCat.Hom.hom this
  subst hρe
  haveI : Nonempty W := ⟨⟨_, hη⟩⟩
  have hle : U.1 ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hUV
  haveI : IsIso (V.ι.app U.1) := Scheme.Hom.isIso_app V.ι U.1 hle
  have hFr : IsFractionRing Γ(X₀ TF.Y Z, W) (X₀ TF.Y Z).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ W hW
  refine ⟨?_, ?_⟩
  · letI := σ.toAlgebra
    exact IsFractionRing.of_ringEquiv_left (asIso (V.ι.app U.1)).commRingCatIsoToRingEquiv (fun x => by
      show σ x = _
      simp only [σ, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
      rfl)
  · intro a
    rw [← GlobalTheory.Cartier.fnOf_comp_algX (s₀ TF.Y Z) W hη]
    simp only [σ, RingHom.comp_apply]
    congr 1
    show ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ TF.Y.s.appLE ⊤ U.1 (fun _ _ => trivial) ≫
      V.ι.appLE U.1 W le_rfl).hom a = _
    have e := Scheme.Hom.appLE_comp_appLE V.ι TF.Y.s ⊤ U.1 W (fun _ _ => trivial) le_rfl
    erw [e]
    rfl

end GlobalTheory.GenFracChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineCharStatement
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
theorem _root_.GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧ ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  first | exact @GlobalTheory.GenFracChart.isFractionRing_and_const | exact GlobalTheory.GenFracChart.isFractionRing_and_const | (intros; apply GlobalTheory.GenFracChart.isFractionRing_and_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrame
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

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add (f := _), map_add (f := _)]) (fun x y => by
      rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerGenericEigenFrameStatement
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
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_genericEigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  first | exact @GlobalTheory.LogKSDiv.GenKSProof.exists_genKS | exact GlobalTheory.LogKSDiv.GenKSProof.exists_genKS | (intros; apply GlobalTheory.LogKSDiv.GenKSProof.exists_genKS <;> assumption)
end
end
