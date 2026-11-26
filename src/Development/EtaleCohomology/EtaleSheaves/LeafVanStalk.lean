module

public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafVan0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) : pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s :=
  pullback.fst _ _

def LeafVanStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
    Subsingleton (Hrel (ZMod q) (sch.map (prS p ι (t ≫ U.hom))) (tw q i) m)) →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafVanW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → (∃ x : Sp A, (∀ z : Sp A, z ⤳ x) ∧ s x ∈ Set.range ι) →
  ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafVanV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y S : Scheme.{0}} (ι : W ⟶ B) (p : Y ⟶ B) (s : S ⟶ B),
  (∀ x : S, s x ∉ Set.range ι) → ∀ m : ℤ, Subsingleton (Ht q (sch.obj (pullback p s)) m i) →
  Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

theorem LeafVan0_of (hS : LeafVanStalk) (hW : LeafVanW) (hV : LeafVanV) : LeafVan0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV' p g1 g2 hp _ _ hSHV U m hm y
  refine hS hH q k hq i b ι p hp U m ?_ y
  intro A _ t hA
  obtain ⟨hHen, _⟩ := hA
  by_cases hx : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ Set.range ι
  · exact hW hH q k hq i b ι p hp A (t ≫ U.hom) ⟨hHen, ‹_›⟩
      ⟨IsLocalRing.closedPoint A, fun z => IsLocalRing.specializes_closedPoint z, hx⟩ m
  · have hall : ∀ z : Sp A, (t ≫ U.hom) z ∈ (V : Set B) := by
      intro z
      have hz : (t ≫ U.hom) z ⤳ (t ≫ U.hom) (IsLocalRing.closedPoint A) :=
        (IsLocalRing.specializes_closedPoint z).map (t ≫ U.hom).continuous
      have hxV : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ (V : Set B) := by rw [hV']; exact hx
      exact hz.mem_open V.isOpen hxV
    have hrange : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) := by rintro _ ⟨z, rfl⟩; exact hall z
    have hmiss : ∀ z : Sp A, (t ≫ U.hom) z ∉ Set.range ι := by
      intro z hz; have := hall z; rw [hV'] at this; exact this hz
    exact hV hH q i ι p (t ≫ U.hom) hmiss m ((hSHV A (t ≫ U.hom) ⟨hHen, ‹_›⟩ hrange).1 m (by omega))

end LateralTheory.E.LeafVan0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafVanBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev bpl (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prB ι U) (pullback.fst (t ≫ U.hom) ι)
    (pullback.map (t ≫ U.hom) ι U.hom ι t (𝟙 W) (𝟙 B) (by simp) (by simp)) t (pullback.lift_fst _ _ _).symm m

def LeafVanBStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  Cov U (fun _ a => rB q i ι a m c = 0)

def LeafRelVanOfH : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  Subsingleton (H R E F n) → Function.Surjective (pull R f F (n - 1)) → Subsingleton (Hrel R f F n)

theorem relVanOfH : LeafRelVanOfH := by
  intro R _ F U E f n hE hs
  suffices h : ∀ y : Hrel R f F n, y = 0 from ⟨fun y₁ y₂ => by rw [h y₁, h y₂]⟩
  intro y
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  set φ := (chains R).map f with hφ
  let a : Cocycle ((chains R).obj E) (res R F) n := zcomp (Cocycle.ofHom (mappingCone.inr φ)) z (zero_add n)
  have ha : CohomologyClass.mk a = 0 := hE.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha
  obtain ⟨α, hα⟩ := ha
  let b : Cochain ((chains R).obj U) (res R F) (n - 1) := (mappingCone.inl φ).comp z.1 (by omega)
  have hz : z.1 = mappingCone.descCochain φ b a.1 (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [b, a, zcomp, mappingCone.inl_descCochain, mappingCone.inr_descCochain]
  have h0 : δ n (n + 1) z.1 = 0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, mappingCone.δ_descCochain _ _ _ _ (n + 1) rfl] at h0
  have h1 := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) h0
  simp only [Cochain.comp_add, Cochain.comp_zero, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at h1
  have hδα : δ (n - 1) n α = a.1 := hα
  let b' : Cochain ((chains R).obj U) (res R F) (n - 1) :=
    b - n.negOnePow • (Cochain.ofHom φ).comp α (zero_add _)
  have hb' : δ (n - 1) n b' = 0 := by
    have e1 : δ (n - 1) n b = -((n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) := eq_neg_of_add_eq_zero_left h1
    simp only [b', δ_sub, δ_units_smul, e1, Int.negOnePow_succ]
    simp
    rw [hδα, sub_self]
  obtain ⟨g, hg⟩ := hs (CohomologyClass.mk (Cocycle.mk b' n (by omega) hb'))
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective g
  have hg' : CohomologyClass.mk (Cocycle.mk b' n (by omega) hb' - zcomp (Cocycle.ofHom φ) γ (zero_add _)) = 0 := by
    rw [CohomologyClass.mk_sub, ← hg]; exact sub_eq_zero.mpr rfl
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 2) (by omega)] at hg'
  obtain ⟨ε, hε⟩ := hg'
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨mappingCone.descCochain φ ε (α + n.negOnePow • γ.1) (by omega), ?_⟩
  have hε' : δ (n - 2) (n - 1) ε = b' - (Cochain.ofHom φ).comp γ.1 (zero_add _) := hε
  have hX : δ (n - 2) (n - 1) ε + n.negOnePow • (Cochain.ofHom φ).comp (α + n.negOnePow • γ.1) (zero_add _) = b := by
    rw [hε']
    simp only [b', Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    abel
  have hY : δ (n - 1) n (α + n.negOnePow • γ.1) = a.1 := by
    rw [δ_add, δ_units_smul, hδα, Cocycle.δ_eq_zero γ n, smul_zero, add_zero]
  rw [mappingCone.δ_descCochain _ _ _ _ n (by omega), hX, hY, hz]
  rfl

def LeafClosedSH : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  (∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)) ∧
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

def LeafClosedSHPos : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  ∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)

def LeafClosedSH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

theorem closedSH_of (h1 : LeafClosedSHPos) (h2 : LeafClosedSH0) : LeafClosedSH :=
  fun hy q _ i A _ _ hA hq _ ι' _ => ⟨h1 hy q i A hA hq ι', h2 hy q i A hA hq ι'⟩

theorem heightFunctionalStatement_of_pairingProperties (hy : Hyps) : B2 := hy.2.2.2.2.2.2.2.2.2.2.2.1

theorem vanBPt (hC : LeafClosedSH) (hy : Hyps) (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A]
    [IsLocalRing A] (hA : SH A) (hq : IsUnit (q : A)) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] (m : ℤ)
    (hm : 0 < m) : Subsingleton (Hrel (ZMod q) (sch.map ι') (tw q i) m) := by
  obtain ⟨hW, hs⟩ := hC hy q i A hA hq ι'
  refine relVanOfH (ZMod q) (tw q i) (sch.map ι') m (heightFunctionalStatement_of_pairingProperties hy (ZMod q) A hA (tw q i) m hm) ?_
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ m by omega) with h | h
  · subst h; simpa using hs
  · have := hW (m - 1) (by omega)
    intro y; exact ⟨0, Subsingleton.elim _ _⟩

theorem LeafVanB_of (hS : LeafVanBStalk) (hP : LeafClosedSHPos) (h0 : LeafClosedSH0) : LeafVanB := by
  have hC := closedSH_of hP h0
  intro hy q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 h1 h2 h3 hsh U m hm c
  exact hS hy q k hq i s ι U m c (fun A _ _ t hA hqA =>
    (vanBPt hC hy q i A hA hqA (pullback.fst (t ≫ U.hom) ι) m hm).elim _ _)

end LateralTheory.E.LeafVanBPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendChainPf

def PreChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) ∧
  (LocallyOfFinitePresentation (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ QuasiSeparated (d1 ≫ q)) ∧
  (LocallyOfFinitePresentation (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ QuasiSeparated (d2 ≫ d1 ≫ q)) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2

end LateralTheory.E.LeafDescendChainPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.NbIsoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.NbIsoPf

def FlatMonoLim : Prop := ∀ {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (ι : ∀ j, D.obj j ⟶ Y), (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) →
  (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) →
  ∀ {X : Scheme.{0}} (m : X ⟶ Y), Mono m → Flat m → QuasiCompact m → Set.range m = ⋂ j, Set.range (ι j) →
  ∀ c : Cone D, IsLimit c → Nonempty (c.pt ≅ X)

def SysFM : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
        Mono m ∧ Flat m ∧ QuasiCompact m ∧ Set.range m = ⋂ j, Set.range (ι j)

theorem NbIso_of (hS : SysFM) (hL : FlatMonoLim) : LateralTheory.E.SysPf.NbIso := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, m, hm, hf, hq, hr⟩ := hS W w hW y
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, fun c hc => ?_⟩
  exact hL D ι (fun j => ⟨(h1 j).1, (h1 j).2.1⟩) (fun f => (h2 f).1) m hm hf hq hr c hc

end LateralTheory.E.NbIsoPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSmoothOfNormalPf

def LeafStalkSmoothClosed : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω)
  [IsIntegral C], LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → ∀ y : C, y ≠ genericPoint C → (c.stalkMap y).hom.FormallySmooth

def LeafRelDimOne : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → Smooth c → topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem smooth_of_stalks (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [LocallyOfFiniteType c]
    (h : ∀ y : C, (c.stalkMap y).hom.FormallySmooth) : Smooth c := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact top_le_iff.mp fun y _ => h y

theorem stalk_smooth_all (hA : LeafStalkSmoothClosed) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hC : IsIntegral C) (hc : LocallyOfFiniteType c)
    (hn : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) (hd : topologicalKrullDim C = 1) (y : C) :
    (c.stalkMap y).hom.FormallySmooth := by
  by_cases hy : y = genericPoint C
  · subst hy
    exact c.genericPoint_mem_smoothLocus_of_perfectField
  · exact hA Ω c hc hn hd y hy

theorem LeafSmoothOfNormal_of (hA : LeafStalkSmoothClosed) (hB : LeafRelDimOne) :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hC hc hn hd
  have hs : Smooth c := smooth_of_stalks Ω c (stalk_smooth_all hA Ω c hC hc hn hd)
  exact hB Ω c hC hs hd

end LateralTheory.E.LeafSmoothOfNormalPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CovOfPoints
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSurj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_points {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop)
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), P U'' (b ≫ a)) : Cov U P := by
  choose Z f hx hP using h
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  · rintro U' a ⟨Y, b, g, ⟨j⟩, rfl⟩
    exact hP j U' b

def LeafSurj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y = 0

def LeafSurj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ V → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), ∃ c : Hrel (ZMod q) (sch.map (prB ι U'')) (tw q i) 0,
      bY q i (g2 ≫ g1 ≫ p) ι U'' 0 c = rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y

theorem LeafSurj0_of (hW : LeafSurj0W) (hV : LeafSurj0V) : LateralTheory.E.LeafDegCut.LeafSurj0 := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hVW p g1 g2 h0 h1 h2 hS U y
  refine cov_of_points U _ fun x => ?_
  by_cases hx : U.hom x ∈ V
  · exact hV hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hx
  · have hxW : U.hom x ∈ Set.range ι := by
      have : U.hom x ∉ (V : Set B) := hx
      rw [hVW] at this
      simpa using this
    obtain ⟨U', a, hxa, hz⟩ := hW hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hxW
    exact ⟨U', a, hxa, fun U'' b' => ⟨0, by rw [map_zero, hz U'' b']⟩⟩

end LateralTheory.E.LeafSurj0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafInj0Of
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_pts {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop}
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧
      Cov U' (fun U'' b => P U'' (b ≫ a))) : Cov U P := by
  choose U' a y hy hC using h
  choose T hT hP using hC
  let R : Sieve U :=
    { arrows := fun {Z} g => ∃ x, ∃ b : Z ⟶ U' x, T x b ∧ g = b ≫ a x
      downward_closed := by
        rintro Z W g ⟨x, b, hb, rfl⟩ h
        exact ⟨x, h ≫ b, (T x).downward_closed hb h, by simp⟩ }
  refine ⟨R, ?_, ?_⟩
  · have h0 : Sieve.ofArrows U' a ∈ (EtTop B) U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨z, y z, hy z⟩
    refine (EtTop B).transitive h0 R ?_
    intro Z f hf
    obtain ⟨W, g, f', hf', rfl⟩ := hf
    cases hf' with
    | mk x =>
      refine (EtTop B).superset_covering ?_ ((EtTop B).pullback_stable g (hT x))
      intro V c hc
      exact ⟨x, c ≫ g, hc, by simp⟩
  · rintro Z g ⟨x, b, hb, rfl⟩
    exact hP x Z b hb

def LeafInj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

def LeafInj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

theorem LeafInj0_of (hW : LeafInj0W) (hV : LeafInj0V) : LateralTheory.E.LeafDegCut.LeafInj0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp1 hp2 hp3 hS U c hc
  apply cov_of_pts
  intro x
  by_cases hx : U.hom x ∈ Set.range ι
  · exact hW hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c x hx
  · exact hV hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c hc x hx
end LateralTheory.E.LeafInj0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof

namespace LateralTheory.E.ChartsGeom_vpaPf

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def chartEquiv {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K)
    (hr : φ.range = B.toSubring) : Γ(Z, U) ≃+* B :=
  (RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hi (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr hr)

theorem chartEquiv_apply {Z : Scheme.{0}} {U : Z.Opens} (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) (s : Γ(Z, U)) : ((chartEquiv φ hi B hr s : B) : K) = φ s := rfl

def chartMap {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : Spec (CommRingCat.of B) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) ≫ hU.fromSpec

instance {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ)
    (B : Subalgebra A K) (hr : φ.range = B.toSubring) : IsOpenImmersion (chartMap hU φ hi B hr) := by
  unfold chartMap
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  infer_instance

theorem chartMap_range {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) :
    Set.range (chartMap hU φ hi B hr).base = (U : Set Z) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom) :=
      (RingEquiv.toCommRingCatIso (chartEquiv φ hi B hr)).isIso_hom
    infer_instance
  unfold chartMap
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  exact hU.range_fromSpec

theorem chartMap_comp {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {U : Z.Opens} (hU : IsAffineOpen U)
    (φ : Γ(Z, U) →+* K) (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring)
    (hA : ∀ a : A, φ (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) :
    chartMap hU φ hi B hr ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  have hp : p = Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hr2 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫
      CommRingCat.ofHom (chartEquiv φ hi B hr).toRingHom = CommRingCat.ofHom (algebraMap A B) := by
    ext a
    have := hA a
    simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply] at this
    simp [chartEquiv_apply]
    exact this
  rw [hp, chartMap, Category.assoc, ← Category.assoc hU.fromSpec, IsAffineOpen.fromSpec_toSpecΓ, ← Spec.map_comp,
    ← Spec.map_comp, ← hr2]
  simp only [Category.assoc]

def ChartData {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop :=
  ∃ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K),
    IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ ∧
    Function.Injective φU ∧ Function.Injective φV ∧ Function.Injective φW ∧
    φU.range = B.toSubring ∧ φV.range = C.toSubring ∧ φW.range = (AdjoinInv B t).toSubring ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) ∧
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) ∧
    (∀ a : A, φU (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a) ∧
    (∀ a : A, φV (p.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = algebraMap A K a)

def GeoData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def CoverOfData : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K),
    Charts B C t → ChartData p B C t → Cover p B C t

def Overlap : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t →
  ∀ (U V : Z.Opens) (φU : Γ(Z, U) →+* K) (φV : Γ(Z, V) →+* K) (φW : Γ(Z, U ⊓ V) →+* K)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V), IsAffineOpen (U ⊓ V) → U ⊔ V = ⊤ →
    ∀ (iU : Function.Injective φU) (iV : Function.Injective φV), Function.Injective φW →
    ∀ (rU : φU.range = B.toSubring) (rV : φV.range = C.toSubring), φW.range = (AdjoinInv B t).toSubring →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) = φU s) →
    (∀ s, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s) = φV s) →
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C),
      (chartMap hU φU iU B rU).base x = (chartMap hV φV iV C rV).base y ↔
        ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

theorem coverOfData_of (hO : Overlap) : CoverOfData := by
  intro A _ _ K _ _ Z p B C t hc hd
  obtain ⟨U, V, φU, φV, φW, hU, hV, hW, hUV, iU, iV, iW, rU, rV, rW, cU, cV, aU, aV⟩ := hd
  refine ⟨⟨chartMap hU φU iU B rU, chartMap hV φV iV C rV, inferInstance, inferInstance, ?_,
    chartMap_comp p hU φU iU B rU aU, chartMap_comp p hV φV iV C rV aV,
    hO A K p B C t hc U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV⟩⟩
  rw [chartMap_range, chartMap_range, ← TopologicalSpace.Opens.coe_sup, hUV, TopologicalSpace.Opens.coe_top]

theorem ChartsGeom_of' (hG : GeoData) (hC : CoverOfData) : LateralTheory.E.StdChartsProof.ChartsGeom := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hd⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, hC A K p B C t hc hd⟩

end LateralTheory.E.ChartsGeom_vpaPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.UliftSmulEq
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MulPf

def Gen : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l : ℤ) (h : j + k = l) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), μ j k l h X (twGen k ζ) (twGen j ζ) = twGen l ζ)

def LocGen : Prop := ∀ (q : ℕ) (j : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
  ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
    ∃ c : ℤ, Sec.res f x = c • twGen j (ζ.map f.appTop.hom)

theorem sep {q : ℕ} {j : ℤ} {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (s t : Sec (tw q j) X)
    (h : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f → Sec.res f s = Sec.res f t) : s = t :=
  Sheaf.isSeparated (tw q j) X S hS s t (fun _ f hf => h f hf)

theorem twGen_pow {q : ℕ} (m : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen m ξ = (ULift.up.{1} ((a ^ m : (ZMod q)ˣ) : ZMod q)) • twGen m ζ := by
  unfold twGen ofRings.sec
  have hmem : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single ζ (ULift.up ((a ^ m : (ZMod q)ˣ) : ZMod q)) ∈ twRel q m Γ(U, ⊤) :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have key : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q m).obj Γ(U, ⊤)) =
      (ULift.up.{1} ((a ^ m : (ZMod q)ˣ) : ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q m).obj Γ(U, ⊤)) := by
    refine ((Submodule.Quotient.eq (twRel q m Γ(U, ⊤))).2 hmem).trans ?_
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (congrArg (fun v => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q m)).app (op U)).hom v) key).trans (map_smul _ _ _)

theorem locPres {q : ℕ} {j : ℤ} {X : Scheme.{0}} (x : Sec (tw q j) X) :
    ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
      ∃ v : (twF q j).obj Γ(Y, ⊤), Sec.res f x = ofRings.sec (twF q j) Y v := by
  refine ⟨_, Presheaf.imageSieve_mem (J := Scheme.etaleTopology) (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j))
    (U := op X) x, fun Y f hf => ?_⟩
  obtain ⟨t, ht⟩ := hf
  exact ⟨t, ht.symm⟩

def RootPow : Prop := ∀ (q : ℕ) (Y : Scheme.{0}) (ζ : Prim q Γ(Y, ⊤)) (s : Finset (Prim q Γ(Y, ⊤))),
  ∃ S ∈ Scheme.etaleTopology Y, ∀ ⦃Z : Scheme.{0}⦄ (g : Z ⟶ Y), S g → ∀ ξ ∈ s,
    ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem secRes {q : ℕ} {j : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (v : (twF q j).obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (twF q j) U v) = ofRings.sec (twF q j) V (((twF q j).map g.appTop).hom v) := by
  unfold ofRings.sec
  have h := congrArg (fun φ => φ.hom v) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  exact h.symm

theorem sec_single {q : ℕ} {j : ℤ} {U : Scheme.{0}} (ξ : Prim q Γ(U, ⊤)) (c : ULift.{1} (ZMod q)) :
    ofRings.sec (twF q j) U (Submodule.Quotient.mk (Finsupp.single ξ c) : (twF q j).obj Γ(U, ⊤)) = c • twGen j ξ := by
  unfold twGen ofRings.sec
  have key : (Submodule.Quotient.mk (Finsupp.single ξ c) : (twF q j).obj Γ(U, ⊤)) =
      c • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(U, ⊤)) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (congrArg (fun v => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)).app (op U)).hom v) key).trans (map_smul _ _ _)

theorem ulift_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ULift.{1} (ZMod q)) (v : M) :
    c • v = ((c.down.cast : ℤ)) • v := by
  have hc : c = (((c.down.cast : ℤ)) : ULift.{1} (ZMod q)) := ULift.ext (by
    show c.down = ((c.down.cast : ℤ) : ULift.{1} (ZMod q)).down
    exact (ZMod.intCast_zmod_cast c.down).symm)
  conv_lhs => rw [hc]
  exact Int.cast_smul_eq_zsmul _ _ _

theorem sec_sum {q : ℕ} {j : ℤ} {U : Scheme.{0}} {ι : Type} (s : Finset ι) (g : ι → (twF q j).obj Γ(U, ⊤)) :
    ofRings.sec (twF q j) U (∑ i ∈ s, g i) = ∑ i ∈ s, ofRings.sec (twF q j) U (g i) := by
  unfold ofRings.sec
  exact map_sum _ _ _

theorem LocGen_of (hR : RootPow) : LocGen := by
  intro q j X ζ x
  obtain ⟨S, hS, hv⟩ := locPres x
  have hv' : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f → ∃ w : Prim q Γ(Y, ⊤) →₀ ULift.{1} (ZMod q),
      Sec.res f x = ofRings.sec (twF q j) Y (Submodule.Quotient.mk w : (twF q j).obj Γ(Y, ⊤)) := by
    intro Y f hf
    obtain ⟨v, hv⟩ := hv f hf
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨w, hv⟩
  choose w hw using hv'
  have hT := fun ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X) (hf : S f) => hR q Y (ζ.map f.appTop.hom) (w f hf).support
  choose T hTmem hTprop using hT
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hTmem, ?_⟩
  rintro Z _ ⟨Y, h, f, hf, hh, rfl⟩
  have hres : Sec.res (h ≫ f) x = Sec.res h (Sec.res f x) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [hres, hw f hf]
  erw [secRes]
  set G := twGen j (ζ.map (h ≫ f).appTop.hom)
  have hmk : (((twF q j).map h.appTop).hom (Submodule.Quotient.mk (w f hf) : (twF q j).obj Γ(Y, ⊤))) =
      ∑ ξ ∈ (w f hf).support, (Submodule.Quotient.mk (Finsupp.single (ξ.map h.appTop.hom) (w f hf ξ)) : (twF q j).obj Γ(Z, ⊤)) := by
    change (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (w f hf)) : (twF q j).obj Γ(Z, ⊤)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.mapDomain, Finsupp.sum, ← Submodule.mkQ_apply, map_sum]
    rfl
  rw [hmk]
  erw [sec_sum]
  have key : ∃ c : ULift.{1} (ZMod q), ∑ ξ ∈ (w f hf).support, ofRings.sec (twF q j) Z
      (Submodule.Quotient.mk (Finsupp.single (ξ.map h.appTop.hom) (w f hf ξ)) : (twF q j).obj Γ(Z, ⊤)) = c • G := by
    refine Finset.sum_induction _ (fun v => ∃ c : ULift.{1} (ZMod q), v = c • G) ?_ ⟨0, by simp⟩ ?_
    · rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, (add_smul c d G).symm⟩
    · intro ξ hξ
      obtain ⟨a, ha⟩ := hTprop f hf h hh ξ hξ
      rw [sec_single, twGen_pow j _ _ a ha, LateralTheory.E.TwistTrivial.prim_map_comp, smul_smul]
      exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := key
  exact ⟨_, hc.trans (ulift_smul_eq c G)⟩

theorem Mul_of (hG : Gen) (hL : LocGen) : LateralTheory.E.TwistTrivial.Mul := by
  intro q
  obtain ⟨μ, hnat, hgen⟩ := hG q
  refine ⟨μ, hnat, ?_⟩
  intro j k l k' h h' X ζ x
  obtain ⟨S, hS, hx⟩ := hL q j X ζ x
  refine sep S hS _ _ (fun Y f hf => ?_)
  obtain ⟨c, hc⟩ := hx f hf
  rw [hnat, hnat, LateralTheory.E.TwistTrivial.genRes, LateralTheory.E.TwistTrivial.genRes, hc, map_zsmul, hgen, map_zsmul, hgen]

end LateralTheory.E.MulPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure
section -- merged from Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.BaseAICPf.Loc

theorem aic_loc {A L : Type} [CommRing A] [CommRing L] [Algebra A L] (M : Submonoid A) [IsLocalization M L]
    (hA : AIC A) : AIC L := by
  classical
  intro p hm hd
  set n := p.natDegree
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (n + 1)).image p.coeff)
  set u := algebraMap A L b
  have hlift : p.scaleRoots u ∈ lifts (algebraMap A L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i n with h | h | h
    · obtain ⟨a, ha⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
      refine ⟨a * (b : A) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, ha, Algebra.smul_def, pow_succ]
      simp only [u]; ring
    · subst h; rw [tsub_self, pow_zero, mul_one]; exact ⟨1, by rw [map_one]; exact hm.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt h, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff u).2 hm)
  obtain ⟨a, ha⟩ := hA q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit u := IsLocalization.map_units L b
  obtain ⟨v, hv⟩ := id hu
  refine ⟨(↑v⁻¹ : L) * algebraMap A L a, ?_⟩
  have h1 : (p.scaleRoots u).eval (algebraMap A L a) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : (p.scaleRoots u).eval (u * ((↑v⁻¹ : L) * algebraMap A L a)) = u ^ n * p.eval ((↑v⁻¹ : L) * algebraMap A L a) :=
    scaleRoots_eval₂_mul (RingHom.id L) _ u
  have hur : u * ((↑v⁻¹ : L) * algebraMap A L a) = algebraMap A L a := by
    rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hur, h1] at h2
  have hun : IsUnit (u ^ n) := hu.pow n
  exact (hun.mul_right_eq_zero).1 h2.symm

end LateralTheory.E.BaseAICPf.Loc
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.AICOpenPf

namespace LateralTheory.E.BaseAICPf

theorem aic_of_local {Z : Scheme.{0}} [IsIntegral Z]
    (hloc : ∀ (W : Z.Opens) (y : Z), y ∈ W → ∃ U : Z.Opens, y ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U))
    (W : Z.Opens) (hW : (W : Set Z).Nonempty) : AIC Γ(Z, W) := by
  intro p hm hd
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, (x : Z) ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U) := fun x => hloc W x x.2
  choose U hxU hUW hUa using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W
  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

def BaseInt : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})

def BaseLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    AIC Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U)

def BaseLocLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra

theorem BaseLoc_of (h : BaseLocLoc) : BaseLoc := by
  intro Z S c _ _ _ hZ hS x W y hy
  obtain ⟨U, hyU, hUW, V, hV, hne, f, M, hM⟩ := h c hZ hS x W y hy
  letI := f.toAlgebra
  exact ⟨U, hyU, hUW, LateralTheory.E.BaseAICPf.Loc.aic_loc M (hZ.2 V hV hne)⟩

theorem BaseAIC_of (h1 : BaseInt) (h2 : BaseLoc) : LateralTheory.E.FibreEqvPf.BaseAIC := by
  intro Z S c _ _ _ hZ hS x
  have : IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := h1 c hZ hS x
  exact ⟨this, fun U _ hne => aic_of_local (h2 c hZ hS x) U hne⟩

end LateralTheory.E.BaseAICPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.HasLimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.HasLimPf

theorem hasLimit_of_affine {K : Type} [SmallCategory K] (F : K ⥤ Scheme.{0}) (hF : ∀ k, IsAffine (F.obj k)) :
    HasLimit F := by
  have : HasLimit (F ⋙ Scheme.Γ.rightOp) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} Scheme.Spec.{0} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  have : HasLimit (F ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) :=
    HasLimit.mk ⟨_, isLimitOfPreserves Scheme.Spec (limit.isLimit (F ⋙ Scheme.Γ.rightOp))⟩
  have : ∀ k, IsIso ((Functor.whiskerLeft F ΓSpec.adjunction.unit).app k) := fun k => by
    have := hF k
    dsimp; infer_instance
  have : IsIso (Functor.whiskerLeft F ΓSpec.adjunction.unit) := NatIso.isIso_of_isIso_app _
  exact hasLimit_of_iso (asIso (Functor.whiskerLeft F ΓSpec.adjunction.unit)).symm

def Loc : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (j₀ : J),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) →
  (∀ U : (D.obj j₀).Opens, IsAffineOpen U → HasLimit (opensDiagram D j₀ U)) → HasLimit (Over.forget j₀ ⋙ D)

theorem HasLim_of (hL : Loc) : LateralTheory.E.SysPf.HasLim := by
  intro J _ _ D hD
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have : HasLimit (Over.forget j₀ ⋙ D) := hL D j₀ hD (fun U hU => by
    refine hasLimit_of_affine _ (fun j => ?_)
    have := hD j.hom
    exact hU.preimage (D.map j.hom))
  have : HasLimit D := Functor.Initial.hasLimit_of_comp (Over.forget j₀)
  exact ⟨limit.cone D, ⟨limit.isLimit D⟩⟩

end LateralTheory.E.HasLimPf
end
end
