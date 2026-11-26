module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CechDR

variable {X X' : Scheme.{0}}

theorem Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩

theorem Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem Pair.exists_le (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩

theorem sec_eq_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairs
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem form_pow_smul_eq_zero_of_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  let A := (OAff s').obj (op W)
  let B := (OAff s').obj (op (⟨X'.basicOpen f, hU⟩ : X'.affineOpens))
  let ψ : A →ₐ[R'] B := mp (OAff s') (homOfLE hle).op
  letI : Algebra A B := (ψ : A →+* B).toAlgebra
  haveI : IsScalarTower R' A B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  haveI : IsLocalization.Away (show A from f) B := W.2.isLocalization_basicOpen f
  have e := (semiHom_mp (OAff s') (homOfLE hle).op).oneFormMap_eq_kaehlerDifferential_map (R := R') (B := A) (B' := B)
    (fun b ↦ rfl) ω
  have h' : KaehlerDifferential.map R' R' A B ω = 0 := e.symm.trans h
  obtain ⟨⟨c, hc⟩, hc0⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (show A from f))
    (f := KaehlerDifferential.map R' R' A B)).1 h'
  obtain ⟨n, rfl⟩ := hc
  exact ⟨n, hc0⟩

theorem form_eq_zero_of_pair {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) : ω = 0 := by
  let A := (OAff s').obj (op W)
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  let I : Set Γ(X', W.1) := {a | (show A from a) ∈ J}
  have hcov : W.1 ≤ ⨆ a : I, X'.basicOpen a.1 := by
    intro x hx
    obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
    obtain ⟨⟨⟨U, hU⟩, V⟩, hpV⟩ := p
    dsimp only at e hxp
    subst e
    have hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W := X'.basicOpen_le f
    obtain ⟨n, hn⟩ := form_pow_smul_eq_zero_of_basicOpen s' W f hU hle ω
      (h ⟨(⟨X'.basicOpen f, hU⟩, V), hpV⟩ hle)
    have hxn : x ∈ X'.basicOpen (f ^ n) := by
      rcases n with _ | n
      · rw [pow_zero, X'.basicOpen_of_isUnit isUnit_one]; exact hx
      · rwa [X'.basicOpen_pow f n.succ_pos]
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f ^ n, show ((show A from f) ^ n) ∈ J from
        (Submodule.mem_annihilator_span_singleton ω _).2 hn⟩, hxn⟩
  have hI := (W.2.self_le_iSup_basicOpen_iff).1 hcov
  have hJ : Ideal.span I ≤ J := Ideal.span_le.2 fun a ha ↦ ha
  have h1 : (1 : A) ∈ J := hJ (hI ▸ Submodule.mem_top)
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by
  first | exact @GlobalTheory.CechDR.form_eq_zero_of_pair | exact GlobalTheory.CechDR.form_eq_zero_of_pair | (intros; apply GlobalTheory.CechDR.form_eq_zero_of_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairs
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem pair_glue : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  intro R' _ X X' φ s' W k hk
  let U : {p : Pair φ // p.1.1 ≤ W} → X'.Opens := fun i ↦ i.1.1.1.1
  let sf : ∀ i : {p : Pair φ // p.1.1 ≤ W}, ToType (X'.sheaf.1.obj (op (U i))) := fun i ↦ k i.1 i.2

  have key : ∀ (i : {p : Pair φ // p.1.1 ≤ W}) (r : Pair φ) (hr : r ≤ i.1) {x : X'} (hx : x ∈ r.1.1.1),
      X'.presheaf.germ (U i) x (Pair.le_fst hr hx) (sf i) =
        X'.presheaf.germ r.1.1.1 x hx (k r ((Pair.le_fst hr).trans i.2)) := by
    intro i r hr x hx
    rw [← hk i.1 r i.2 ((Pair.le_fst hr).trans i.2) hr]
    exact (X'.presheaf.germ_res_apply (homOfLE (show r.1.1.1 ≤ U i from Pair.le_fst hr)) x hx _).symm
  have hcomp : TopCat.Presheaf.IsCompatible X'.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun x hx ↦ ?_
    obtain ⟨r, hri, hrj, hxr⟩ := Pair.exists_le_le φ i.1 j.1 hx
    change X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf i)) = X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf j))
    exact ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (U i) (U j)) x hx (sf i)).trans
      (key i r hri hxr)).trans ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (U i) (U j))
        x hx (sf j)).trans (key j r hrj hxr)).symm
  have hcov : W.1 ≤ iSup U := fun x hx ↦ by
    obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' U W.1 (fun i ↦ homOfLE i.2) hcov sf hcomp
  exact ⟨G, fun p hp ↦ hG ⟨p, hp⟩⟩

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)), (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p), mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) → ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  first | exact @GlobalTheory.CechDR.pair_glue | exact GlobalTheory.CechDR.pair_glue | (intros; apply GlobalTheory.CechDR.pair_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem exists_cob_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (f : Z1 (OAff s'))
    (g : ∀ p : Pair φ, (OAff s').obj (op p.1.1))
    (hg : ∀ (p q : Pair φ) (hqp : q ≤ p), f.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
      g q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g p)) :
    ∃ G : C0 (OAff s'), d0 (OAff s') G = f.1 ∧ ∀ (W : X'.affineOpens) (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op (G (op W)) = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
  have ex : ∀ W : X'.affineOpens, ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op G = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
    intro W
    refine GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs φ s' W _ fun p q hp hq hqp ↦ ?_
    have e := Z1.comp f (homOfLE hp).op (homOfLE (Pair.le_fst hqp)).op
    rw [show (homOfLE hp).op ≫ (homOfLE (Pair.le_fst hqp)).op = (homOfLE hq).op from rfl, hg p q hqp] at e
    rw [map_sub, e]
    ring
  choose G hG using ex
  refine ⟨fun T ↦ G T.unop, ?_, hG⟩
  funext T T' a
  refine sec_eq_of_pair φ s' T'.unop _ _ fun p hp ↦ ?_
  have e1 := Z1.comp f a (homOfLE hp).op
  have e2 : a ≫ (homOfLE hp).op = (homOfLE (hp.trans (leOfHom a.unop))).op := rfl
  rw [e2] at e1
  rw [amitsur_d0_apply, map_sub, ← mp_comp, e2, hG, hG]
  linear_combination e1

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential

theorem pairRes_injective : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  intro R' _ X X' φ s'
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    obtain ⟨G, hG, -⟩ := exists_cob_of_pair φ s' f (fun p ↦ g (op p)) fun p q hqp ↦
      (congrFun (congrFun (congrFun hg (op p)) (op q)) (homOfLE hqp).op).symm
    exact H1.mk_eq_zero.2 ⟨G, hG⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    have h0 : ∀ p : Pair φ, ω.1 (op p.1.1) = 0 := fun p ↦
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) (op p) _).symm.trans
        (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) hω)
    refine Subtype.ext (funext fun W ↦ GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop _ fun p hp ↦ ?_)
    rw [← ω.2 (homOfLE hp).op]
    exact h0 p
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Hyp1.mk_surjective _ c
    rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ p : Pair φ, (OAff s').obj (op p.1.1) := fun p ↦ g (op p)
    have hf : ∀ (p q : Pair φ) (hqp : q ≤ p), z.1.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
        g' q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g' p) := fun p q hqp ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.1 (op p) (op q) (homOfLE hqp).op) hg).symm
    have hω : ∀ p : Pair φ, D R' _ (g' p) = z.1.2 (op p.1.1) := fun p ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.2 (op p)) hg).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor _ _ _ _)
    obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' (cechDeRhamTotalCocyclesOne.fn _ z) g' hf
    refine Hyp1.mk_eq_zero.2 ⟨G, Tot1.ext (fun T T' a ↦ congrFun (congrFun (congrFun hG T) T') a)
      fun W ↦ ?_⟩
    refine (sub_eq_zero.1 (GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop (D R' _ (G W) - z.1.2 W) fun p hp ↦ ?_))
    have e := cechDeRhamTotalCocyclesOne.conn z (homOfLE hp).op
    rw [map_sub, p1_D, hGp, map_sub, hω]
    change _ - (p1 _ _ _) = _
    rw [e, show ((cechDeRhamTotalCocyclesOne.fn (OAff s') z : Z1 (OAff s')) : C1 (OAff s')) = z.1.1 from rfl]
    abel

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomologyStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePairRestriction_injective_firstCohomology : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧ Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  first | exact @GlobalTheory.CechDR.pairRes_injective | exact GlobalTheory.CechDR.pairRes_injective | (intros; apply GlobalTheory.CechDR.pairRes_injective <;> assumption)
end
