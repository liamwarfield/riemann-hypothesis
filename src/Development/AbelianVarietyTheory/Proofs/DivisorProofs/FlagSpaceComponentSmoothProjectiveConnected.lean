module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem tri_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {S : Type} [CommRing S] {φ : c.F →+* S} (z : Sp S ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') (g g' : EigFrame Y φ (z ≫ π)) (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') : ∃ d, g.Tri (RingHom.id S) g' d := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have h1 : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => F.TAt k k' z hh (some ⟨τ, i⟩), by rw [h2, Category.id_comp], rfl, fun τ i =>
    ⟨fun j => (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) j i, rfl, fun j hj => F.B_map_tri k k' τ _ hj, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have e : (fun j => g.v τ j) = fun j => (tv (F.vecAt k z hz rfl τ j)).left := funext (hg τ)
  rw [e, hg' τ i, GlobalTheory.LieMet.isComb_iff]
  exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i

end GlobalTheory.VarFlag

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_congr {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x x' : Sp K ⟶ Y.X} (h : x = x') (g : EigFrame Y φ x) (g' : EigFrame Y φ x')
    (hv : ∀ τ i, g.v τ i = g'.v τ i) (p : Sp K ⟶ C.Y.X) : C.Carries p g ↔ C.Carries p g' := by
  subst h
  obtain ⟨v, a1, a2, a3⟩ := g
  obtain ⟨v', b1, b2, b3⟩ := g'
  have e : v = v' := funext fun τ => funext fun i => hv τ i
  subst e
  rfl

theorem carries_of_tri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {g' : EigFrame Y φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem carries_over {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {p : Sp K ⟶ C.Y.X} (hp : C.Carries p g) :
    p ≫ C.π ≫ genι Y = x := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  rw [h1, Category.assoc, ← h3.1]

theorem uniq_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hlifts hbar K _ z
  set zz := z ≫ GlobalTheory.CompHS.inc₀ X Z with hzz

  let φ : c.F →+* K := (Spec.preimage (zz ≫ X.π ≫ Y.s)).hom
  have hφ : zz ≫ X.π ≫ Y.s = spMap φ := (Spec.map_preimage _).symm

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover zz
  obtain ⟨g, hg⟩ := hFE K φ zz k hk hφ

  let xg : Sp K ⟶ gen Y := zz ≫ X.π ≫ inv (genι Y)
  have hxg : xg ≫ genι Y = zz ≫ X.π := by simp [xg]
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hstr : xg ≫ genStr Y = spMap φ := by
    have e : genStr Y = genι Y ≫ Y.s := by
      calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
        _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
    rw [e, ← Category.assoc, hxg, Category.assoc, hφ]

  have hr : Set.range xg ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    refine (hbar _).1 ?_
    have e : genι Y (xg a) = X.π (GlobalTheory.CompHS.inc₀ X Z (z a)) := by
      rw [← Scheme.Hom.comp_apply, hxg]; rfl
    rw [e]
    have hm : GlobalTheory.CompHS.inc₀ X Z (z a) ∈ X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z := by
      have := (Scheme.Opens.range_ι (X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z)).le ⟨z a, rfl⟩
      exact this
    exact hm
  let x' := IsOpenImmersion.lift j xg hr
  have hx' : x' ≫ j = xg := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ (xg ≫ genι Y), ∀ τ i, g0.v τ i = g.v τ i := by
    rw [hxg]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨p, ⟨hp1, hp2⟩, hpu⟩ := hlifts K φ xg x' hx' hstr g0
  refine ⟨p, ⟨φ, k, hk, g, hφ, hg, (carries_congr C hxg g0 g hg0 p).1 hp2⟩, ?_⟩
  rintro p' ⟨φ', k', hk', g', hφ', hg', hc'⟩
  have e : φ' = φ := by
    have h0 : spMap φ' = spMap φ := hφ'.symm.trans hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst e
  obtain ⟨d, hd⟩ := tri_of_isFrameAt X.F zz k' k hk' hk g' g hg' hg
  have hc : C.Carries p' g := carries_of_tri C hd hc'
  have hc0 : C.Carries p' g0 := (carries_congr C hxg g0 g hg0 p').2 hc
  refine hpu p' ⟨?_, hc0⟩
  have h1 : p' ≫ C.π = xg := by
    rw [← cancel_mono (genι Y), Category.assoc]
    exact carries_over C hc0
  rw [← cancel_mono j, Category.assoc, ← hπ, h1, hx']

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  first | exact @GlobalTheory.VarFlag.uniq_rel | exact GlobalTheory.VarFlag.uniq_rel | (intros; apply GlobalTheory.VarFlag.uniq_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames frX frVec)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem tv_vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X}
    (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx
  rfl

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (Q Q' : FrPt Xo c S)
    (e : Q'.x = Q.x) : ∃ u : Sˣ, ∀ e : Q'.x = Q.x, ∀ i, (e ▸ Q'.s).f i = scal Q.x (u : S) i * Q.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨u0, fun _ => hu0⟩

theorem rel_unique : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  intro E _ _ _ H Dw l Xo c Y X C _ hC K _ z z' p hp hr hr'
  obtain ⟨φ, k, hk, g, hφ, hg, hc⟩ := hr
  obtain ⟨φ', k', hk', g', hφ', hg', hc'⟩ := hr'
  have e1 : p ≫ C.π ≫ genι Y = z ≫ X.π := carries_over C hc
  have e2 : p ≫ C.π ≫ genι Y = z' ≫ X.π := carries_over C hc'
  have hπ : z' ≫ X.π = z ≫ X.π := e2.symm.trans e1
  have ephi : φ' = φ := by
    have h0 : spMap φ' = spMap φ := by rw [← hφ', ← hφ, ← Category.assoc, hπ, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst ephi
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ' (z ≫ X.π), ∀ τ i, g0.v τ i = g'.v τ i := by
    rw [← hπ]; exact ⟨g', fun _ _ => rfl⟩
  have hc0 : C.Carries p g0 := (carries_congr C hπ.symm g0 g' hg0 p).2 hc'
  obtain ⟨t, ht⟩ := hC K _ _ (z ≫ X.π) p g g0 hc hc0
  letI : Algebra c.F K := φ'.toAlgebra
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hxg : (p ≫ C.π) ≫ genι Y = z ≫ X.π := by rw [Category.assoc]; exact e1
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have := hp a
    rw [Scheme.Hom.comp_apply]
    exact this
  have := Y.jQ_open
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy0 : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hyj : z ≫ X.π = y ≫ Y.j := by
    rw [Model.j, ← Category.assoc, hy0, ← hxg]
  have hstr : genStr Y = genι Y ≫ Y.s := by
    calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← Y.jQ_over, ← Category.assoc, hy0]
    show (p ≫ C.π) ≫ genStr Y = _
    rw [hstr, ← Category.assoc, hxg, Category.assoc]
    exact hφ
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hyj k hk
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr hy (hπ.trans hyj) k' hk'
  have hx : frX Q ≫ Y.j = z ≫ X.π := hQ.over
  have hx' : frX Q' ≫ Y.j = z ≫ X.π := hQ'.over.trans hπ
  have eQ : Q'.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := Y) (GlobalTheory.FlagMod.frX_snd Q') (GlobalTheory.FlagMod.frX_snd Q) (hx'.trans hx.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q Q' eQ
  choose cf hcf1 hcf2 hcf3 using ht.2.2
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  let T : Ix Dw → Kˣ := fun ix => match ix with | none => u0 | some q => t q.1 q.2
  have hB : FrBor T Q Q' := by
    refine GlobalTheory.FlagMod.frBor_of_frVec (X.F.inM hk rfl) hx hx' T (fun σ j i => cf σ i j)
      (fun σ r s hrs => hcf2 σ s r hrs) (fun σ i => hcf1 σ i) (fun σ i => ?_) hu0
    rw [hQ'.frVec_eq hπ hx', hQ.frVec_eq rfl hx]
    refine (GlobalTheory.LieMet.isComb_iff _ _ _).1 ?_
    have h3 := hcf3 σ i
    simp only [h1, Category.id_comp] at h3
    rw [hg0 σ i, hg' σ i, ← tv_vecAt_congr X.F k' z' hk' hπ σ i] at h3
    have e : (fun j => g.v σ j) = fun j => (tv (X.F.vecAt k z hk rfl σ j)).left := funext (hg σ)
    rw [e] at h3
    exact h3
  exact (X.rep K Q').unique (hQ.lies.frBor hB) hQ'.lies

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  first | exact @GlobalTheory.VarFlag.rel_unique | exact GlobalTheory.VarFlag.rel_unique | (intros; apply GlobalTheory.VarFlag.rel_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open GlobalTheory.Toroidal (gen genι genStr)

theorem exists_rel_of_mem_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hbar K _ p hp

  obtain ⟨yF, hyF, hcar⟩ := GlobalTheory.Mean4O.CompModel.exists_flagPt C p

  haveI := Y.jQ_open
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hp s
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hys : y ≫ pullback.snd _ _ = spMap yF.fK := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hyF]
    exact yF.y_over

  obtain ⟨P, hPy, hPw⟩ := GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y K yF.fK y
    (yF.y ≫ genι Y) yF.frame hys (by rw [← Category.assoc, hy, hyF])
  letI : Algebra c.F K := yF.fK.toAlgebra
  have hPX : GlobalTheory.FlagMod.frX P = y := hPy
  have hl := X.lies_ptY P
  have hxg : X.ptY P ≫ X.π = yF.y ≫ genι Y := by
    rw [hl.1, hPX, Model.j, ← Category.assoc, hy, hyF]

  have hr₀ : Set.range (X.ptY P) ⊆ Set.range (GlobalTheory.CompHS.inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    show X.π (X.ptY P s) ∈ GlobalTheory.CompHS.barComp Y Z
    have e : X.π (X.ptY P s) = genι Y (j (f (p s))) := by
      rw [← Scheme.Hom.comp_apply, hxg, ← hyF, hπ]
      rfl
    rw [e]
    exact (hbar _).2 ⟨f (p s), rfl⟩
  let z := IsOpenImmersion.lift (GlobalTheory.CompHS.inc₀ X Z) (X.ptY P) hr₀
  have hz : z ≫ GlobalTheory.CompHS.inc₀ X Z = X.ptY P := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z, ?_⟩
  rw [hz]

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P)
  have hφ : X.ptY P ≫ X.π ≫ Y.s = spMap yF.fK := GlobalTheory.CompHS.ptY_str X P
  obtain ⟨g₂, hg₂⟩ := hFE K yF.fK (X.ptY P) k hk hφ
  refine ⟨yF.fK, k, hk, g₂, hφ, hg₂, ?_⟩

  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have ht' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).2.2.1 _ _ _ ht
  have hPx : GlobalTheory.FlagMod.frX P ≫ Y.j = X.ptY P ≫ X.π := hl.1.symm
  choose b hb hdiag hsum using fun τ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (X.F.M k).toMChart) (X.F.inM hk rfl) hPx hQ.over ht' τ

  have hgv : ∀ τ i, yF.frame.v τ i = (tv (GlobalTheory.FlagMod.frVec Y P hPx τ i)).left := by
    intro τ i
    obtain ⟨w, hw1, hw2, hw3⟩ := hPw τ i
    rw [← hPX] at hw1
    have hL : w = GlobalTheory.FlagMod.liftTan Y (GlobalTheory.FlagMod.frX P) ((GlobalTheory.FlagMod.frX_fst P).symm ▸ P.tan τ i) :=
      Y.m0.cart.1.hom_ext (hw2.trans (GlobalTheory.FlagMod.liftTan_univ _ _).symm)
        (hw1.trans (GlobalTheory.FlagMod.liftTan_over _ _).symm)
    show yF.frame.v τ i = _
    rw [← hw3, hL]
    rfl
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have hd : yF.frame.Tri (RingHom.id K) g₂ (fun τ i => (t⁻¹) (some ⟨τ, i⟩)) := by
    refine ⟨by rw [h2, Category.id_comp, hxg], rfl, fun τ i => ⟨fun m => b τ m i, hdiag τ i,
      fun m hm => hb τ hm, ?_⟩⟩
    simp only [h1, Category.id_comp]
    have e : (fun m => yF.frame.v τ m) = fun m => (tv (GlobalTheory.FlagMod.frVec Y P hPx τ m)).left := funext (hgv τ)
    rw [e, hg₂ τ i, GlobalTheory.LieMet.isComb_iff, ← hQ.frVec_eq rfl hQ.over τ]
    exact hsum τ i
  exact carries_of_tri C hd hcar

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  first | exact @GlobalTheory.VarFlag.exists_rel_of_mem_Vo | exact GlobalTheory.VarFlag.exists_rel_of_mem_Vo | (intros; apply GlobalTheory.VarFlag.exists_rel_of_mem_Vo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuli
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VarFlag

theorem isIso_restrict_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  intro E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH
  have := C.Y.isNormalScheme
  have hN := GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme
  have : IsLocallyNoetherian C.Y.X := LocallyOfFiniteType.isLocallyNoetherian C.Y.str
  refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance
    fun K _ w => ?_
  have hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C := fun s => by
    rw [Scheme.Hom.comp_apply]; exact (w s).2
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint X Z hF C hT B j f hπ hB K _ hp
  have e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := (hU K z₀).unique (hH K z₀) hz₀
  have P := (isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip
  refine ⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    have ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
    have hr := hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)
    rw [ey] at hr
    have := GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point X C hF hT K _ _ _ hp hr hz₀
    exact (cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this
  · rw [P.lift_snd]; exact hy

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFlagModelFlagBundleOverModuliStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  first | exact @GlobalTheory.VarFlag.isIso_restrict_Vo | exact GlobalTheory.VarFlag.isIso_restrict_Vo | (intros; apply GlobalTheory.VarFlag.isIso_restrict_Vo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

attribute [local instance] Over.cartesianMonoidalCategory

theorem rel_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C K K' _ _ ι z p hR
  obtain ⟨φ, k, hz, g, hs, hg, y, ψ, φ₁, f, t, t', hp, hf0, hx, hφ, hcomb⟩ := hR
  have hz' : ⊤ ≤ (spMap ι ≫ z) ⁻¹ᵁ X.F.U k := fun w _ => by
    exact hz (show spMap ι w ∈ (⊤ : (Sp K).Opens) from trivial)
  have hs' : (spMap ι ≫ z) ≫ X.π ≫ Y.s = spMap (ι.comp φ) := by
    rw [Category.assoc, hs, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨g', hg'⟩ := hFE K' (ι.comp φ) (spMap ι ≫ z) k hz' hs'
  have e : spMap ι ≫ (z ≫ X.π) = (spMap ι ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  have hv : ∀ τ i, g'.v τ i = spMap (dualMap ι) ≫ g.v τ i := fun τ i => by
    have h1 : g'.v τ i = (tv (GlobalTheory.FlagMod.tanPull ι e (X.F.vecAt k z hz rfl τ i))).left := by
      rw [hg' τ i, X.F.tanPull_vecAt k ι z hz hz' rfl rfl e]
    rw [h1, hg τ i]
    rfl
  refine ⟨ι.comp φ, k, hz', g', hs', hg', y, ι.comp ψ, φ₁, f, t, fun τ i => Units.map ι.toMonoidHom (t' τ i), ?_, hf0,
    ?_, ?_, fun τ i => ?_⟩
  · rw [hp, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [Category.assoc, hx, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [hφ]; rfl
  · obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
    refine ⟨fun j => ι (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩
    have h4 := GlobalTheory.LatDRFree.comb_map Y.t ι h3
    have hd : ∀ j, spMap (dualMap ι) ≫ spMap (dualMap ψ) ≫ f.v τ j = spMap (dualMap (ι.comp ψ)) ≫ f.v τ j := fun j => by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
      have hmap : (dualMap ι).comp (dualMap ψ) = dualMap (ι.comp ψ) := by
        ext a <;> simp [dualMap]
      rw [hmap]
    simp only [hd] at h4
    rw [hv, ← e]
    exact h4

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  first | exact @GlobalTheory.VarFlag.rel_baseChange | exact GlobalTheory.VarFlag.rel_baseChange | (intros; apply GlobalTheory.VarFlag.rel_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProper
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProper
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldPointGraph

theorem epi_spMap {K K' : Type} [Field K] [Field K'] (ι : K →+* K') : Epi (spMap ι) := by
  have : Flat (spMap ι) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ι.toAlgebra
    exact (inferInstance : Module.Flat K K')
  have : Surjective (spMap ι) := ⟨fun y => ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pt (K : Type) [Field K] : Sp K := IsLocalRing.closedPoint K

theorem eq_pt {K : Type} [Field K] (t : Sp K) : t = pt K := Subsingleton.elim _ _

theorem exists_eq_spMap_comp {X : Scheme.{0}} {K : Type} [Field K] (c : Sp K ⟶ X) {x : X}
    (hx : c (pt K) = x) :
    ∃ ι : X.residueField x →+* K, c = spMap ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X c).symm⟩

theorem exists_valuationRing_factor {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (φ : R →+* A)
      (ι : FractionRing A →+* K), IsLocalHom φ ∧
        ι.comp ((algebraMap A (FractionRing A)).comp φ) = f := by
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, inferInstance, inferInstance, inferInstance, f.codRestrict A.toSubring hA,
    IsFractionRing.lift (A := A) (g := A.subtype) Subtype.val_injective, hl, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (A := A) (g := A.subtype) Subtype.val_injective _

theorem exists_valuationRing_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (u : Sp A ⟶ X)
      (ι : FractionRing A →+* X.residueField x),
      spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ u = X.fromSpecResidueField x ∧
        (spMap (IsLocalRing.residue A) ≫ u) (pt _) = y := by
  obtain ⟨A, _, _, _, φ, ι, hl, hf⟩ := exists_valuationRing_factor
    (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
  refine ⟨A, inferInstance, inferInstance, inferInstance, spMap φ ≫ X.fromSpecStalk y, ι, ?_, ?_⟩
  · have e : spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ spMap φ =
        Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf]
      rfl
    refine Eq.trans ?_ ((congrArg (· ≫ X.fromSpecStalk y) e).trans ?_)
    · simp only [Category.assoc]
    · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      rfl
  · have e1 : (spMap (IsLocalRing.residue A)) (pt _) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    have e2 : (spMap φ) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint _ :=
      IsLocalRing.comap_closedPoint φ
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]
    exact (congrArg (X.fromSpecStalk y) e2).trans Scheme.fromSpecStalk_closedPoint

theorem exists_section {W Q : Scheme.{0}} (r : W ⟶ Q) [IsProper r] [IsNoetherian Q]
    [GlobalTheory.IsNormalScheme Q] (G : ∀ (K : Type) [Field K], (Sp K ⟶ W) → Prop)
    (hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! c, G K c ∧ c ≫ r = z)
    (hB : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K c → G K' (spMap ι ≫ c))
    (hV : ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ W),
      G (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) →
      G (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u)) :
    ∃ s : Q ⟶ W, s ≫ r = 𝟙 Q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), G K (z ≫ s) := by

  have hD : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K' (spMap ι ≫ c) → G K c := by
    intro K K' _ _ ι c hc
    obtain ⟨d, ⟨hd, hdr⟩, -⟩ := hU K (c ≫ r)
    have e : spMap ι ≫ c = spMap ι ≫ d :=
      (hU K' (spMap ι ≫ c ≫ r)).unique ⟨hc, Category.assoc _ _ _⟩
        ⟨hB _ _ ι d hd, by rw [Category.assoc, hdr]⟩
    have := epi_spMap ι
    rwa [(cancel_epi _).mp e]
  let T : Set W := {x | G (W.residueField x) (W.fromSpecResidueField x)}
  have hT : ∀ (K : Type) [Field K] (c : Sp K ⟶ W),
      G K c ↔ c (pt K) ∈ T := by
    intro K _ c
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp c rfl
    exact ⟨fun h => hD _ _ ι _ (hι ▸ h), fun h => by rw [hι]; exact hB _ _ ι _ h⟩
  have hspec : ∀ x y : W, x ⤳ y → x ∈ T → y ∈ T := by
    intro x y h hx
    obtain ⟨A, _, _, _, u, ι, hu, hy⟩ := exists_valuationRing_of_specializes h
    have h1 := hV A u (hD _ _ ι _ (hu ▸ hx))
    rwa [hT, hy] at h1
  choose g hg hg' using fun y : Q => hU (Q.residueField y) (Q.fromSpecResidueField y)
  let γ : Q → W := fun y => g y (pt _)
  have hγT : ∀ y, γ y ∈ T := fun y => (hT _ _).mp (hg y).1
  have hγr : ∀ y, r (γ y) = y := fun y => by
    refine (Scheme.Hom.comp_apply (g y) r _).symm.trans ?_
    rw [(hg y).2]
    exact Scheme.fromSpecResidueField_apply _ _
  have hTγ : ∀ x ∈ T, x = γ (r x) := by
    intro x hx
    have hpt : (W.fromSpecResidueField x ≫ r) (pt (W.residueField x)) =
        r x := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp (K := W.residueField x) _ hpt
    have e : W.fromSpecResidueField x = spMap ι ≫ g (r x) :=
      (hU (W.residueField x) (W.fromSpecResidueField x ≫ r)).unique ⟨hx, rfl⟩
        ⟨hB _ _ ι _ (hg _).1, by rw [Category.assoc, (hg _).2, hι]⟩
    have e1 := Scheme.fromSpecResidueField_apply x (pt (W.residueField x))
    refine e1.symm.trans ?_
    rw [e, Scheme.Hom.comp_apply]
    exact congrArg (g (r x)) (eq_pt _)
  have hfin : (γ '' genericPoints Q).Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image γ
  have hsub : closure (γ '' genericPoints Q) ⊆ T := by
    intro x hx
    rw [← Set.biUnion_of_singleton (γ '' genericPoints Q), hfin.closure_biUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, ⟨y, -, rfl⟩, hx⟩ := hx
    exact hspec _ _ (specializes_iff_mem_closure.mpr hx) (hγT y)
  have hcl : IsClosed T := by
    have hsurj : r '' closure (γ '' genericPoints Q) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← genericPoints.closure (α := Q)]
      refine closure_minimal (fun y hy => ⟨γ y, subset_closure ⟨y, hy, rfl⟩, hγr y⟩)
        (r.isClosedMap _ isClosed_closure)
    have : T = closure (γ '' genericPoints Q) := by
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      obtain ⟨x', hx', e⟩ : r x ∈ r '' closure (γ '' genericPoints Q) := hsurj ▸ Set.mem_univ _
      rwa [hTγ x hx, ← e, ← hTγ x' (hsub hx')]
    rw [this]
    exact isClosed_closure
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hcl⟩ : Closeds W)
  have hI : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hGI : ∀ (K : Type) [Field K] (c : Sp K ⟶ I.subscheme), G K (c ≫ I.subschemeι) := by
    intro K _ c
    rw [hT, ← hI, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : IsIso (I.subschemeι ≫ r) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance
      (ReducedSubgroup.isReduced_subscheme_vanishingIdeal _) (GlobalTheory.IsNormalScheme.pred _)
      inferInstance fun K _ z => ?_
    obtain ⟨c, ⟨hc, hcr⟩, hu⟩ := hU K z
    have hker : I.subschemeι.ker ≤ c.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      apply ReducedSubgroup.vanishingIdeal_le_ker c ⟨T, hcl⟩
      rintro _ ⟨t, rfl⟩
      rw [eq_pt t]
      exact (hT K c).mp hc
    have hl := IsClosedImmersion.lift_fac I.subschemeι c hker
    refine ⟨IsClosedImmersion.lift I.subschemeι c hker, ?_, fun d hd => ?_⟩
    · show _ ≫ _ ≫ _ = _
      rw [← Category.assoc, hl, hcr]
    · rw [← cancel_mono I.subschemeι, hl]
      exact hu _ ⟨hGI K d, (Category.assoc _ _ _).trans hd⟩
  refine ⟨inv (I.subschemeι ≫ r) ≫ I.subschemeι, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← Category.assoc]
    exact hGI K _

theorem exists_hom_of_rel : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  intro Q P S q p _ _ _ R hC hU hB hV
  obtain ⟨s, hs, hG⟩ := exists_section (pullback.fst q p)
    (fun K _ c => R K (c ≫ pullback.fst q p) (c ≫ pullback.snd q p))
    (fun K _ z => by
      obtain ⟨w, hw, hu⟩ := hU K z
      refine ⟨pullback.lift z w (hC K z w hw), ⟨?_, pullback.lift_fst _ _ _⟩, fun c hc => ?_⟩
      · rwa [pullback.lift_fst, pullback.lift_snd]
      · refine pullback.hom_ext (by rw [pullback.lift_fst, hc.2]) ?_
        rw [pullback.lift_snd]
        exact hu _ (hc.2 ▸ hc.1))
    (fun K K' _ _ ι c hc => by
      rw [Category.assoc, Category.assoc]
      exact hB K K' ι _ _ hc)
    (fun A _ _ _ u hu => by
      rw [Category.assoc, Category.assoc] at hu ⊢
      exact hV A _ _ (by simp [pullback.condition]) hu)
  refine ⟨s ≫ pullback.snd q p, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · have := hG K z
    rwa [Category.assoc, Category.assoc, hs, Category.comp_id] at this

end GlobalTheory.FieldPointGraph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProperStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  first | exact @GlobalTheory.FieldPointGraph.exists_hom_of_rel | exact GlobalTheory.FieldPointGraph.exists_hom_of_rel | (intros; apply GlobalTheory.FieldPointGraph.exists_hom_of_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag
open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.AnForm.R.FinalTheorems (Snc)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal)
open GlobalTheory.CompHS (Y₀ inc₀ str₀ barComp U₀ IsVariety₀ TorFlag dense_U₀ flagStr flagOpen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem Rel.over (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] {z : Sp K ⟶ X.YY} {p : Sp K ⟶ C.Y.X}
    (h : Rel X.F C z p) : z ≫ X.π = p ≫ C.π ≫ genι Y := by
  obtain ⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩ := h
  rw [hT.1, hp]
  simp only [Category.assoc]

theorem barComp_iff (Z : Formalism.L2.Pj.Comp Xo c) (B : Formalism.L2.Pj.Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen Y)
    (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, ∀ p ∈ i.1, Y.jQ p ∈ Set.range (j i))
    (h3 : ∀ z : gen Y, ∃! i, z ∈ Set.range (j i)) (w : gen Y) :
    genι Y w ∈ barComp Y Z ↔ w ∈ Set.range (j Z) := by
  have hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p) := fun p => rfl
  have hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1 := fun p => by
    obtain ⟨u, hu, hs⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))
    exact ⟨⟨u, hu⟩, hs rfl⟩
  have key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1 := fun p hp => by
    obtain ⟨i, hi⟩ := hc p
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    have e : i = Z := (hu' i (h2 i p hi)).trans (hu' Z hp).symm
    exact e ▸ hi
  obtain ⟨i, hi, -⟩ := h3 w
  constructor
  · intro hw
    by_contra hn
    have hiZ : i ≠ Z := fun e => hn (e ▸ hi)
    apply hw
    rw [mem_closure_iff]
    intro O hO hwO
    have := h1 i
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ := Y.jQ_dense.inter_open_nonempty _
      ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩
    refine ⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    exact hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)
  · rintro ⟨b, rfl⟩ hw
    have := h1 Z
    rw [mem_closure_iff] at hw
    obtain ⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩ := hw (genι Y '' Set.range (j Z))
      ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩
    have e : w' = Y.jQ p := (genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))
    exact hpZ (key p (e ▸ hw'))

theorem genStr_eq : genStr Y = genι Y ≫ Y.s := by
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  exact ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm

theorem smooth_iso {A B S : Scheme.{0}} (e : A ⟶ B) [IsIso e] (g : B ⟶ S) {d : ℕ} (h : SmoothOfRelativeDimension d g) :
    SmoothOfRelativeDimension d (e ≫ g) := by
  have := smoothOfRelativeDimension_comp 0 d e g
  rwa [Nat.zero_add] at this

theorem smooth_gen {d : ℕ} (h : SmoothOfRelativeDimension d Y.s) : SmoothOfRelativeDimension d (genStr Y) := by
  rw [genStr_eq]
  exact smooth_iso _ _ h

theorem isVariety_of_iso (X : FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c) (C : FlagCpt Y (RingEquiv.refl c.F))
    (e : Y₀ X Z ⟶ C.Y.X) [IsIso e] (he : e ≫ C.Y.str = str₀ X Z) (hd : C.Y.dim = GlobalTheory.FlagTan.dimFlag Dw) : IsVariety₀ X Z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hd]
    exact smooth_iso _ _ inferInstance
  · obtain ⟨N, i, hi, hs⟩ := C.Y.isProjOver
    exact ⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩
  · rw [← he]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance

theorem dim_eq (Dw : Datum H) : Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = GlobalTheory.FlagTan.dimFlag Dw := by
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]

theorem isVariety₀_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ T.X Z := by
  intro E _ _ _ H Dw l Xo c T Z hF
  have hsm := smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, hdim, hl⟩ := GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := GlobalTheory.T.flagBundlePointFramesTriangular_component C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR
  have hiso := GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])
  rw [← hps, ← Category.assoc, hh, Category.assoc]

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_component_smooth_projective_connected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ T.X Z := by
  first | exact @GlobalTheory.VarFlag.isVariety₀_flag | exact GlobalTheory.VarFlag.isVariety₀_flag | (intros; apply GlobalTheory.VarFlag.isVariety₀_flag <;> assumption)
end
