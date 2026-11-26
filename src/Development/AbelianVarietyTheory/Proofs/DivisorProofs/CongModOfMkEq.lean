module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsLatticePart
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelMove

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)

section Identification

variable (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
  (oP : letI := H.starRing; P.toPre.OAct (𝓞 E))

end Identification

theorem exists_lattice_part {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 0 < n) (y : D.X) : ∃ p : QkPt D F n, p.y = y :=
  exists_qkPt GlobalTheory.abelianSchemeLaws_all.1.mulN (Or.inr GlobalTheory.abelianSchemeLaws_all.1.polBaseChange) hB hn.ne' y

end GlobalTheory.LevelMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportTorsionLabelsThetaSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportTorsionLabelsThetaSetup
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem galTransport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs
  obtain ⟨a, hG, hfix⟩ := GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ
  exact ⟨a, hfix, fun p _ z₁ c y h h' yy hL =>
    GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs a hG p z₁ c y h h' yy hL⟩

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportTorsionLabelsThetaSetupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transport_torsion_labels_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.galTransport | exact GlobalTheory.Poinc.galTransport | (intros; apply GlobalTheory.Poinc.galTransport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfCongMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Spread.noeth (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem GlobalTheory.Poinc.Spread.endo_id {R O : Type} [CommRing R] [CommRing O] [IsDomain O] (f : R →+* O)
    (hf : ∀ o : O, ∃ a b : R, f b ≠ 0 ∧ f b * o = f a) (σ : Sp O ⟶ Sp O) (h : σ ≫ spMap f = spMap f) : σ = 𝟙 _ := by
  obtain ⟨s, rfl⟩ := Spec.map_surjective σ
  rw [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hs : ∀ r, s.hom (f r) = f r := fun r => congrArg (fun g => g.hom r) h'
  have : s = 𝟙 _ := by
    ext o
    obtain ⟨a, b, hb, e⟩ := hf o
    have e2 := congrArg s.hom e
    rw [map_mul, hs, hs, ← e] at e2
    exact mul_left_cancel₀ hb e2
  rw [this, Spec.map_id]

theorem GlobalTheory.Poinc.Spread.sec {R₁ R₂ O M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing O] [IsDomain O] {P₁ : PolAV (Sp R₁)} {P₂ : PolAV (Sp R₂)} {f₁ : R₁ →+* O} {f₂ : R₂ →+* O} {e₁ : M → (P₁.A ⟶ P₁.A)} {e₂ : M → (P₂.A ⟶ P₂.A)} {t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)} {t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)}
    (hf : ∀ o : O, ∃ a b : R₁, f₁ b ≠ 0 ∧ f₁ b * o = f₁ a) (h : SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂) :
    ∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left := by
  obtain ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, ht⟩ := h
  refine ⟨P, b₁, b₂, h₁, h₂, l₁, l₂, he, fun x => ?_⟩
  obtain ⟨w, w₁, w₂⟩ := ht x
  refine ⟨w, GlobalTheory.Poinc.Spread.endo_id f₁ hf _ ?_, w₁, w₂⟩
  have := Over.w (t₁ x)
  rw [Category.assoc, ← h₁.1.w, ← Category.assoc, w₁, Category.assoc, this]
  exact Category.comp_id _

theorem GlobalTheory.Poinc.Spread.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  intro g n F W Z i X ε p _ z c c₀ hc R' fg frac hth hev ρ' ε' hS' hR' y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS'' hR'' y₁ hy₁ u u'
  set z' := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hz'
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z') := GlobalTheory.Poinc.Spread.noeth X.o₁ X.Ω₁ X.M z'
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z') := X.normal.isIntegrallyClosed_stalk z'
  haveI : IsIntegrallyClosed (X.M.O z') := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z')
  let ι' : R' →+* X.M.O z' := (Subalgebra.inclusion hR').toRingHom
  let ι'' : R'' →+* X.M.O z' := (Subalgebra.inclusion hR'').toRingHom
  have h0 := GlobalTheory.Poinc.SameComb.combine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS' hS''
  have h1 := GlobalTheory.Poinc.sameAt_of_generic (X.M.O z') X.Ω₁ _ _ _ _ _ _ ι' ι'' _ _ _ _ h0
  have hfr : ∀ o : X.M.O z', ∃ a b : R', ι' b ≠ 0 ∧ ι' b * o = ι' a := by
    intro o
    obtain ⟨a, ha, b, hb, e⟩ := frac (o : X.Ω₁)
    by_cases hb0 : b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : o = 0 := Subtype.ext (by simpa [hb0] using e)
      simp [this]
    · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      change b * (o : X.Ω₁) = a
      rw [e]; field_simp
  let v : X.M.O z' →+* PadicAlgCl p := RatModel.valHom (gPt p ≫ c.y) z' (RatModel.range_eq_singleton _ _)
  have e₀ : v.comp ι' = y₀ := RingHom.ext fun a => (hy₀ a).symm
  have e₁ : v.comp ι'' = y₁ := RingHom.ext fun a => (hy₁ a).symm
  obtain ⟨P₀, a, a', ha, ha', hL, hL', ht, hε⟩ := GlobalTheory.Poinc.Special.main _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.Poinc.Spread.sec hfr h1) v u.yK u'.yK
    (u.fac.trans e₀.symm) (u'.fac.trans e₁.symm) u.A u'.A u.φ u'.φ u.cart u'.cart u.lb u'.lb
  refine ⟨P₀, a, a', ha, ha', hL, hL', fun b => ?_, fun E w w₂ hw hw₂ h => ?_⟩
  · obtain ⟨w, hw, h₁, h₂⟩ := ht b
    have q₁ : (w ≫ a) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha.1.w, ← Category.assoc, hw, Category.id_comp]
    have q₂ : (w ≫ a') ≫ u'.A.A.hom = jFK (R := u'.V) (PadicAlgCl p) := by
      rw [Category.assoc, ha'.1.w, ← Category.assoc, hw, Category.id_comp]
    refine ⟨w, Over.homMk (w ≫ a) q₁, Over.homMk (w ≫ a') q₂, hw, rfl, rfl, ?_, ?_⟩
    · simpa [e₀] using h₁
    · simpa [e₁] using h₂
  · exact hε E w w₂ hw hw₂ h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  first | exact @GlobalTheory.Poinc.Spread.main | exact GlobalTheory.Poinc.Spread.main | (intros; apply GlobalTheory.Poinc.Spread.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndoPt

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (T : Over S') :
    ∃ E : (T ⟶ G') ≃* (Over.mk (T.hom ≫ g) ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ g) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ g
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have inj : Function.Injective F := fun x y e => by
    apply Over.OverMorphism.ext
    refine h.1.hom_ext ?_ ?_
    · rw [← hF, ← hF, e]
    · rw [Over.w x, Over.w y]
  have sur : Function.Surjective F := fun z => by
    have w : z.left ≫ G.hom = T.hom ≫ g := Over.w z
    refine ⟨Over.homMk (h.1.lift z.left T.hom w) (h.1.lift_snd _ _ w), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ w
  refine ⟨{ Equiv.ofBijective F ⟨inj, sur⟩ with map_mul' := fun x y => ?_ }, hF⟩
  apply Over.OverMorphism.ext
  exact (h.2 T x y (F x) (F y) rfl rfl).symm

theorem exists_point_of_isMonHom {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (f : G ⟶ G) [IsMonHom f] (m : ℕ) {T : Over S'}
    (x : T ⟶ G') (hx : x ^ m = 1) :
    ∃ x₂ : T ⟶ G', x₂.left ≫ φ = x.left ≫ φ ≫ f.left ∧ x₂ ^ m = 1 := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points h T
  refine ⟨E.symm (E x ≫ f), ?_, ?_⟩
  · rw [← hE, MulEquiv.apply_symm_apply, Over.comp_left, hE, Category.assoc]
  · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hx, map_one, MonObj.one_comp, map_one]

theorem exists_endo_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u f hf m x hx
  exact exists_point_of_isMonHom u.cart f m x hx

end GlobalTheory.EndoPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  first | exact @GlobalTheory.EndoPt.exists_endo_point | exact GlobalTheory.EndoPt.exists_endo_point | (intros; apply GlobalTheory.EndoPt.exists_endo_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GeomCore

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in
theorem core : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x ν, yy x = QuotientAddGroup.mk ν → yy' x = QuotientAddGroup.mk (θ ν)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  intro g n F W Z i X ε hd p _ z c yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩ := GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → (∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have ord : ∀ m pk (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
      x ^ m = 1 := fun m pk x h => by
    obtain ⟨w, hw⟩ := u.U.ext
    exact (h w hw).1
  have hqe : ∀ χ, l'.q (e χ) = l.q χ := fun χ => by
    have h2 := (hψ χ _).1 (l.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ →
      l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := (tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := (tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')
    have e1 := l.yy_eq b pk x hpk hx
    have e2 := l'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  have hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X,
      CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ))) := fun m hm E χ => by
    obtain ⟨pk, rfl⟩ := GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ
    obtain ⟨x, hQ⟩ := (tors m hm).2 pk
    obtain ⟨w, x', hw, hwa, hwa', hx'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)
    obtain ⟨pk', hQ'⟩ := (tors' m hm).1 x' hx'
    have hmon := GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E
    obtain ⟨x₂, hx₂φ, hx₂⟩ := GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)
    obtain ⟨pk₂, hQ₂⟩ := (tors m hm).1 x₂ hx₂
    obtain ⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂
    obtain ⟨pk₂', hQ₂'⟩ := (tors' m hm).1 x₂' hx₂'
    have hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left := by
      have := hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])
      rw [← hw₂a', ← hwa']
      simpa only [Category.assoc] using this
    have c1 := hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ
    have c2 := hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂
    have t1 := htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'
    have t2 := htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'
    refine ⟨pk₂.y, c1, ?_⟩
    exact cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2))
      (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have h1 := hq χ
    have h2 := hq' (e χ)
    rw [hqe] at h2
    have hs := c.scale_pos
    have h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hs.ne' (h2.symm.trans h1)
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (l'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))
  · intro m hm E v
    obtain ⟨χ, rfl⟩ := j.surjective v
    obtain ⟨χ₂, c1, c2⟩ := hcom m hm E χ
    have c3 : CongMod m (j.symm (matAct E (j χ))) χ₂ := by
      simpa using cm_symm (cm_map j.symm.toAddMonoidHom c1)
    have c4 := cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2
    simpa [matAct] using c4

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := core

end GlobalTheory.GeomCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qW_automorphism_eighthPower_lattice_labels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  first | exact @GlobalTheory.GeomCore.main | exact GlobalTheory.GeomCore.main | (intros; apply GlobalTheory.GeomCore.main <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LabUniq

section Lin
variable {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem eq_of_congMod (x y : M) (h : ∀ m : ℕ, 1 ≤ m → CongMod m x y) : x = y := by
  let b := Module.Free.chooseBasis ℤ M
  rw [← sub_eq_zero]
  apply b.repr.injective
  ext k
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (b.repr (x - y) k).natAbs + 1 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := h N (by omega)
  have hxy : x - y = N • w := by rw [hw]; abel
  have h2 : b.repr (x - y) k = (N : ℤ) * b.repr w k := by
    rw [hxy, map_nsmul]; simp [nsmul_eq_mul]
  refine Int.eq_zero_of_abs_lt_dvd ⟨_, h2⟩ ?_
  rw [Int.abs_eq_natAbs]; omega

end Lin

section Diag
variable {Y : Type} [AddCommGroup Y]

theorem act_unit (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

end Diag

theorem qW_single {Y : Type} [AddCommGroup Y] (W : Matrix (Fin 8) (Fin 8) ℤ) (β : LinearMap.BilinForm ℤ Y) (y : Y) :
    qW W β (Pi.single 0 y) = W 0 0 * β y y := by
  unfold qW
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ κ : c.T.D.toPre.X ≃+ c.T.D.toPre.X, (∀ a b, c.T.β (κ a) (κ b) = c.T.β a b) ∧ ∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (fun a => κ (μ a)) := by
  intro g n F W Z i X ε hdiag p _ z c yy yy' h1 h2
  obtain ⟨θ, hq, hl, hE⟩ := GlobalTheory.T.exists_qW_automorphism_eighthPower_lattice_labels g n F W Z i X ε hdiag p z c yy yy' h1 h2
  have hc : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b :=
    fun E v => eq_of_congMod _ _ fun m hm => hE m hm E v
  let κ0 : c.T.D.toPre.X →+ c.T.D.toPre.X :=
    (Pi.evalAddMonoidHom (fun _ : Fin 8 => c.T.D.toPre.X) 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => c.T.D.toPre.X) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ hc v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  let κ := AddEquiv.ofBijective κ0 ⟨inj, surj⟩
  have hκ : ∀ x, κ x = κ0 x := fun x => rfl
  have hd : ∀ x, c.T.β (κ0 x) (κ0 x) = c.T.β x x := by
    intro x
    have := hq (Pi.single 0 x)
    rw [hsingle, qW_single, qW_single] at this
    exact mul_left_cancel₀ (X.diag_pos 0).ne' this
  refine ⟨κ, ?_, ?_⟩
  · intro a b
    rw [hκ, hκ]
    have hab := hd (a + b)
    simp only [map_add (f := _), LinearMap.map_add₂, LinearMap.add_apply] at hab
    have s1 := c.T.symm (κ0 a) (κ0 b)
    have s2 := c.T.symm a b
    have ha := hd a
    have hb := hd b
    linarith
  · intro x μ h
    rw [hl x μ h]
    congr 1
    funext a
    exact hθ μ a

end GlobalTheory.Poinc.LabUniq
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalLab

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem three_le_level (X₁ : Setup F W i) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem isLab_onto (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X))
    (h : IsLab X ε c yy) (μ : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) : ModN m (Fin 8 → X)) =
      QuotientAddGroup.mk (fun b => κ ((d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) b))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  have hw0 := congrFun hw 0
  simp only [nsmulAddMonoidHom_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same,
    map_nsmul] at hw0
  refine ⟨w 0, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w 0) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw0, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

theorem rigid {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)
    {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (h₁ : IsLab X₁ ε₁ c yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))
    (hl : IsLab D.X D.ε (D.lift c y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : IsLab D.X D.ε (D.lift c y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := LabUniq.main g n F W Z i D.X D.ε D.diag p (y (cPt p)) (D.lift c y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := isLab_onto X₁ ε₁ c yy₁ h₁ (Pi.single 0 x)
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  let e : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X := κ.toIntLinearEquiv
  have he : e = LinearEquiv.refl ℤ _ :=
    eq_refl_of_isometry_congMod _ c.T.β (fun x hx => Trait.beta_pos g n _ _ F c.T x hx) e hκβ _
      (three_le_level X₁) hcong
  have hκ1 : ∀ x, κ x = x := fun x => by
    have := congrArg (fun f : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X => f x) he
    simpa [e] using this
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ]
  simp [hκ1]

end GlobalTheory.Poinc.GalLab

theorem GlobalTheory.Poinc.GalLab.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  obtain ⟨a, hfix, htr⟩ := GlobalTheory.T.galois_transport_torsion_labels_thetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ c yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ c y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GalLab.rigid D c yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact (DFunLike.congr_fun this x)
