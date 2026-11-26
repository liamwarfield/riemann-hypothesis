module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrix
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeTransform
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelation

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeries
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap

open Formalism.MainNotions.ModuliIntegralCharts.H1

section Jets

variable {k : Type} [CommRing k]

theorem exists_jetMap {κ κ' : Type} {m : ℕ} (χ : Jet k κ m →ₐ[k] Jet k κ' m)
    (h : ∀ q, (jetAug : Jet k κ' m →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) :
    ∃ (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ'), χ = jetMap φ hφ := by
  choose P hP using fun q => Ideal.Quotient.mk_surjective (χ (Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.X q)))
  have hc : ∀ q, MvPolynomial.constantCoeff (P q) = 0 := fun q => by
    have e : (jetAug : Jet k κ' m →ₐ[k] k) (Ideal.Quotient.mk _ (P q)) = 0 := by rw [hP]; exact h q
    have e' : (MvPolynomial.aeval (fun _ : κ' => (0 : k))) (P q) = 0 := e
    rwa [MvPolynomial.aeval_zero'] at e'
  have hm : ∀ q, P q ∈ orig k κ' := fun q => by
    have := sub_const_mem_orig (P q)
    rwa [hc q, map_zero, sub_zero] at this
  refine ⟨P, hm, GermD.jet_hom_ext fun q => ?_⟩
  rw [GermD.jetMap_mk, MvPolynomial.aeval_X, hP]

end Jets

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem fibPt_fst {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

theorem fibPt_snd {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.snd t.G.hom x = spMap (algebraMap k A) :=
  (pullback.lift_snd _ _ _).trans (by simp)

theorem homAt_fibPt {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (y : overAt x A ⟶ t.G) : homAt (𝟙 (Sp k)) f ≫ fibPt t x y = fibPt t x (homAt x f ≫ y) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_fst, fibPt_fst]
    rfl
  · rw [Over.comp_left, Category.assoc]
    erw [fibPt_snd, fibPt_snd]
    exact spMap_comp_alg f

theorem one_left_fst {T : Over (Sp k)} :
    (1 : T ⟶ GF t x).left ≫ pullback.fst t.G.hom x = T.hom ≫ x ≫ η[t.G].left := by
  rw [Hom.one_def, Over.comp_left, Category.assoc]
  have e : η[(Over.pullback x).obj t.G].left ≫ pullback.fst t.G.hom x = x ≫ η[t.G].left := by
    rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
      ← pullback.condition_assoc]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  erw [e]
  rfl

theorem fibPt_one {A : Type} [CommRing A] [Algebra k A] : fibPt t x (1 : overAt x A ⟶ t.G) = 1 := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · erw [fibPt_fst, one_left_fst]
    rw [Hom.one_def, Over.comp_left]
    simp
  · erw [fibPt_snd]
    have := Over.w (1 : overAt (𝟙 (Sp k)) A ⟶ GF t x)
    simpa using this.symm

end Fibre

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {x : Sp k ⟶ X}

theorem q_one (Q : AbQuot t x) {T : Over (Sp k)} : (1 : T ⟶ GF t x) ≫ Q.q = 1 := by
  have := Q.q_hom
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

theorem chart_trunc {S : Type} [CommRing S] {Y : Scheme.{0}} {G : Over Y} (x₀ : Sp S ⟶ Y) {d e : ℕ}
    (gx : ∀ m, jOG x₀ e m 1 ⟶ G)
    (htr : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) ≫ gx (m + 1) = gx m)
    (y : ∀ m, overAt x₀ (Jet S (Fin 1 × Fin d) m) ⟶ G)
    (hy : ∀ m, homAt x₀ (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ y (m + 1) = y m)
    (χ : ∀ m, Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m)
    (hz : ∀ m q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (χ m (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0)
    (hχ : ∀ m, y m = homAt x₀ (χ m) ≫ gx m)
    (hu : ∀ m (ψ : Jet S (Fin 1 × Fin e) m →ₐ[S] Jet S (Fin 1 × Fin d) m),
      (∀ q, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) →
        y m = homAt x₀ ψ ≫ gx m → ψ = χ m) (m : ℕ) (q : Fin 1 × Fin e) :
    (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)
      (χ (m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X q))) = χ m (Ideal.Quotient.mk _ (MvPolynomial.X q)) := by
  obtain ⟨φ, hφ, e₁⟩ := exists_jetMap (χ (m + 1)) (hz (m + 1))
  have hcomm : (jetMap (m := m) φ hφ).comp
      (jetTrunc : Jet S (Fin 1 × Fin e) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin e) m) =
      (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m).comp (χ (m + 1)) := by
    rw [e₁]
    exact GermD.jet_hom_ext fun i => rfl
  have hψ : jetMap (m := m) φ hφ = χ m := by
    refine hu m _ (fun q => ?_) ?_
    · have h := hz (m + 1) q
      rw [e₁] at h
      exact h
    · rw [← hy m, hχ (m + 1), ← htr m, ← Category.assoc, ← Category.assoc, GermD.homAt_comp, GermD.homAt_comp, hcomm]
  rw [← hψ]
  exact (AlgHom.congr_fun hcomm _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  intro E _ _ _ H _ hst X t k _ _ p _ _ x Q d d' g gB
  have hy₀ : ∀ m, homAt (𝟙 (Sp k)) (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ (fibPt t x (g.x m) ≫ Q.q) = 1 := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.zero m, fibPt_one, q_one]
  have hy₁ : ∀ m, homAt (𝟙 (Sp k)) (jetTrunc : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m) ≫
      (fibPt t x (g.x (m + 1)) ≫ Q.q) = fibPt t x (g.x m) ≫ Q.q := fun m => by
    rw [← Category.assoc, homAt_fibPt, g.chart.trunc m]
  choose χ hχ hu using fun m =>
    (GlobalTheory.T.formal_germ_dimension_unique E H hst (Sp k) Q.tB k (𝟙 (Sp k)) d' gB).2 (Fin 1 × Fin d) m _ (hy₀ m)
  have hc := chart_trunc (𝟙 (Sp k)) gB.x gB.chart.trunc (fun m => fibPt t x (g.x m) ≫ Q.q) hy₁ χ
    (fun m => (hχ m).1) (fun m => (hχ m).2) (fun m ψ h₁ h₂ => hu m ψ ⟨h₁, h₂⟩)
  choose Qs hQs using fun i : Fin d' => GaugeR.exists_ps_of_compat
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => hc m _)
  have hconst : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0 := fun i => by
    rw [← GaugeR.jetAug_psJet 0 (Qs i), hQs i 0]
    exact (hχ 0).1 _
  refine ⟨Qs, hconst, fun m => ?_⟩
  have he : sub1 Qs m = χ m := by
    refine GermD.jet_hom_ext fun q => ?_
    obtain ⟨a, i⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have h0 : MvPolynomial.constantCoeff (psTrunc m (Qs i)) = 0 := by
      rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp)]
      exact hconst i
    rw [← hQs i m, sub1, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X, h0, map_zero, sub_zero]
    rfl
  rw [he]
  exact (hχ m).2

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_germ_power_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxes
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

abbrev pb {A C : Scheme.{0}} (f : A ⟶ C) : Γ(C, ⊤)ˣ →* Γ(A, ⊤)ˣ := Units.map f.appTop.hom.toMonoidHom

theorem pb_comp {A C D : Scheme.{0}} (f : A ⟶ C) (g : C ⟶ D) (w : Γ(D, ⊤)ˣ) :
    pb (f ≫ g) w = pb f (pb g w) :=
  Units.ext (Rosenlicht.appTop_comp_apply f g w.val)

theorem pb_id {A : Scheme.{0}} (w : Γ(A, ⊤)ˣ) : pb (𝟙 A) w = w :=
  Units.ext (by simp)

variable {S : Scheme.{0}}

section Whisker

variable {X Y : Over S} (f : X ⟶ Y) (Z : Over S)

theorem isPullback_whiskerRight :
    IsPullback (f ▷ Z).left (fst X Z).left (fst Y Z).left f.left := by
  have h1 : IsPullback (fst Y Z).left (snd Y Z).left Y.hom Z.hom := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst X Z).left (snd X Z).left X.hom Z.hom := IsPullback.of_hasPullback _ _
  have e1 : (f ▷ Z).left ≫ (snd Y Z).left = (snd X Z).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e2 : (f ▷ Z).left ≫ (fst Y Z).left = (fst X Z).left ≫ f.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  refine IsPullback.of_right (t := h1.flip) ?_ e2
  rw [e1, Over.w f]
  exact h2.flip

theorem isPullback_whiskerLeft :
    IsPullback (Z ◁ f).left (snd Z X).left (snd Z Y).left f.left := by
  have h1 : IsPullback (fst Z Y).left (snd Z Y).left Z.hom Y.hom := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst Z X).left (snd Z X).left Z.hom X.hom := IsPullback.of_hasPullback _ _
  have e1 : (Z ◁ f).left ≫ (fst Z Y).left = (fst Z X).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e2 : (Z ◁ f).left ≫ (snd Z Y).left = (snd Z X).left ≫ f.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  refine IsPullback.of_right (t := h1) ?_ e2
  rw [e1, Over.w f]
  exact h2

end Whisker

theorem pb_act_eq {Ch : Type} [AddCommGroup Ch] [Module.Free ℤ Ch] (W : Over S) [IsIntegral W.left]
    (a : splitTorus S Ch ⊗ W ⟶ W) (ha : lift (1 : W ⟶ splitTorus S Ch) (𝟙 W) ≫ a = 𝟙 W)
    (e : splitTorus S Ch ⟶ W) (u : Γ(W.left, ⊤)ˣ)
    (h₁ : pb (lift (𝟙 _) e ≫ a).left u = 1) (h₂ : pb e.left u = 1) :
    pb a.left u = pb (snd (splitTorus S Ch) W).left u := by
  set ρ := pb a.left u * (pb (snd (splitTorus S Ch) W).left u)⁻¹ with hρ
  have hu : pb (GlobalTheory.BiextTriv.unitSec Ch W) ρ = 1 := by
    have c1 : pb (GlobalTheory.BiextTriv.unitSec Ch W) (pb a.left u) = u := by
      rw [← pb_comp, GlobalTheory.BiextTriv.unitSec, ← Over.comp_left, ha, Over.id_left, pb_id]
    have c2 : pb (GlobalTheory.BiextTriv.unitSec Ch W) (pb (snd (splitTorus S Ch) W).left u) = u := by
      rw [← pb_comp, GlobalTheory.BiextTriv.unitSec, ← Over.comp_left, lift_snd, Over.id_left, pb_id]
    rw [hρ, map_mul, map_inv, c1, c2, mul_inv_cancel]
  obtain ⟨χ, hχ⟩ := GlobalTheory.BiextTriv.exists_char (X := Ch) (Y := W) ρ (congrArg Units.val hu)
  have hχ' : ρ = pb (fst (splitTorus S Ch) W).left (charUnit S Ch χ) := Units.ext hχ
  have hc : charUnit S Ch χ = 1 := by
    have c0 : pb (lift (𝟙 _) e).left ρ = charUnit S Ch χ := by
      rw [hχ', ← pb_comp, ← Over.comp_left, lift_fst, Over.id_left, pb_id]
    rw [← c0, hρ, map_mul, map_inv, ← pb_comp, ← pb_comp, ← Over.comp_left, ← Over.comp_left, lift_snd, h₁, h₂]
    simp
  rw [hc, map_one] at hχ'
  exact mul_inv_eq_one.1 (hρ.symm.trans hχ')

section Orbit

variable {G B : Over S} [GrpObj G] [GrpObj B] {T : Over S} [GrpObj T]

theorem exists_orbit (q : G ⟶ B) [IsMonHom q] (i : T ⟶ G) (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : ∃ s : Z ⟶ T, g' = g * (s ≫ i) := by
  have e : (g⁻¹ * g') ≫ q = toUnit Z ≫ η := by
    rw [MonObj.mul_comp, ← h, ← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp, Hom.one_def]
  refine ⟨hk.lift (g⁻¹ * g') (toUnit Z) e, ?_⟩
  rw [hk.lift_fst, mul_inv_cancel_left]

end Orbit

section Act

variable {G T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj T]

def act₁ (i : T ⟶ G) : T ⊗ (G ⊗ G) ⟶ G ⊗ G :=
  lift ((snd T (G ⊗ G) ≫ fst G G) * (fst T (G ⊗ G) ≫ i)) (snd T (G ⊗ G) ≫ snd G G)

def act₂ (i : T ⟶ G) : T ⊗ (G ⊗ G) ⟶ G ⊗ G :=
  lift (snd T (G ⊗ G) ≫ fst G G) ((snd T (G ⊗ G) ≫ snd G G) * (fst T (G ⊗ G) ≫ i))

theorem lift_act₁ (i : T ⟶ G) {Z : Over S} (s : Z ⟶ T) (y : Z ⟶ G ⊗ G) :
    lift s y ≫ act₁ i = lift ((y ≫ fst G G) * (s ≫ i)) (y ≫ snd G G) := by
  simp [act₁, MonObj.comp_mul]

theorem lift_act₂ (i : T ⟶ G) {Z : Over S} (s : Z ⟶ T) (y : Z ⟶ G ⊗ G) :
    lift s y ≫ act₂ i = lift (y ≫ fst G G) ((y ≫ snd G G) * (s ≫ i)) := by
  simp [act₂, MonObj.comp_mul]

end Act

section Act2

variable {G T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G) [IsMonHom i]

theorem act₁_unit : lift (1 : G ⊗ G ⟶ T) (𝟙 _) ≫ act₁ i = 𝟙 _ := by
  rw [lift_act₁]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]

theorem act₂_unit : lift (1 : G ⊗ G ⟶ T) (𝟙 _) ≫ act₂ i = 𝟙 _ := by
  rw [lift_act₂]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]

theorem act₁_axis : lift (𝟙 T) (1 : T ⟶ G ⊗ G) ≫ act₁ i = i ≫ lift (𝟙 G) (1 : G ⟶ G) := by
  rw [lift_act₁]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]

theorem act₂_axis : lift (𝟙 T) (1 : T ⟶ G ⊗ G) ≫ act₂ i = i ≫ lift (1 : G ⟶ G) (𝟙 G) := by
  rw [lift_act₂]
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]

end Act2

section Main

variable {G B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B] {Ch : Type} [AddCommGroup Ch] [Module.Free ℤ Ch]

theorem exists_descent (q : G ⟶ B) [IsMonHom q] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (i : splitTorus S Ch ⟶ G) [IsMonHom i] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    [IsIntegral (G ⊗ G).left] (u : Γ((G ⊗ G).left, ⊤)ˣ)
    (h0 : pb (lift (1 : G ⟶ G) (𝟙 G)).left u = 1) (h1 : pb (lift (𝟙 G) (1 : G ⟶ G)).left u = 1) :
    ∃ c : Γ((B ⊗ B).left, ⊤), (lift (fst G G ≫ q) (snd G G ≫ q)).left.appTop.hom c = u.val := by
  have e₀ : pb (1 : splitTorus S Ch ⟶ G ⊗ G).left u = 1 := by
    have : (1 : splitTorus S Ch ⟶ G ⊗ G) = (1 : splitTorus S Ch ⟶ G) ≫ lift (1 : G ⟶ G) (𝟙 G) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp, MonObj.comp_one]
    rw [this, Over.comp_left, pb_comp, h0, map_one]
  have i₁ : pb (act₁ i).left u = pb (snd (splitTorus S Ch) (G ⊗ G)).left u := by
    refine pb_act_eq (G ⊗ G) (act₁ i) (act₁_unit i) 1 u ?_ e₀
    rw [act₁_axis, Over.comp_left, pb_comp, h1, map_one]
  have i₂ : pb (act₂ i).left u = pb (snd (splitTorus S Ch) (G ⊗ G)).left u := by
    refine pb_act_eq (G ⊗ G) (act₂ i) (act₂_unit i) 1 u ?_ e₀
    rw [act₂_axis, Over.comp_left, pb_comp, h0, map_one]
  have j₁ : ∀ {Z : Over S} (s : Z ⟶ splitTorus S Ch) (y : Z ⟶ G ⊗ G),
      pb (lift s y ≫ act₁ i).left u = pb y.left u := fun s y => by
    rw [Over.comp_left, pb_comp, i₁, ← pb_comp, ← Over.comp_left, lift_snd]
  have j₂ : ∀ {Z : Over S} (s : Z ⟶ splitTorus S Ch) (y : Z ⟶ G ⊗ G),
      pb (lift s y ≫ act₂ i).left u = pb y.left u := fun s y => by
    rw [Over.comp_left, pb_comp, i₂, ← pb_comp, ← Over.comp_left, lift_snd]
  let qo : G ⊗ G ⟶ B ⊗ B := lift (fst G G ≫ q) (snd G G ≫ q)
  have hfac : qo = (q ▷ G) ≫ (B ◁ q) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [qo]
  let r := qo.left
  have hr : r = (q ▷ G).left ≫ (B ◁ q).left := by
    simp only [r]; rw [hfac, Over.comp_left]
  have : Flat (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : Flat (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : Surjective (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : Surjective (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : QuasiCompact (q ▷ G).left := MorphismProperty.of_isPullback (isPullback_whiskerRight q G).flip ‹_›
  have : QuasiCompact (B ◁ q).left := MorphismProperty.of_isPullback (isPullback_whiskerLeft q B).flip ‹_›
  have : Flat r := by rw [hr]; infer_instance
  have : Surjective r := by rw [hr]; infer_instance
  have : QuasiCompact r := by rw [hr]; infer_instance
  have hp := IsPullback.of_hasPullback r r
  have hW : r ≫ (B ⊗ B).hom = (G ⊗ G).hom := Over.w qo
  let P : Over S := Over.mk (pullback.fst r r ≫ (G ⊗ G).hom)
  let g : P ⟶ G ⊗ G := Over.homMk (pullback.fst r r) rfl
  let g' : P ⟶ G ⊗ G := Over.homMk (pullback.snd r r) (by
    show pullback.snd r r ≫ (G ⊗ G).hom = pullback.fst r r ≫ (G ⊗ G).hom
    rw [← hW, pullback.condition_assoc])
  have hq : g ≫ qo = g' ≫ qo := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hq₁ : (g ≫ fst G G) ≫ q = (g' ≫ fst G G) ≫ q := by
    have := congrArg (· ≫ fst B B) hq
    simpa [qo] using this
  have hq₂ : (g ≫ snd G G) ≫ q = (g' ≫ snd G G) ≫ q := by
    have := congrArg (· ≫ snd B B) hq
    simpa [qo] using this
  obtain ⟨s₁, hs₁⟩ := exists_orbit q i hk _ _ hq₁
  obtain ⟨s₂, hs₂⟩ := exists_orbit q i hk _ _ hq₂
  have hg' : g' = lift s₂ (lift s₁ g ≫ act₁ i) ≫ act₂ i := by
    rw [lift_act₂, lift_act₁]
    apply CartesianMonoidalCategory.hom_ext
    · simpa using hs₁
    · simpa using hs₂
  have key : pb g'.left u = pb g.left u := by
    rw [hg', j₂, j₁]
  obtain ⟨c, hc, -⟩ := (GlobalTheory.FlatDescent.existsUnique_appTop_eq_iff r hp u.val).2
    (congrArg Units.val key).symm
  exact ⟨c, hc⟩

theorem unit_eq_one (q : G ⟶ B) [IsMonHom q] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (i : splitTorus S Ch ⟶ G) [IsMonHom i] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B))
    [IsIntegral (G ⊗ G).left] (hB : Function.Surjective (B ⊗ B).hom.appTop.hom) (u : Γ((G ⊗ G).left, ⊤)ˣ)
    (h0 : pb (lift (1 : G ⟶ G) (𝟙 G)).left u = 1) (h1 : pb (lift (𝟙 G) (1 : G ⟶ G)).left u = 1) : u = 1 := by
  obtain ⟨c, hc⟩ := exists_descent q i hk u h0 h1
  obtain ⟨b, rfl⟩ := hB c
  have hw : (lift (fst G G ≫ q) (snd G G ≫ q)).left ≫ (B ⊗ B).hom = (G ⊗ G).hom :=
    Over.w (lift (fst G G ≫ q) (snd G G ≫ q))
  rw [← Rosenlicht.appTop_comp_apply, hw] at hc
  have hv : (lift (1 : G ⟶ G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w (lift (1 : G ⟶ G) (𝟙 G))
  have hs : (η : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w (η : 𝟙_ (Over S) ⟶ G)
  have hb : b = 1 := by
    have e1 := congrArg Units.val h0
    simp only [Units.coe_map, Units.val_one] at e1
    have e2 : (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom ((G ⊗ G).hom.appTop.hom b) = 1 := by
      rw [hc]; exact e1
    rw [← Rosenlicht.appTop_comp_apply, hv] at e2
    have e3 := congrArg (η : 𝟙_ (Over S) ⟶ G).left.appTop.hom e2
    rw [← Rosenlicht.appTop_comp_apply, hs, map_one] at e3
    simpa using e3
  apply Units.ext
  rw [← hc, hb, map_one, Units.val_one]

end Main

theorem unit_eq_one_of_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (_ : AbQuot t x) (d : ℕ) (_ : GermAt t x d) (u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ), (ax0 t x).appTop.hom u.val = 1 → (ax1 t x).appTop.hom u.val = 1 → u = 1 := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d _ u h0 h1
  have hs : IsSemiAbelian (GF t x) := IsSemiAbelian.pullback x t.G t.semi
  have := hs.smooth
  have := hs.geomConnected
  have := Q.proper
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surjective
  have := Q.q_quasiCompact
  obtain ⟨c₁, c₂⟩ := GlobalTheory.GroupConn.connectedSpace_group _ (GF t x)
  obtain ⟨-, c₄⟩ := c₂ Q.Ch (GF t x) c₁
  have : Smooth (GF t x ⊗ GF t x).hom := inferInstanceAs (Smooth (pullback.fst (GF t x).hom (GF t x).hom ≫ _))
  have : IsIntegral (GF t x ⊗ GF t x).left := isIntegral_of_smooth_field_of_connectedSpace (GF t x ⊗ GF t x).hom
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper Q.tB.G Q.tB.semi
  have hB := (GlobalTheory.globalFns_holds _ _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)).2
  exact unit_eq_one Q.q Q.i Q.isKernel hB u (Units.ext h0) (Units.ext h1)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitTrivialOnBothAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_trivial_on_both_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (_ : AbQuot t x) (d : ℕ) (_ : GermAt t x d) (u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ), (ax0 t x).appTop.hom u.val = 1 → (ax1 t x).appTop.hom u.val = 1 → u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.FibUnit.unit_eq_one_of_axes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (eXv eZ)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {d d' : ℕ}

theorem eval_first_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 0] φ = MvPowerSeries.rename (eXv d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem eval_second_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 1] φ = MvPowerSeries.rename (eZ d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem coeff_xz_rename (P Q : PS R 1 d) (a b : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1)
        (MvPowerSeries.rename (eXv d) P * MvPowerSeries.rename (eZ d) Q) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), a) 1) P *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), b) 1) Q := by
  classical
  have hA : ∀ u : Fin 2 × Fin d →₀ ℕ, u ((1 : Fin 2), b) ≠ 0 →
      MvPowerSeries.coeff u (MvPowerSeries.rename (eXv d) P) = 0 := by
    intro u hu
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hu
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hB : ∀ v : Fin 2 × Fin d →₀ ℕ, v ((0 : Fin 2), a) ≠ 0 →
      MvPowerSeries.coeff v (MvPowerSeries.rename (eZ d) Q) = 0 := by
    intro v hv
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hv
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (1 : Fin 2) = 0 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hne : ((0 : Fin 2), a) ≠ ((1 : Fin 2), b) := fun e => absurd (congrArg Prod.fst e) (by simp)
  have e0 : Finsupp.single ((0 : Fin 2), a) 1 = Finsupp.embDomain (eXv d) (Finsupp.single ((0 : Fin 1), a) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  have e1 : Finsupp.single ((1 : Fin 2), b) 1 = Finsupp.embDomain (eZ d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single
    (Finsupp.single ((0 : Fin 2), a) 1, Finsupp.single ((1 : Fin 2), b) 1)]
  · show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1) _ * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), b) 1) _ = _
    rw [e0, e1, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_embDomain_rename]
  · rintro ⟨u, v⟩ huv hne'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
    simp only at huv ⊢
    by_cases hu : u ((1 : Fin 2), b) = 0
    · by_cases hv : v ((0 : Fin 2), a) = 0
      · exfalso
        apply hne'
        have hv1 := DFunLike.congr_fun huv ((1 : Fin 2), b)
        have hu0 := DFunLike.congr_fun huv ((0 : Fin 2), a)
        simp only [Finsupp.add_apply, Finsupp.single_apply, hne, hne.symm, if_true, if_false, hu, hv] at hv1 hu0
        have hrest : ∀ t, t ≠ ((0 : Fin 2), a) → t ≠ ((1 : Fin 2), b) → u t = 0 ∧ v t = 0 := by
          intro t h0 h1
          have ht := DFunLike.congr_fun huv t
          simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm h0, Ne.symm h1, if_false] at ht
          omega
        refine Prod.ext (Finsupp.ext fun t => ?_) (Finsupp.ext fun t => ?_)
        · by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp; omega
          by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp [Finsupp.single_apply, hne.symm, hu]
          simp [Finsupp.single_apply, Ne.symm h0, (hrest t h0 h1).1]
        · by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp; omega
          by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp [Finsupp.single_apply, hne, hv]
          simp [Finsupp.single_apply, Ne.symm h1, (hrest t h0 h1).2]
      · rw [hB v hv, mul_zero]
    · rw [hA u hu, zero_mul]
  · intro h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact absurd rfl h

theorem const_side {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    (p : Fin 2 × Fin d') :
    MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d p.1] (Qs p.2)) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 0] (Qs i)) = 0
    rw [eval_first_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 1] (Qs i)) = 0
    rw [eval_second_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]

theorem subst_side {τ : Type} {b : Fin 2 × Fin d → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) (j : Fin 2)
    (φ : PS R 1 d) :
    MvPowerSeries.subst b (ev (n := 2) ![pt R d j] φ) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => b (j, q.2)) φ := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![pt R d j] q.1 q.2 : PS R 2 d)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨u, i⟩ := q
      fin_cases u
      exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply hs hb]
  congr 1
  funext q
  obtain ⟨u, i⟩ := q
  fin_cases u
  exact MvPowerSeries.subst_X hb _

theorem subst_one' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_one]

theorem subst_zero' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]

theorem ev_subQ_eq_one {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (A : Fin 2 → Pt R 1 d) (A' : Fin 2 → Pt R 1 d')
    (hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0) (hA' : ∀ j i, MvPowerSeries.constantCoeff (A' j i) = 0)
    (hc : ∀ j i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => A j q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (A' j i))
    (h : ev (n := 1) A' f = 1) : ev (n := 1) A (subQ Qs f) = 1 := by
  have hb : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => A p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA p.1 p.2
  have hb' : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => A' p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA' p.1 p.2
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have h1 := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2)) h
  unfold ev at h1
  rw [subst_one' hq, MvPowerSeries.subst_comp_subst_apply hb' hq] at h1
  unfold ev subQ
  rw [MvPowerSeries.subst_comp_subst_apply hσ hb, ← h1]
  congr 1
  funext p
  rw [subst_side hb, hc]

theorem axOne_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : AxOne (subQ Qs f) := by
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have hz : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => (0 : PS R 1 d)) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (0 : PS R 1 d') := fun i => by
    rw [subst_zero' hq]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hQ i)
  have hx : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => pt R d 0 q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (pt R d' 0 i) := fun i => by
    have e : (fun q : Fin 1 × Fin d => pt R d 0 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨u, l⟩ := q
      fin_cases u
      rfl
    rw [e, MvPowerSeries.subst_self]
    show _ = MvPowerSeries.subst _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d')
    rw [MvPowerSeries.subst_X hq]
    rfl
  have c0 : ∀ {n : ℕ} (i : Fin n), MvPowerSeries.constantCoeff (pt R (n := 1) n 0 i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_X _
  constructor
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.1
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact hz i
      · exact hx i
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.2
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact hx i
      · exact hz i

theorem bil_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  classical
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hA0 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![0, pt R d' 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact map_zero _
      · exact MvPowerSeries.constantCoeff_X _
  have hA1 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![pt R d' 0, 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact MvPowerSeries.constantCoeff_X _
      · exact map_zero _
  have h0 : ev (n := 1) ![0, pt R d' 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA0, subst_one' hA0]
    exact sub_eq_zero.2 hf.1
  have h1 : ev (n := 1) ![pt R d' 0, 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA1, subst_one' hA1]
    exact sub_eq_zero.2 hf.2
  ext a b
  have hdeg := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz a b
  have hn : (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1 : Fin 2 × Fin d →₀ ℕ) ≠ 0 := by
    intro e
    rw [e] at hdeg
    simp at hdeg
  have key := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz (f - 1) h0 h1 _ (const_side hQ) _ hdeg
  rw [MvPowerSeries.subst_sub hσ, subst_one' hσ, map_sub, MvPowerSeries.coeff_one, if_neg hn, sub_zero] at key
  show MvPowerSeries.coeff _ (subQ Qs f) = _
  refine key.trans ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  have hl : (Finsupp.single ((0 : Fin 2), l) 1 + Finsupp.single ((1 : Fin 2), m) 1 : Fin 2 × Fin d' →₀ ℕ) ≠ 0 := by
    intro e
    have hd := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz l m
    rw [e] at hd
    simp at hd
  have e0 : ev (n := 2) ![pt R d ((0 : Fin 2), l).1] (Qs ((0 : Fin 2), l).2) = MvPowerSeries.rename (eXv d) (Qs l) :=
    eval_first_point_eq_rename _
  have e1 : ev (n := 2) ![pt R d ((1 : Fin 2), m).1] (Qs ((1 : Fin 2), m).2) = MvPowerSeries.rename (eZ d) (Qs m) :=
    eval_second_point_eq_rename _
  rw [map_sub, MvPowerSeries.coeff_one, if_neg hl, sub_zero, e0, e1, coeff_xz_rename]
  show _ = linQ Qs l a * bil f 1 1 l m * linQ Qs m b
  simp only [linQ, bil]
  ring

theorem bil_axOne_subQ : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'),
    (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f →
      AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs :=
  fun _ _ _ _ _ _ hQ hf => ⟨axOne_subQ hQ hf, bil_subQ hQ hf⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransformStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_bilinear_form_transform : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'), (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f → AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinear
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

theorem frame_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  intro E _ _ _ H _ hstar X t k _ _ p _ _ x Q d d' g gB P hP
  obtain ⟨w, hw⟩ := Q.bun
  obtain ⟨Qs, hc, hQ⟩ := GlobalTheory.T.abelian_quotient_germ_power_series E H hstar X t k p x Q d d' g gB
  have hl := GlobalTheory.T.abelian_quotient_differential_matrix E H hstar X t k p x Q d d' g gB P hP Qs hc hQ
  obtain ⟨lam, hax, hlam⟩ := GlobalTheory.T.abelian_quotient_gauge_transform E H hstar X t k p x Q d d' g gB w hw Qs hc hQ
  refine ⟨bil lam 1 1, fun a => ?_⟩
  obtain ⟨wL, hwL, hrL⟩ := g.frame.ad a
  obtain ⟨wB, hwB, hrB⟩ := gB.frame.ad a
  obtain ⟨u, hu⟩ := GlobalTheory.T.abelian_quotient_line_bundle_gauge E H hstar X t k p x Q d d' g gB w hw a wL wB hwL hwB
  obtain ⟨h0, h1⟩ := GlobalTheory.T.abelian_quotient_gauge_unit E H hstar X t k p x Q d d' g gB w hw Qs hc hQ a wL wB hwL hwB hrL hrB u hu
  obtain rfl := GlobalTheory.T.unit_trivial_on_both_axes E H hstar X t k p x Q d g u h0 h1
  have hrel := GlobalTheory.T.abelian_quotient_gauge_relation E H hstar X t k p x Q d d' g gB w hw Qs hc hQ lam hlam a wL wB hwL hwB hrL hrB hu
  rw [← hstar a] at hrel
  obtain ⟨hA, hbA⟩ := GlobalTheory.T.substitution_bilinear_form_transform k d d' Qs (gB.B.ad a) hc ⟨gB.B.adjoint_zero_fst a, gB.B.adjoint_zero_snd a⟩
  have hadx : AxOne (g.B.ad a) := ⟨g.B.adjoint_zero_fst a, g.B.adjoint_zero_snd a⟩
  have hcs : ∀ (b : 𝓞 E) (i : Fin d), MvPowerSeries.constantCoeff (g.B.A.act b i) = 0 := fun b i => g.B.A.const b i
  have hp0 : ∀ i : Fin d, MvPowerSeries.constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => by simp [pt]
  have hp2 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (pt k (n := 2) d j i) = 0 := fun j i => by simp [pt]
  obtain ⟨-, -, -, hT, hbT, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (pt k d 0) (g.B.A.act (star a)) hax hax hp0 (hcs _)
  obtain ⟨-, -, -, hS, hbS, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d lam lam (g.B.A.act a) (pt k d 0) hax hax (hcs _) hp0
  rw [germ_comp1_zero_point_left _ (hp2 0)] at hT hbT
  rw [germ_comp1_zero_point_left _ (hp2 1)] at hS hbS
  obtain ⟨-, -, e1, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d (subQ Qs (gB.B.ad a)) _ (pt k d 0) (pt k d 0) hA hT hp0 hp0
  obtain ⟨-, -, e2, -⟩ := GlobalTheory.T.formal_bilinear_term_product k d _ (g.B.ad a) (pt k d 0) (pt k d 0) hS hadx hp0 hp0
  have h := congrArg (fun f => bil f 1 1) hrel
  beta_reduce at h
  rw [e1, e2, hbT, hbS, hbA, hl, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  change _ + (rho g.B a).transpose * _ - _ * rho g.B (star a) = _
  change _ + bil lam 1 1 * rho g.B (star a) = (rho g.B a).transpose * bil lam 1 1 + _ at h
  rw [eq_sub_of_add_eq h]
  abel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientBilinearStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_bilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ P : Matrix (Fin d') (Fin d) k, Q.IsDiff g gB P → ∃ Z : Matrix (Fin d) (Fin d) k, ∀ a, bil (g.B.ad a) 1 1 + (rho g.B a).transpose * Z - Z * rho g.B (star a) = P.transpose * bil (gB.B.ad a) 1 1 * P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.frame_gauge <;> assumption)
end
