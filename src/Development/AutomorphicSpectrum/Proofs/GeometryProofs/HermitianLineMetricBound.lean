module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionAt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhood
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhood
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ (W : X.Opens) (t : Γ(X, W)) (q : Cpt ξ) (hq : q.1 ∈ W) (hW : genPt ξ ∈ W) :
    genMap ξ q (X.presheaf.germ W q.1 hq t) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW t) := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 t)

theorem regAt_near {p : Cpt ξ} {a : Ω} (h : a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → a ∈ regAt ξ q := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨W, hp, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  have hW : genPt ξ ∈ W := p.2.mem_open W.isOpen hp
  refine ⟨W, hp, fun q hq => ⟨X.presheaf.germ W q.1 hq t, ?_⟩⟩
  rw [genMap_germ W t q hq hW, genMap_germ W t p hp hW]

theorem regAt_near_finset {p : Cpt ξ} (A : Finset Ω) (h : ∀ a ∈ A, a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ A, a ∈ regAt ξ q := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ ha => absurd ha (Finset.notMem_empty _)⟩
  | insert a A _ ih =>
    obtain ⟨W, hp, hW⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨W', hp', hW'⟩ := regAt_near (h a (Finset.mem_insert_self a A))
    refine ⟨W ⊓ W', ⟨hp, hp'⟩, fun q hq b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hW' q hq.2
    · exact hW q hq.1 b hb

theorem lie_near (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) (hG : SmoothOfRelativeDimension g G.hom)
    (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li)
    (hS : ∀ j, S j ∈ M.lat p) (hΦ : ∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  classical
  obtain ⟨U, hpU, b, -, hb⟩ := (GlobalTheory.T.lie_lattice_vector_bundle_of_smooth X G g Ω ξ Li M hξ hG).1 p (Set.mem_univ p)
  have hbp := (hb p (Set.mem_univ p) hpU).2
  have hc : ∀ j, ∃ c : Fin g → regAt ξ p, ∑ s, c s • b s = S j := fun j => by
    have := hS j
    rw [hbp] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose c hc using hc
  have hΦb : ∀ j s, Φ j (b s) ∈ regAt ξ p := fun j s =>
    hΦ j _ (by rw [hbp]; exact Submodule.subset_span ⟨s, rfl⟩)
  obtain ⟨W, hpW, hW⟩ := regAt_near_finset (ξ := ξ) (p := p)
    (Finset.univ.image (fun js : Fin n × Fin g => (c js.1 js.2 : Ω)) ∪
      Finset.univ.image (fun js : Fin n × Fin g => Φ js.1 (b js.2))) (by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact (c js.1 js.2).2
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact hΦb js.1 js.2)
  refine ⟨U ⊓ W, ⟨hpU, hpW⟩, fun q hq => ?_⟩
  have hbq := (hb q (Set.mem_univ q) hq.1).2
  have hcq : ∀ j s, (c j s : Ω) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  have hΦq : ∀ j s, Φ j (b s) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  refine ⟨fun j => ?_, fun j e he => ?_⟩
  · rw [hbq, ← hc j]
    refine Submodule.sum_mem _ fun s _ => ?_
    have : (c j s) • b s = (⟨c j s, hcq j s⟩ : regAt ξ q) • b s := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [hbq] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hΦq j s
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx =>
      have : Φ j (r • x) = (r : Ω) * Φ j x := by
        show Φ j ((r : Ω) • x) = _
        simp
      rw [this]
      exact mul_mem r.2 hx

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhoodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_sections_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li),
    IsCptGen ξ → SmoothOfRelativeDimension g G.hom →
    ∀ (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li),
      (∀ j, S j ∈ M.lat p) → (∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) →
      ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

section Frac

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem stalk_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ f g : Γ(X, U), IsUnit (X.presheaf.germ U p hp g) ∧
      s * X.presheaf.germ U p hp g = X.presheaf.germ U p hp f := by
  let : Algebra Γ(X, U) (X.presheaf.stalk p) := (X.presheaf.germ U p hp).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨f, g⟩, h⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl (S := X.presheaf.stalk p) s
  exact ⟨f, g, IsLocalization.map_units (X.presheaf.stalk p) g, h⟩

theorem genMap_germ_indep {U : X.Opens} {p q : Cpt ξ} (hp : p.1 ∈ U) (hq : q.1 ∈ U) (f : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp f) = genMap ξ q (X.presheaf.germ U q.1 hq f) := by
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  have key : ∀ r : Cpt ξ, ∀ hr : r.1 ∈ U, genMap ξ r (X.presheaf.germ U r.1 hr f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg f) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 f)
  rw [key p hp, key q hq]

theorem exists_frac {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) :
    ∃ (P Q : MvPolynomial κ ℤ) (t : X.presheaf.stalk p.1), IsUnit t ∧
      genMap ξ p t = MvPolynomial.aeval (fun j => x j / x c) Q ∧
      a * MvPolynomial.aeval (fun j => x j / x c) Q = MvPolynomial.aeval (fun j => x j / x c) P := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hp.1
  have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨f, g, hg, e⟩ := stalk_frac hU hpU s
  have hA : ∀ f : Γ(X, U), ∃ P : MvPolynomial κ ℤ, MvPolynomial.aeval (fun j => x j / x c) P =
      genMap ξ p (X.presheaf.germ U p.1 hpU f) := by
    intro f
    have hm : genMap ξ p (X.presheaf.germ U p.1 hpU f) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hp.1 _).2 fun q hq => ?_
      have hqU : q.1 ∈ U := (hmem q.1).2 ⟨q.2, hq⟩
      rw [genMap_germ_indep hpU hqU]
      exact ⟨_, rfl⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hm
    obtain ⟨P, hP⟩ := hm
    exact ⟨P, hP⟩
  obtain ⟨P, hP⟩ := hA f
  obtain ⟨Q, hQ⟩ := hA g
  refine ⟨P, Q, X.presheaf.germ U p.1 hpU g, hg, hQ.symm, ?_⟩
  rw [hP, hQ, ← map_mul, e]

end Frac

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X}

theorem val_intCast (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_finsetProd (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (a : I → Ω) (r : I → ℂ)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def ratioAt (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) (c' : (k : K) → J k) : ℂ :=
  ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_ratio {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (ratioAt c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_finsetProd hz _ _ _ fun k _ => ?_
  obtain ⟨-, h2⟩ := hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  obtain ⟨r, hr, e⟩ := h2 (c' k)
  rw [e, mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem val_ratioPoly {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ValAt ξ z (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P)
      (MvPolynomial.aeval (ratioAt c w) P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_intCast hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (val_ratio hz hw hc i)

theorem continuousAt_ratioAt {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (c' : (k : K) → J k) : ContinuousAt (fun w => ratioAt c w c') w₀ :=
  tendsto_finsetProd _ fun k _ =>
    ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_ratioPoly {w₀ : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0)
    (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (ratioAt c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_ratioAt hc i)

end Values

theorem val_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  intro X Ω _ ξ K _ J _ y hall hT z₀ w₀ h₀ a hw ha
  choose c hc using hw.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hch := in_chart h₀ hw hc'
  obtain ⟨P, Q, t, ht, hQ, hPQ⟩ := exists_frac hT hch ha
  have hvQ := val_ratioPoly (hall _) hw hc' Q
  have hvt : ValAt ξ z₀ (MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)
      ((Scheme.stalkClosedPointTo z₀).hom t) := ⟨h₀, t, hQ, rfl⟩
  have hne : MvPolynomial.aeval (ratioAt c w₀) Q ≠ 0 := by
    rw [val_unique hT.gen hvQ hvt]
    exact (ht.map (Scheme.stalkClosedPointTo z₀).hom).ne_zero
  have hQa : MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q ≠ (0 : Ω) := by
    rw [← hQ]
    exact (ht.map (genMap ξ _)).ne_zero
  have haeq : a = MvPolynomial.aeval
      (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P *
      (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) Q)⁻¹ := by
    rw [← hPQ, mul_inv_cancel_right₀ hQa]
  refine ⟨fun w => MvPolynomial.aeval (ratioAt c w) P / MvPolynomial.aeval (ratioAt c w) Q,
    (continuousAt_ratioPoly hc' P).div (continuousAt_ratioPoly hc' Q) hne,
    {w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (ratioAt c w) Q ≠ 0}, ?_, ?_⟩
  · have e1 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 w₀, ∀ k, w ⟨k, c k⟩ ≠ 0 :=
      eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
    exact e1.and ((continuousAt_ratioPoly hc' Q).eventually_ne hne)
  · rintro z w ⟨h1, h2⟩ hwz
    rw [haeq]
    show ValAt ξ z _ (_ / _)
    rw [div_eq_mul_inv]
    exact val_mul (val_ratioPoly (hall _) hwz h1 P) (val_inv₀ h2 (val_ratioPoly (hall _) hwz h1 Q))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_continuous_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoice
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem gen_chart_change (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ)
    (hξ : IsCptGen ξ) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (h₁ : ∀ k, w ⟨k, c₁ k⟩ ≠ 0) (hu : ValAt ξ z (τ / gen y a e₀ c₀) u)
    (hu' : ValAt ξ z (τ / gen y a e₀ c₁) u') :
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  classical
  obtain ⟨hz, -⟩ := val_spec hu
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (h₀ k))).1
  have hy₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0 := fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).1
  have hr : ∀ k, ∃ r : ℂ, ValAt ξ z (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) r ∧ w ⟨k, c₀ k⟩ = r * w ⟨k, c₁ k⟩ :=
    fun k => (hw.2 k (c₁ k) (isUnit_iff_ne_zero.2 (h₁ k))).2 (c₀ k)
  choose r hrv hrw using hr
  have hr0 : ∀ k, r k ≠ 0 := fun k hk => h₀ k (by rw [hrw k, hk, zero_mul])
  have hprod : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k) (∏ k ∈ s, r k ^ a k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using val_one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact val_mul (val_zpow (hr0 k) (hrv k) (a k)) ih
  have hg₀ : (∏ k, y ⟨k, c₀ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hg₁ : (∏ k, y ⟨k, c₁ k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₁ k)
  have hΩ : τ / gen y a e₀ c₁ = (τ / gen y a e₀ c₀) * ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k := by
    have : ∏ k, (y ⟨k, c₀ k⟩ / y ⟨k, c₁ k⟩) ^ a k = (∏ k, y ⟨k, c₀ k⟩ ^ a k) / ∏ k, y ⟨k, c₁ k⟩ ^ a k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => div_zpow _ _ _
    rw [this]
    unfold gen
    field_simp
  have hval : u' = u * ∏ k, r k ^ a k := by
    have h := val_mul hu (hprod Finset.univ)
    rw [← hΩ] at h
    exact val_unique hξ hu' h
  have hw₀ : ∏ k, w ⟨k, c₀ k⟩ ^ a k = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hrw k, mul_zpow]
  rw [hw₀, hval, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoiceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_at_gen_independent_choice : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ),
    IsCptGen ξ → e₀ ≠ 0 → CoordsAt ξ y z w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → (∀ k, w ⟨k, c₁ k⟩ ≠ 0) →
    ValAt ξ z (τ / gen y a e₀ c₀) u → ValAt ξ z (τ / gen y a e₀ c₁) u' →
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsNeighbourhoodInOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsNeighbourhoodInOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

namespace OpenNear

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {T : Type} (s : Finset T) {a : T → Ω} {r : T → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem val_aeval {κ : Type} {a : κ → Ω} {r : κ → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i, ValAt ξ z (a i) (r i)) (P : MvPolynomial κ ℤ) :
    ValAt ξ z (MvPolynomial.aeval a P) (MvPolynomial.aeval r P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_int hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (h i)

theorem genMap_germ {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) (p : Cpt ξ) (hp : p.1 ∈ W) :
    genMap ξ p (X.presheaf.germ W p.1 hp Q) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
  have h2 : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ W p.1 hp Q) =
      X.presheaf.germ W (genPt ξ) hW Q := by
    rw [← h]; rfl
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem isUnit_germ_iff (hξ : IsCptGen ξ) {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) {z : Sp ℂ ⟶ X}
    (hz : centre z ∈ W) {v : ℂ}
    (hv : ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q)) v) :
    IsUnit (X.presheaf.germ W (centre z) hz Q) ↔ v ≠ 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  have hs' : s = X.presheaf.germ W (centre z) hz Q :=
    hξ.inj ⟨centre z, h⟩ (hs.trans (genMap_germ hW Q ⟨centre z, h⟩ hz).symm)
  subst hs'
  have := Scheme.isLocalHom_stalkClosedPointTo' z
  constructor
  · exact fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero
  · exact fun hv => (isUnit_map_iff (Scheme.stalkClosedPointTo z).hom _).1 (isUnit_iff_ne_zero.2 hv)

def segreRatio {K : Type} [Fintype K] {J : K → Type} (c : (k : K) → J k) (w : (Σ k, J k) → ℂ)
    (c' : (k : K) → J k) : ℂ := ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_segreRatio {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X}
    {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_prod _ hz fun k _ => ?_
  obtain ⟨r, hr, hr'⟩ := (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).2 (c' k)
  rw [hr', mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem continuousAt_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ContinuousAt (fun w => segreRatio c w c') w₀ := by
  refine tendsto_finsetProd _ fun k _ => ?_
  exact ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_aeval_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (segreRatio c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_segreRatio hc i)

end OpenNear


open OpenNear in
theorem open_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (U : X.Opens), CoordsAt ξ y z₀ w₀ → centre z₀ ∈ U →
      ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → centre z ∈ U := by
  intro X Ω _ ξ K _ J _ y hgen ht z₀ w₀ U hw₀ hU
  choose c hc using hw₀.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hin₀ := in_chart (hgen (centre z₀)) hw₀ hc'
  obtain ⟨W, hWa, hW⟩ := ht.affine c hin₀.1
  have hz₀W : centre z₀ ∈ W := (hW _).2 ⟨hgen _, hin₀⟩
  obtain ⟨Q, hQU, hQ₀⟩ := hWa.exists_basicOpen_le (V := U) ⟨centre z₀, hU⟩ hz₀W
  have hgW : genPt ξ ∈ W := (hgen _).mem_open W.isOpen hz₀W
  have hreg : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q) ∈
      Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    rw [ht.ring c hin₀.1]
    intro p hp
    exact ⟨X.presheaf.germ W p.1 ((hW _).2 ⟨p.2, hp⟩) Q, OpenNear.genMap_germ hgW Q p _⟩
  rw [Algebra.adjoin_range_eq_range_aeval] at hreg
  obtain ⟨P, hP⟩ := hreg
  have hval : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → (∀ k, w ⟨k, c k⟩ ≠ 0) →
      ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q))
        (MvPolynomial.aeval (segreRatio c w) P) := by
    intro z w hw hcw
    rw [← hP]
    exact val_aeval (hgen _) (val_segreRatio (hgen _) hw hcw) P
  have hne₀ : MvPolynomial.aeval (segreRatio c w₀) P ≠ 0 :=
    (isUnit_germ_iff ht.gen hgW Q hz₀W (hval z₀ w₀ hw₀ hc')).1
      ((Scheme.mem_basicOpen X Q _ hz₀W).1 hQ₀)
  refine ⟨{w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (segreRatio c w) P ≠ 0}, ?_, ?_⟩
  · refine Filter.Eventually.and ?_ ((continuousAt_aeval_segreRatio hc' P).eventually_ne hne₀)
    exact Filter.eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
  · rintro z w ⟨hcw, hne⟩ hw
    have hzW : centre z ∈ W := (hW _).2 ⟨hgen _, in_chart (hgen _) hw hcw⟩
    exact hQU ((Scheme.mem_basicOpen X Q _ hzW).2
      ((isUnit_germ_iff ht.gen hgW Q hzW (hval z w hw hcw)).2 hne))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsNeighbourhoodInOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_neighbourhood_in_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (U : X.Opens), CoordsAt ξ y z₀ w₀ → centre z₀ ∈ U →
      ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → centre z ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.open_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.open_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.open_near <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformBoundOnClosedCone
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformBoundOnClosedCone
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem bound_of_local_bounds_of_blockScale :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  intro K _ J _ T Bd hT hcl hBdT hscale hloc
  classical
  obtain ⟨A, hA⟩ : ∃ A : Set ((Σ k, J k) → ℂ),
      A = (⋂ p, {w | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1} := ⟨_, rfl⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact (isClosed_iInter fun p => isClosed_le (continuous_norm.comp (continuous_apply p))
      continuous_const).inter (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i =>
        isClosed_eq (continuous_norm.comp (continuous_apply _)) continuous_const)
  have hA_le : ∀ w ∈ A, ∀ p, ‖w p‖ ≤ 1 := by
    intro w hw p
    rw [hA] at hw
    exact Set.mem_iInter.mp hw.1 p
  have hA_ne : ∀ w ∈ A, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro w hw k
    rw [hA] at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hw.2 k)
    refine ⟨i, fun h0 => ?_⟩
    have hi' : ‖w ⟨k, i⟩‖ = 1 := hi
    rw [h0, norm_zero] at hi'
    exact zero_ne_one hi'
  have hScl : IsClosed (T ∩ A) := by
    apply isClosed_of_closure_subset
    intro w hw
    have hwT : w ∈ closure T := closure_mono Set.inter_subset_left hw
    have hwA : w ∈ A := hAcl.closure_subset (closure_mono Set.inter_subset_right hw)
    exact ⟨hcl w hwT (hA_ne w hwA), hwA⟩
  have hSsub : T ∩ A ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact hA_le w hw.2
  have hScpt : IsCompact (T ∩ A) := (isCompact_closedBall 0 1).of_isClosed_subset hScl hSsub
  choose N hN C hC using fun w (hw : w ∈ T ∩ A) => hloc w hw.1
  obtain ⟨t, ht⟩ := hScpt.elim_nhds_subcover' N hN
  refine ⟨∑ s ∈ t, |C s.1 s.2|, ?_⟩
  intro w x hBd
  have hwT := hBdT w x hBd
  have hmax : ∀ k, ∃ i, ∀ j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i₀, -⟩ := hT w hwT k
    haveI : Nonempty (J k) := ⟨i₀⟩
    exact Finite.exists_max fun j => ‖w ⟨k, j⟩‖
  choose m hm using hmax
  have hmpos : ∀ k, 0 < ‖w ⟨k, m k⟩‖ := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hT w hwT k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hm k i₀)
  obtain ⟨c, hc⟩ : ∃ c : K → ℂ, c = fun k => ((‖w ⟨k, m k⟩‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    rw [hc]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (hmpos k).ne')
  have hBd' := hscale w x c hc0 hBd
  have hnorm : ∀ (k : K) (j : J k), ‖c k * w ⟨k, j⟩‖ = ‖w ⟨k, j⟩‖ / ‖w ⟨k, m k⟩‖ := by
    intro k j
    rw [hc, norm_mul, Complex.norm_real, norm_inv, norm_norm, div_eq_inv_mul]
  have hw'S : (fun p => c p.1 * w p) ∈ T ∩ A := by
    refine ⟨hBdT _ _ hBd', ?_⟩
    rw [hA]
    refine ⟨Set.mem_iInter.mpr fun p => ?_, Set.mem_iInter.mpr fun k => Set.mem_iUnion.mpr ⟨m k, ?_⟩⟩
    · obtain ⟨k, j⟩ := p
      show ‖c k * w ⟨k, j⟩‖ ≤ 1
      rw [hnorm]
      exact (div_le_one (hmpos k)).mpr (hm k j)
    · show ‖c k * w ⟨k, m k⟩‖ = 1
      rw [hnorm]
      exact div_self (hmpos k).ne'
  obtain ⟨s, hs, hsN⟩ := Set.mem_iUnion₂.mp (ht hw'S)
  calc |x| ≤ C s.1 s.2 := hC s.1 s.2 _ hsN x hBd'
    _ ≤ |C s.1 s.2| := le_abs_self _
    _ ≤ ∑ s ∈ t, |C s.1 s.2| :=
      Finset.single_le_sum (f := fun s : ↥(T ∩ A) => |C s.1 s.2|) (fun _ _ => abs_nonneg _) hs

end GlobalTheory.CompanionTheory.Ar.RootHt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformBoundOnClosedConeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_on_closed_cone : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale | exact GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianLineMetricBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem exists_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (hξ : IsCptGen ξ)
    (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z) {e : Li} (he : e ∈ M.lat ⟨centre z, hz⟩) :
    ∃ v : epsAt z ⟶ G, M.ValAt z e v := by
  obtain ⟨E, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M ℂ z hz E MR hξ inferInstance
  exact ⟨MR.pt (ev ⟨e, he⟩), (hev e _).2 ⟨he, rfl⟩⟩

theorem lat_of_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} (hz : genPt ξ ⤳ centre z)
    {e : Li} {v : epsAt z ⟶ G} (h : M.ValAt z e v) : e ∈ M.lat ⟨centre z, hz⟩ := by
  obtain ⟨_, v', hv', -⟩ := h
  exact Submodule.subset_span ⟨v', hv'⟩

theorem local_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ), CoordsAt ξ y z₀ w₀ → ∃ N ∈ 𝓝 w₀, ∃ C : ℝ,
    ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm z₀ w₀ hw₀
  have hξ := htie.gen
  obtain ⟨g, hg⟩ := GlobalTheory.T.smooth_group_rel_dim_generic X Ω ξ G hall
  choose c₁ hc₁ using fun k => hw₀.1 k
  have hc₁' : ∀ k, w₀ ⟨k, c₁ k⟩ ≠ 0 := fun k => (hc₁ k).ne_zero
  have h₀ := hall (centre z₀)
  obtain ⟨b, π, κ, hfl, hfr, hmb, hd, hmπ, hκ0, hκr, hκi, hκ⟩ :=
    GlobalTheory.T.exists_graded_sandwich_coordinates X Ω ξ K J y G Li M V r b₀ m i A.a e₀ hind hsw hdeg ⟨centre z₀, h₀⟩ c₁ (in_chart h₀ hw₀ hc₁')
  obtain ⟨U, hU, hnear⟩ := GlobalTheory.T.regular_sections_open_neighbourhood X Ω ξ G g Li M hξ hg ⟨centre z₀, h₀⟩ r (fun j => (m : Ω) • b j)
    (fun j => (m : Ω) • π j) hmb (fun j e he => by simpa using hmπ j e he)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : Ω) ≠ 0 := by exact_mod_cast hm.ne'
  have hminv : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, hz⟩ := fun z hz => by
    obtain ⟨_, h'⟩ := val_spec (val_inv₀ hm0 (val_nat (ξ := ξ) hz m))
    exact h'
  have hbq : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), centre z ∈ U → ∀ j, b j ∈ M.lat ⟨centre z, hz⟩ := by
    intro z hz hzU j
    have h1 := (hnear ⟨centre z, hz⟩ hzU).1 j
    have h2 := (M.lat ⟨centre z, hz⟩).smul_mem ⟨_, hminv z hz⟩ h1
    have h3 : (⟨(m : Ω)⁻¹, hminv z hz⟩ : regAt ξ ⟨centre z, hz⟩) • ((m : Ω) • b j) = b j := by
      show ((m : Ω)⁻¹) • ((m : Ω) • b j) = b j
      rw [smul_smul, inv_mul_cancel₀ hm1, one_smul]
    rwa [h3] at h2
  have hπq : ∀ (z : Sp ℂ ⟶ X) (hz : genPt ξ ⤳ centre z), centre z ∈ U → ∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩,
      π j e ∈ regAt ξ ⟨centre z, hz⟩ := by
    intro z hz hzU j e he
    have h1 := (hnear ⟨centre z, hz⟩ hzU).2 j e he
    have h2 := mul_mem (hminv z hz) h1
    have h3 : (m : Ω)⁻¹ * ((m : Ω) • π j) e = π j e := by
      simp [hm1]
    rwa [h3] at h2
  obtain ⟨N1, hN1, hN1'⟩ := GlobalTheory.T.coords_neighbourhood_in_open X Ω ξ K J y hall htie z₀ w₀ U hw₀ hU
  obtain ⟨φ, hφc, N2, hN2, hN2'⟩ := GlobalTheory.T.regular_function_continuous_at X Ω ξ K J y hall htie z₀ w₀ h₀ κ hw₀ hκr
  choose F hFc hFe using fun (a c : Fin r) => h.cont (b a) (b c)
  have hφ0 : φ w₀ ≠ 0 := by
    have hv := hN2' z₀ w₀ (mem_of_mem_nhds hN2) hw₀
    intro h0
    rw [h0] at hv
    obtain ⟨r', hr'⟩ := val_exists hκi
    have h1 := val_mul hv hr'
    rw [mul_inv_cancel₀ hκ0, zero_mul] at h1
    exact one_ne_zero (val_unique hξ (val_one h₀) h1)
  have hN3 : {w : (Σ k, J k) → ℂ | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} ∈ 𝓝 w₀ := by
    have : {w : (Σ k, J k) → ℂ | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} = ⋂ k, {w | w ⟨k, c₁ k⟩ ≠ 0} := by ext; simp
    rw [this]
    exact (isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const).mem_nhds
      (by simpa using hc₁')
  have hN5 : {w | φ w ≠ 0} ∈ 𝓝 w₀ := hφc.eventually_ne hφ0
  set N₀ : Set ((Σ k, J k) → ℂ) := N1 ∩ N2 ∩ {w | ∀ k, w ⟨k, c₁ k⟩ ≠ 0} ∩ {w | φ w ≠ 0} with hN₀
  have hN₀m : N₀ ∈ 𝓝 w₀ := inter_mem (inter_mem (inter_mem hN1 hN2) hN3) hN5
  set S₀ : Set ((Σ k, J k) → ℂ) := {w | w ∈ N₀ ∧ ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w} with hS₀
  have hw₀S : w₀ ∈ S₀ := ⟨mem_of_mem_nhds hN₀m, z₀, hw₀⟩
  have hS : ∀ a c, S₀ ⊆ {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z (b a) va ∧ M.ValAt z (b c) vb} := by
    rintro a c w ⟨hwN, z, hz⟩
    have hzU := hN1' z w hwN.1.1.1 hz
    obtain ⟨va, hva⟩ := exists_lieVal M hξ z (hall _) (hbq z (hall _) hzU a)
    obtain ⟨vb, hvb⟩ := exists_lieVal M hξ z (hall _) (hbq z (hall _) hzU c)
    exact ⟨z, va, vb, hz, hva, hvb⟩
  have hFw : ∀ a c, ContinuousWithinAt (F a c) S₀ w₀ := fun a c => ((hFc a c).mono (hS a c)) w₀ hw₀S
  let G₁ : ((Σ k, J k) → ℂ) → Matrix (Fin (i + 1)) (Fin (i + 1)) ℂ := fun w =>
    Matrix.of fun a c => F (Fin.castLE i.2 a) (Fin.castLE i.2 c) w
  let G₀ : ((Σ k, J k) → ℂ) → Matrix (Fin i) (Fin i) ℂ := fun w =>
    Matrix.of fun a c => F (Fin.castLE i.2.le a) (Fin.castLE i.2.le c) w
  have hg1 : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (B : Fin r → (epsAt z ⟶ G)), CoordsAt ξ y z w →
      (∀ j, M.ValAt z (b j) (B j)) → (gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)) = G₁ w := by
    intro z w B hz hB
    ext a c
    exact (hFe _ _ z w _ _ hz (hB _) (hB _)).symm
  have hg0 : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (B : Fin r → (epsAt z ⟶ G)), CoordsAt ξ y z w →
      (∀ j, M.ValAt z (b j) (B j)) → (gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)) = G₀ w := by
    intro z w B hz hB
    ext a c
    exact (hFe _ _ z w _ _ hz (hB _) (hB _)).symm
  choose B₀ hB₀ using fun j => exists_lieVal M hξ z₀ h₀ (hbq z₀ h₀ (hN1' z₀ w₀ (mem_of_mem_nhds hN1) hw₀) j)
  have hπ₀ := hπq z₀ h₀ (hN1' z₀ w₀ (mem_of_mem_nhds hN1) hw₀)
  have hne1 : (G₁ w₀).det ≠ 0 := by
    rw [← hg1 z₀ w₀ B₀ hw₀ hB₀]
    exact GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z₀ h₀ r b π B₀ hξ hd hπ₀ hB₀ _ _ (Fin.castLE_injective _)
  have hne0 : (G₀ w₀).det ≠ 0 := by
    rw [← hg0 z₀ w₀ B₀ hw₀ hB₀]
    exact GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z₀ h₀ r b π B₀ hξ hd hπ₀ hB₀ _ _ (Fin.castLE_injective _)
  have hd1 : ContinuousWithinAt (fun w => (G₁ w).det) S₀ w₀ :=
    (Continuous.matrix_det continuous_id).continuousAt.comp_continuousWithinAt
      (continuousWithinAt_pi.2 fun a => continuousWithinAt_pi.2 fun c => hFw _ _)
  have hd0 : ContinuousWithinAt (fun w => (G₀ w).det) S₀ w₀ :=
    (Continuous.matrix_det continuous_id).continuousAt.comp_continuousWithinAt
      (continuousWithinAt_pi.2 fun a => continuousWithinAt_pi.2 fun c => hFw _ _)
  let D : ((Σ k, J k) → ℂ) → ℝ := fun w => (1 / 2) * (Real.log ‖(G₁ w).det‖ - Real.log ‖(G₀ w).det‖) - Real.log ‖φ w‖ -
    ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖ + Real.log (A.h w)
  have hb₀ : ∀ k, ∃ j, w₀ ⟨k, j⟩ ≠ 0 := fun k => ⟨c₁ k, hc₁' k⟩
  have hA : ContinuousWithinAt A.h S₀ w₀ := by
    refine (hsm.continuousOn w₀ hb₀).mono ?_
    rintro w ⟨-, z, hz⟩ k
    exact (hz.1 k).imp fun c hc => hc.ne_zero
  have hsum : ContinuousWithinAt (fun w : (Σ k, J k) → ℂ => ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖) S₀ w₀ := by
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finsetSum _ fun k _ => ?_
    refine ContinuousAt.mul continuousAt_const ?_
    exact ((continuous_apply _).continuousAt.norm).log (norm_ne_zero_iff.2 (hc₁' k))
  have hD : ContinuousWithinAt D S₀ w₀ :=
    (((continuousWithinAt_const.mul ((hd1.norm.log (norm_ne_zero_iff.2 hne1)).sub
      (hd0.norm.log (norm_ne_zero_iff.2 hne0)))).sub
      (hφc.continuousWithinAt.norm.log (norm_ne_zero_iff.2 hφ0))).sub hsum).add (hA.log (A.pos w₀ hb₀).ne')
  have hev : ∀ᶠ w in 𝓝[S₀] w₀, dist (D w) (D w₀) < 1 := (Metric.tendsto_nhds.1 hD) 1 one_pos
  obtain ⟨N4, hN4, hN4'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  refine ⟨N4 ∩ N₀, inter_mem hN4 hN₀m, |D w₀| + 1, ?_⟩
  rintro z w ⟨hw4, hwN⟩ hz c₀ hc₀ f e v ve t u hf he hv hve hcls hu hu0 hG
  have hzq := hall (centre z)
  have hzU := hN1' z w hwN.1.1.1 hz
  have hc₁w : ∀ k, w ⟨k, c₁ k⟩ ≠ 0 := hwN.1.2
  have hφw : φ w ≠ 0 := hwN.2
  choose B hB using fun j => exists_lieVal M hξ z hzq (hbq z hzq hzU j)
  obtain ⟨s, hs⟩ := val_exists (R := ℂ) (hπq z hzq hzU i e (lat_of_lieVal hzq hve))
  have hκv := hN2' z w hwN.1.1.2 hz
  have hmul := val_mul hs hκv
  rw [← hκ e t he hcls] at hmul
  have hr := GlobalTheory.T.val_at_gen_independent_choice X Ω ξ K J y z w A.a e₀ t c₀ c₁ u (s * φ w) hξ hdeg.1 hz hc₀ hc₁w hu hmul
  have hp0 : ∏ k, w ⟨k, c₀ k⟩ ^ A.a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc₀ k)
  have hp1 : ∏ k, w ⟨k, c₁ k⟩ ^ A.a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc₁w k)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hr
    exact mul_ne_zero hu0 hp0 hr
  have hgv := GlobalTheory.T.lie_metric_frame_projection_at X Ω ξ K J y G Li M h z hzq r b π B i hξ hd (hπq z hzq hzU) hB f e v ve s
    (fun j => by rw [hfl]; exact hf j) (by rw [hfl]; exact he) hv hve hs hs0 hG
  rw [hg1 z w B hz hB, hg0 z w B hz hB] at hgv
  have hlog : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → Real.log ‖∏ k, c k ^ A.a k‖ = ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
    intro c hc'
    rw [norm_prod, Real.log_prod (fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hc' k)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_zpow, Real.log_zpow]
  have hnorm : Real.log ‖u‖ + ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ =
      Real.log ‖s‖ + Real.log ‖φ w‖ + ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₁ k⟩‖ := by
    have h1 := congrArg (fun x : ℂ => Real.log ‖x‖) hr
    simp only [norm_mul] at h1
    rw [Real.log_mul (norm_ne_zero_iff.2 hu0) (norm_ne_zero_iff.2 hp0),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hs0) (norm_ne_zero_iff.2 hφw)) (norm_ne_zero_iff.2 hp1),
      Real.log_mul (norm_ne_zero_iff.2 hs0) (norm_ne_zero_iff.2 hφw),
      hlog (fun k => w ⟨k, c₀ k⟩) hc₀, hlog (fun k => w ⟨k, c₁ k⟩) hc₁w] at h1
    exact h1
  have hfin : (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w) = D w := by
    simp only [D]
    rw [hgv]
    linarith
  rw [hfin]
  have h4 : dist (D w) (D w₀) < 1 := hN4' ⟨hw4, hwN, z, hz⟩
  rw [Real.dist_eq] at h4
  have h5 := abs_sub_abs_le_abs_sub (D w) (D w₀)
  linarith

theorem arch_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∃ C : ℝ, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm
  let Ex : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (c₀ : (k : K) → J k) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (u : ℂ), ℝ :=
    fun z w c₀ v ve u => (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)
  let Bd : ((Σ k, J k) → ℂ) → ℝ → Prop := fun w x => ∃ (z : Sp ℂ ⟶ X), CoordsAt ξ y z w ∧ ∃ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) ∧
      ∃ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧ (∀ j, M.ValAt z (f j) (v j)) ∧ M.ValAt z e ve ∧
      IsCls b₀ i e t ∧ ValAt ξ z (t / gen y A.a e₀ c₀) u ∧ u ≠ 0 ∧ (gramAt h z v).det ≠ 0 ∧ x = Ex z w c₀ v ve u
  obtain ⟨C, hC⟩ := GlobalTheory.T.uniform_bound_on_closed_cone K J {w | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w} Bd
    (fun w ⟨z, hz⟩ k => (hz.1 k).imp fun c hc => hc.ne_zero)
    (fun w hw hb => GlobalTheory.T.complex_points_closure_coords X Ω ξ K J y hall htie w hw hb)
    (fun w x ⟨z, hz, _⟩ => ⟨z, hz⟩)
    (by
      rintro w x c hc ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩
      refine ⟨z, coordsAt_smul c hc hz, c₀, fun k => mul_ne_zero (hc k) (hc₀ k), f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
      have hb : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => ⟨c₀ k, hc₀ k⟩
      have hp := A.pos w hb
      have hs := A.smul c w hc
      simp only [Ex]
      rw [hs, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))) hp.ne',
        Real.log_prod (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]
      have : ∀ k, (A.a k : ℝ) * Real.log ‖c k * w ⟨k, c₀ k⟩‖ = (A.a k : ℝ) * Real.log ‖c k‖ + (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ := fun k => by
        rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc₀ k))]; ring
      simp only [this, Finset.sum_add_distrib, Real.log_zpow]
      ring)
    (by
      rintro w₀ ⟨z₀, hz₀⟩
      obtain ⟨N, hN, C, hC⟩ := local_bound X Ω ξ K J y G Li M V r b₀ m i e₀ h A hc hall htie hm hind hsw hdeg hsm z₀ w₀ hz₀
      refine ⟨N, hN, C, ?_⟩
      rintro w hw x ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩
      exact hC z w hw hz c₀ hc₀ f e v ve t u h1 h2 h3 h4 h5 h6 h7 h8)
  refine ⟨C, ?_⟩
  intro z w hz c₀ hc₀ f e v ve t u h1 h2 h3 h4 h5 h6 h7 h8
  exact hC w _ ⟨z, hz, c₀, hc₀, f, e, v, ve, t, u, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianLineMetricBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_metric_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∃ C : ℝ, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound <;> assumption)
end
