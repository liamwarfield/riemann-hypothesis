module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsStarSubdivision
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMatchingPiecesOfCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionDropsMultCells
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedCentreSet
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EqOfOrbitMarkInCellCone
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EqOfOrbitMarkInCellCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell

theorem eq_of_orbMark_of_inRCone_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), IsTwG w0 φ → IsTwG w0 lab →
  SimpLab bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun O w0 v).evalZ β = 1 → (OrbMark.orbFun O w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  intro O _ _ _ _ bar w0 hb q φ lab hφ hlab hS X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt X _ _ _ _ hX m γ hγ β hβ hβn β' hβ' hβ'n
    hm hm' hin hin'
  obtain ⟨m', δ, hδ, hδli, hδinj, hγδ⟩ := hS.2 X hX m γ hγ
  have hcδ : ∀ j, InRCone δ (γ j) := hγδ
  obtain ⟨c, hc, hβc⟩ := inRCone_trans hcδ hin
  obtain ⟨c', hc', hβc'⟩ := inRCone_trans hcδ hin'
  obtain ⟨p, hp, hpi, hpc⟩ := GlobalTheory.T.exists_matching_pieces_of_cell O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β hm
  obtain ⟨p', hp', hpi', hpc'⟩ := GlobalTheory.T.exists_matching_pieces_of_cell O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β' hm'
  have hlabray : ∀ (x : LinearMap.BilinForm ℤ X) (j : Fin m') (d : ℝ), 0 < d → x ∈ balForms bar X →
      (∀ y, 0 ≤ x y y) → toReal x = d • toReal (δ j) → lab.evalZ x = lab.evalZ (δ j) := by
    intro x j d hd hxb hxn hx
    obtain ⟨a, b, ha, hb', hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x (δ j) d hd (hδli.ne_zero j) hx
    have h1 := hS.1 X hX x hxb hxn a ha
    have h2 := hS.1 X hX (δ j) (hδ.mem j) (hδ.nonneg j) b hb'
    rw [← h1, ← h2, hab]
  have hpeq : ∀ i, 0 < t i → p i = p' i := by
    intro i hti
    obtain ⟨hpb, hpn, hpp, hpl⟩ := hpi i hti
    obtain ⟨hpb', hpn', hpp', hpl'⟩ := hpi' i hti
    obtain ⟨j, -, d, hd, hpd⟩ := (hpc m' δ hδ hδli c hc hβc).1 i hti
    obtain ⟨j', -, d', hd', hpd'⟩ := (hpc' m' δ hδ hδli c' hc' hβc').1 i hti
    have hjj : j = j' := hδinj (by
      show lab.evalZ (δ j) = lab.evalZ (δ j')
      rw [← hlabray _ j d hd hpb hpn hpd, ← hlabray _ j' d' hd' hpb' hpn' hpd', hpl lab hlab, hpl' lab hlab])
    subst hjj
    have : toReal (p i) = (d / d') • toReal (p' i) := by
      rw [hpd, hpd', smul_smul, div_mul_cancel₀ _ hd'.ne']
    exact (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (p' i) (d / d') (div_pos hd hd') hpp hpp' this).1
  apply toReal_injective
  rw [hp, hp']
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).lt_or_eq with h | h
  · rw [hpeq i h]
  · rw [← h, zero_smul, zero_smul]

end GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EqOfOrbitMarkInCellConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.eq_of_orbit_mark_in_cell_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), IsTwG w0 φ → IsTwG w0 lab →
  SimpLab bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun O w0 v).evalZ β = 1 → (OrbMark.orbFun O w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OrbitMarkCoordinateLtOne
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OrbitMarkCoordinateLtOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound

theorem orbMark_coord_lt_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro O _ _ _ _ bar w0 hb φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    GlobalTheory.T.exists_matching_pieces_of_cell O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms bar (δ j) (h.mem j) (hprim j)
    have hd1 := (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OrbitMarkCoordinateLtOneStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.orbit_mark_coordinate_lt_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound.orbMark_coord_lt_one | exact GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound.orbMark_coord_lt_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound.orbMark_coord_lt_one <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedCentreSet
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres

theorem isTwG_orbFun {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (w0 : O)
    (v : LinearMap.BilinForm ℤ X₀) : IsTwG w0 (OrbMark.orbFun O w0 v) := by
  intro τ hτ n B
  rw [OrbMark.orbFun_toFun, OrbMark.orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (OrbMark.twv τ (OrbMark.twv (σ.trans τ.symm) a)) (OrbMark.twv τ (OrbMark.twv (σ.trans τ.symm) b)) = _
    rw [OrbMark.twv_twv, OrbMark.twv_twv]
    convert this using 3 <;> ext i <;> simp

theorem centres_exists : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → ∀ c : FormFamily O,
    ∃ w : InvFun O, IsTwG w0 w ∧ IsCentreSet bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  intro O _ _ _ _ bar w0 hb q φ lab _hdom _hfan hφ hlab hsl M hM _hmax c
  classical
  by_cases hex : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X)
      (_ : Module.Projective O X), Module.finrank O X ≤ q ∧
      ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ ∧ c.Carries δ
  · obtain ⟨X₀, _, _, _, _, -, m₀, δ₀, hM₀, hc₀⟩ := hex
    obtain ⟨v, hv, hvp, hvn, t, ht, htv⟩ := GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult bar φ M δ₀ hM₀ hM
    obtain ⟨h₀, hli, hpr, -⟩ := hM₀
    have hv0 : v ≠ 0 := fun h => by
      have e : (⟨v, hv⟩ : balForms bar X₀) = 0 := Subtype.ext h
      rw [e] at hvp
      exact not_isPrim_zero hvp
    refine ⟨OrbMark.orbFun O w0 v, isTwG_orbFun w0 v,
      fun X _ _ _ _ hX => ⟨fun β _ _ => OrbMark.orbFun_eval_eq_zero_or_one _ _ _,
        fun β _ _ h1 => GlobalTheory.T.markedOrbit_form_primitive bar w0 v hv hvp β h1,
        fun m γ hγ β hβ hβp β' hβ' hβp' h1 h1' hc hc' =>
          GlobalTheory.T.eq_of_orbit_mark_in_cell_cone O bar w0 hb q φ lab hφ hlab hsl δ₀ h₀ hli hpr v t hv0 (fun i => (ht i).1) htv X hX m γ hγ β hβ hβp β' hβ' hβp'
            h1 h1' hc hc'⟩,
      fun X _ _ _ _ _ m δ _ hδ => ?_,
      fun X _ _ _ _ _ m δ h hδ hδp β hβ hβp h1 c' hc' hβc =>
        GlobalTheory.T.orbit_mark_coordinate_lt_one O bar w0 hb φ hφ δ₀ h₀ hli hpr v t hv0 ht htv X m δ h hδ hδp β hβ hβp h1 c' hc' hβc⟩
    obtain ⟨β, hβ, hβp, h1, hin⟩ := GlobalTheory.T.carries_exists_marked_form_in_cone bar w0 c δ₀ v t hv hv0 hvn hc₀ (fun i => (ht i).1) htv X m δ hδ
    exact ⟨β, hβ, hβp, h1, hin⟩
  · refine ⟨GlobalTheory.PolFan.zeroFun O, fun _ _ _ _ => rfl, fun X _ _ _ _ _ =>
      ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h,
        fun _ _ _ β _ _ _ _ _ h => by simp at h⟩,
      fun X _ _ _ _ hX m δ hδ hc => (hex ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, hX, m, δ, hδ, hc⟩).elim,
      fun X _ _ _ _ _ m δ _ _ _ β _ _ h => by simp at h⟩

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedCentreSetStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_twisted_centre_set : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → ∀ c : FormFamily O,
    ∃ w : InvFun O, IsTwG w0 w ∧ IsCentreSet bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres.centres_exists | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres.centres_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres.centres_exists <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionMultLe
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStar
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity


open GlobalTheory.PolFan.StarNewCell in
theorem cellMult_lt_of_star_new : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar φ γ → β₀ ∈ balForms bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
  intro O _ _ _ _ bar _hb q φ lab w ψ' hSL hCS hcoord M hM X _ _ _ _ hX n γ' hγ' hliγ' hprimγ' m γ β₀ m' s h hγ hβ₀ hβ₀p hw
    hβ₀γ hcut hpos hτ hγ'τ
  classical

  obtain ⟨m₀, δ, hδ, hliδ, -, hγδ⟩ := hSL.2 X hX m γ hγ
  obtain ⟨δt, hδt, hliδt, hprimδt, hδδt⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell bar φ δ hδ hliδ
  have hγδt : ∀ k, InRCone δt (γ k) := fun k => hδδt _ (hγδ k)

  obtain ⟨h₂, h₂0, h₂γ, h₂cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone bar φ δt γ hδt hγ hγδt
  have hcutγ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 →
      InRCone (fun k => γ (s k)) β :=
    fun β _ _ hβ hβ0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero γ h s β hcut.1 (fun i hi => (hcut.2 i).1 hi) hβ hβ0
  have hhs : ∀ k, h (γ (s k)) = 0 := fun k => (hcut.2 (s k)).2 ⟨k, rfl⟩
  obtain ⟨h₃, h₃0, h₃γs, h₃cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone bar δt γ (fun k => γ (s k)) h₂ h hδt.mem hδt.nonneg
    (fun k => inRCone_self γ (s k)) h₂0 h₂γ h₂cut hcut.1 hhs hcutγ

  set I : Finset (Fin m₀) := Finset.univ.filter (fun i => h₃ (δt i) = 0) with hI
  set eI : Fin I.card ↪ Fin m₀ := (I.orderEmbOfFin rfl).toEmbedding with heIdef
  have heI : ∀ i, i ∈ Set.range eI ↔ h₃ (δt i) = 0 := by
    intro i
    show i ∈ Set.range (I.orderEmbOfFin rfl) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [I]
  have hsupp : ∀ β, InRCone δt β → h₃ β = 0 → InRCone (fun k => δt (eI k)) β :=
    fun β hβ h0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero δt h₃ eI β h₃0 (fun i hi => (heI i).2 hi) hβ h0

  obtain ⟨c, hc0, hcβ⟩ : InRCone δt β₀ := StarNewCell.inRCone_trans hγδt hβ₀γ
  have hclt : ∀ i, c i < 1 := hcoord X hX m₀ δt hδt hliδt hprimδt β₀ hβ₀ hβ₀p hw c hc0 hcβ
  obtain ⟨j, hcj, hjI⟩ : ∃ j, 0 < c j ∧ h₃ (δt j) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h30 : h₃ β₀ = 0 := by
      have : (h₃ β₀ : ℝ) = 0 := by
        rw [val_eq h₃ hcβ]
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases (hc0 i).eq_or_lt with hi | hi
        · rw [← hi, zero_mul]
        · rw [hno i hi]; simp
      exact_mod_cast this
    have := val_zero h hhs (h₃cut β₀ hβ₀ hβ₀p ⟨c, hc0, hcβ⟩ h30)
    omega

  have hprimβ₀ : ∀ hx : β₀ ∈ balForms bar X, IsPrim bar (⟨β₀, hx⟩ : balForms bar X) := by
    intro hx k β' hk
    refine (hCS X hX).2.1 β₀ hβ₀ hβ₀p hw k β' ?_
    have h' : β₀ = ((k • β' : balForms bar X) : LinearMap.BilinForm ℤ X) := congrArg Subtype.val hk
    rw [h', Submodule.coe_smul_of_tower, natCast_zsmul]

  set δs : Fin m₀ → balForms bar X := fun i => ⟨δt i, hδt.mem i⟩ with hδs
  set βs : balForms bar X := ⟨β₀, hβ₀⟩ with hβs
  have hliδs : LinearIndependent ℤ δs := LinearIndependent.of_comp (balForms bar X).subtype hliδt

  set ρs : Fin (I.card + 1) → balForms bar X := Fin.cons βs (fun k => δs (eI k)) with hρsdef
  obtain ⟨ρ, hρ0, hρs, hρv⟩ : ∃ ρ : Fin (I.card + 1) → LinearMap.BilinForm ℤ X, ρ 0 = β₀ ∧
      (∀ k, ρ k.succ = δt (eI k)) ∧ ∀ i, ρ i = (ρs i : LinearMap.BilinForm ℤ X) :=
    ⟨fun i => (ρs i : LinearMap.BilinForm ℤ X), by simp [ρs, βs], fun k => by simp [ρs, δs], fun i => rfl⟩
  have hjeI : j ∉ Set.range eI := fun hh => hjI ((heI j).1 hh)
  have hliρ : LinearIndependent ℤ ρ := by
    have h1 := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero bar δs βs c j eI hliδs hcβ hcj.ne' hjeI
    have h2 := h1.map' (balForms bar X).subtype (Submodule.ker_subtype _)
    have : ρ = (balForms bar X).subtype ∘ ρs := funext hρv
    rw [this]; exact h2
  have hρmem : ∀ i, ρ i ∈ balForms bar X := fun i => by rw [hρv]; exact (ρs i).2
  have hρnn : ∀ i y, 0 ≤ ρ i y y := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact hβ₀p
    · rw [hρs]; exact hδt.nonneg _
  have hρprim : ∀ i, IsPrim bar (⟨ρ i, hρmem i⟩ : balForms bar X) := by
    have key : ∀ (x y : LinearMap.BilinForm ℤ X) (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), x = y →
        IsPrim bar (⟨y, hy⟩ : balForms bar X) → IsPrim bar (⟨x, hx⟩ : balForms bar X) := by
      rintro x y hx hy rfl hp; exact hp
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · exact key _ _ _ hβ₀ hρ0 (hprimβ₀ hβ₀)
    · exact key _ _ _ (hδt.mem _) (hρs k) (hprimδt _)

  have hτρ : ∀ i, InRCone ρ ((Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, ← hρ0]; exact inRCone_self ρ 0
    · rw [Fin.cons_succ]
      exact StarNewCell.inRCone_trans (fun l => hρs l ▸ inRCone_self ρ l.succ) (hsupp _ (hγδt (s k)) (h₃γs k))
  have hρτ : ∀ i, InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) (ρ i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact inRCone_cons_zero _ _
    · rw [hρs]
      exact StarNewCell.inRCone_trans (fun l => inRCone_cons_succ β₀ (fun j => γ (s j)) l)
        (h₃cut _ (hδt.mem _) (hδt.nonneg _) (inRCone_self δt _) ((heI _).1 ⟨k, rfl⟩))

  obtain ⟨h₁, h₁0, h₁γ', h₁cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone bar ψ' _ γ' hτ hγ' hγ'τ
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive bar ρ γ' hρmem hγ'.mem h₁ hliρ hliγ' hρprim hprimγ'
    (fun k => StarNewCell.inRCone_trans hτρ (hγ'τ k)) (fun i => val_nonneg h₁ h₁0 (hρτ i)) h₁γ'
    (fun i hi => h₁cut (ρ i) (hρmem i) (hρnn i) (hρτ i) hi)

  set J : Finset (Fin m₀) := Finset.univ.erase j with hJ
  have hJc : J.card = m₀ - 1 := by simp [J]
  set eJ : Fin (m₀ - 1) ↪ Fin m₀ := (J.orderEmbOfFin hJc).toEmbedding with heJdef
  have heJ : ∀ i, i ∈ Set.range eJ ↔ i ≠ j := by
    intro i
    show i ∈ Set.range (J.orderEmbOfFin hJc) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [J]
  set ρ's : Fin (m₀ - 1 + 1) → balForms bar X := Fin.cons βs (fun k => δs (eJ k)) with hρ'sdef
  have hliρ' : LinearIndependent ℤ ρ's := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero bar δs βs c j eJ hliδs hcβ hcj.ne' (fun hh => (heJ j).1 hh rfl)
  have hmultρ' : (cellMult bar ρ's : ℝ) = c j * cellMult bar δs :=
    GlobalTheory.T.cell_multiplicity_positive_cone bar δs βs c j eJ hliδs hcβ hcj heJ (GlobalTheory.T.balancedFormCellMultiplicity_pos bar δs)
  have hrange : Set.range (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ⊆ Set.range ρ's := by
    rintro _ ⟨k, rfl⟩
    have e := hs' k
    rcases Fin.eq_zero_or_eq_succ (s' k) with h0 | ⟨l, hl⟩
    · refine ⟨0, Subtype.ext ?_⟩
      simp [ρ's, βs]
      rw [e, h0, hρ0]
    · have hne : eI l ≠ j := fun hh => hjI (hh ▸ (heI (eI l)).1 ⟨l, rfl⟩)
      obtain ⟨r, hr⟩ := (heJ (eI l)).2 hne
      refine ⟨r.succ, Subtype.ext ?_⟩
      simp [ρ's, δs]
      rw [e, hl, hρs, hr]
  have hdvd : cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ∣ cellMult bar ρ's :=
    GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms bar X) ρ's _ hliρ' hrange
  have hle := Nat.le_of_dvd (GlobalTheory.T.balancedFormCellMultiplicity_pos bar ρ's) hdvd
  have hδpos := GlobalTheory.T.balancedFormCellMultiplicity_pos bar δs
  have hlt : (cellMult bar ρ's : ℝ) < cellMult bar δs := by
    rw [hmultρ']; exact mul_lt_of_lt_one_left (by exact_mod_cast hδpos) (hclt j)
  have hlt' : cellMult bar ρ's < cellMult bar δs := by exact_mod_cast hlt
  have hδsM : cellMult bar δs ≤ M := by
    have := (SmoothEnd.cellMult_le_maxMult hX hδt hliδt hprimδt).trans hM
    exact_mod_cast this
  omega

end GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStarStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.new_cell_mult_lt_after_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar φ γ → β₀ ∈ balForms bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new | exact GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStar
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity

theorem starOld_cell_mult_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → IsCell bar ψ' γ →
          (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell bar φ γ', cellMult bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms bar X)) ≤ M ∧
            ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  intro O _ _ _ _ bar hb q φ lab w ψ' hDom hφ hlab M hM X _ _ _ _ hX n γ' hγ' hli' hp' m γ hγφ hγψ hw hin

  obtain ⟨m', δ, hδ, hδli, -, hδγ⟩ := hlab.2 X hX m γ hγφ
  obtain ⟨δ₁, hδ₁, hδ₁li, hδ₁p, hδδ₁⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell bar φ δ hδ hδli
  have hγδ₁ : ∀ k, InRCone δ₁ (γ k) := fun k => hδδ₁ _ (hδγ k)

  obtain ⟨h₂, h₂n, h₂z, h₂c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone bar φ δ₁ γ hδ₁ hγφ hγδ₁
  obtain ⟨h₁, h₁n, h₁z, h₁c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone bar ψ' γ γ' hγψ hγ' hin
  obtain ⟨h, hn, hz, hc⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone bar δ₁ γ γ' h₂ h₁ hδ₁.mem hδ₁.nonneg hin h₂n h₂z h₂c h₁n h₁z h₁c
  have hin₁ : ∀ j, InRCone δ₁ (γ' j) := fun j => inRCone_trans hγδ₁ (hin j)
  obtain ⟨s, hs, hsf⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive bar δ₁ γ' hδ₁.mem hγ'.mem h hδ₁li hli' hδ₁p hp' hin₁ hn hz
    (fun i hi => hc _ (hδ₁.mem i) (hδ₁.nonneg i) (inRCone_self δ₁ i) hi)
  have hγ'eq : γ' = fun j => δ₁ (s j) := funext hs
  have hcut : IsFaceCut δ₁ s h := ⟨hn, hsf⟩
  have hφ' : IsCell bar φ γ' := by
    rw [hγ'eq]; exact GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q φ hφ X hX (hDom X) m' δ₁ hδ₁ _ s h hcut
  refine ⟨hφ', ?_, fun β hβ hβn hβc h1 => ?_⟩
  ·
    have hliB : LinearIndependent ℤ (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) :=
      LinearIndependent.of_comp (balForms bar X).subtype hδ₁li
    have hrange : Set.range (fun j => (⟨γ' j, hφ'.mem j⟩ : balForms bar X)) ⊆
        Set.range (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨s j, Subtype.ext (hs j).symm⟩
    have hdvd := GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms bar X) _ _ hliB hrange
    have hpos := GlobalTheory.T.balancedFormCellMultiplicity_pos bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X))
    have hle := SmoothEnd.cellMult_le_maxMult hX hδ₁ hδ₁li hδ₁p
    have hle' : cellMult bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms bar X)) ≤ M := by
      exact_mod_cast hle.trans hM
    exact (Nat.le_of_dvd hpos hdvd).trans hle'
  ·
    rw [hw β hβ hβn (inRCone_trans hin hβc)] at h1
    exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStarStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.old_cell_mult_le_after_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → IsCell bar ψ' γ →
          (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell bar φ γ', cellMult bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms bar X)) ≤ M ∧
            ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le | exact GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionMultLe
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity

theorem starMult : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' → ∀ M : ℕ, maxMult bar q φ ≤ M →
    maxMult bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar ψ' M δ →
          IsMultCell bar φ M δ ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro O _ _ _ _ bar hCM q φ lab w ψ' hDom hφ hlab hw hc1 hψ' hsub hstar M hM
  obtain ⟨hs1, hs2, hs3⟩ := hstar
  have key : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        (∃ (_ : IsCell bar φ γ'), (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) ≤ M ∧
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1) ∨
        (cellMult bar fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
    intro X _ _ _ _ hX n γ' hγ' hli hpr
    rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hw0, hin⟩ |
        ⟨m, γ, β₀, m', s, h, hγ, hβ₀, hpsd, hw1, hcone, hcut, hpos, hin⟩
    · left
      exact GlobalTheory.T.old_cell_mult_le_after_star O bar hCM q φ lab w ψ' hDom hφ hlab M hM X hX n γ' hγ' hli hpr m γ hγ
        (hs1 X hX m γ hγ hw0) hw0 hin
    · right
      exact GlobalTheory.T.new_cell_mult_lt_after_star O bar hCM q φ lab w ψ' hlab hw hc1 M hM X hX n γ' hγ' hli hpr m γ β₀ m' s h
        hγ hβ₀ hpsd hw1 hcone hcut hpos (hs2 X hX m γ hγ β₀ hβ₀ hpsd hw1 hcone m' s h hcut hpos) hin
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.PolFan.maxMult
    refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hX => iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli =>
      iSup_le fun hpr => ?_
    rcases key X hX n γ' hγ' hli hpr with ⟨_, hle, _⟩ | hlt
    · exact_mod_cast hle
    · exact_mod_cast hlt.le
  · intro X _ _ _ _ hX m δ hδ
    obtain ⟨hc, hli, hpr, hEq⟩ := hδ
    rcases key X hX m δ hc hli hpr with ⟨hφ', _, hno⟩ | hlt
    · exact ⟨⟨hφ', hli, hpr, hEq⟩, hno⟩
    · exact absurd hEq (ne_of_lt hlt)

end GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionMultLeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.star_subdivision_mult_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' → ∀ M : ℕ, maxMult bar q φ ≤ M →
    maxMult bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar ψ' M δ →
          IsMultCell bar φ M δ ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity.starMult | exact GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity.starMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity.starMult <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabel
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabel
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.StarLab GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling

theorem isTwG_starLab {O : Type} [CommRing O] (w0 : O) {lab w : InvFun O}
    (hl : IsTwG w0 lab) (hw : IsTwG w0 w) : IsTwG w0 (starLab lab w) := by
  have fwd : ∀ (σ : O ≃+* O), σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      IsCentreRay w (Fin n → O) B →
        IsCentreRay w (Fin n → O) (fun a b => B (fun i => σ (a i)) fun i => σ (b i)) := by
    intro σ hσ n B h
    unfold IsCentreRay at h ⊢
    obtain ⟨t, ht, β, hβ, hB⟩ := h
    let τ : (Fin n → O) →ₗ[ℤ] (Fin n → O) :=
      { toFun := fun a i => σ (a i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun k a => by ext i; simp }
    let β' : LinearMap.BilinForm ℤ (Fin n → O) := β.compl₁₂ τ τ
    have h1 : w.evalZ β' = w.evalZ β := by
      unfold GlobalTheory.LocM.InvFun.evalZ
      rw [GlobalTheory.LocM.InvFun.eval_pi, GlobalTheory.LocM.InvFun.eval_pi]
      exact hw σ hσ n (fun a b => ((β a) b : ℝ))
    exact ⟨t, ht, β', h1.trans hβ, fun a b => hB (τ a) (τ b)⟩
  intro σ hσ n B
  have hσ' : σ.symm w0 = w0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hσ.symm
  have hiff : IsCentreRay w (Fin n → O) (fun a b => B (fun i => σ (a i)) fun i => σ (b i)) ↔
      IsCentreRay w (Fin n → O) B := by
    refine ⟨fun h => ?_, fwd σ hσ n B⟩
    have h2 := fwd σ.symm hσ' n _ h
    simp only [RingEquiv.apply_symm_apply] at h2
    exact h2
  rw [← GlobalTheory.LocM.InvFun.eval_pi, ← GlobalTheory.LocM.InvFun.eval_pi, starLab_eval, starLab_eval,
    GlobalTheory.LocM.InvFun.eval_pi, GlobalTheory.LocM.InvFun.eval_pi, hl σ hσ n B]
  by_cases hc : IsCentreRay w (Fin n → O) B
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (mt hiff.mp hc), if_neg hc]

theorem exists_isTwG_simpLab_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 lab → SimpLab bar q φ lab → IsTwG w0 w → IsCentreSet bar q φ w →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' →
    ∃ lab' : InvFun O, IsTwG w0 lab' ∧ SimpLab bar q ψ' lab' := by
  intro O _ _ _ _ bar w0 hb q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwG_starLab w0 hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le O bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell bar φ (fun j => δ (s j)) := GlobalTheory.T.cell_face_restriction O bar hb q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell bar φ (fun j => γ (s j)) := GlobalTheory.T.cell_face_restriction O bar hb q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le O bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · exact LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => by
        have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
        have h2 := congrArg g hz
        rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
        exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabelStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_simplicial_star_label : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 lab → SimpLab bar q φ lab → IsTwG w0 w → IsCentreSet bar q φ w →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' →
    ∃ lab' : InvFun O, IsTwG w0 lab' ∧ SimpLab bar q ψ' lab' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionDropsMultCells
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells

theorem exists_star_drop_multCells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → MultCellsAmong bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
      Subordinate bar q φ' φ ∧ maxMult bar q φ' ≤ M ∧ MultCellsAmong bar q φ' M n := by
  intro O _ _ _ _ bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := GlobalTheory.T.exists_twisted_centre_set O bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := GlobalTheory.T.exists_star_subdivision O bar w0 hb q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := GlobalTheory.T.exists_twisted_simplicial_star_label O bar w0 hb q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := GlobalTheory.T.star_subdivision_mult_le O bar hb q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionDropsMultCellsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.star_subdivision_drops_mult_cells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → MultCellsAmong bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
      Subordinate bar q φ' φ ∧ maxMult bar q φ' ≤ M ∧ MultCellsAmong bar q φ' M n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells.exists_star_drop_multCells | exact GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells.exists_star_drop_multCells | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells.exists_star_drop_multCells <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFan
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan GlobalTheory.PolFan.CellClass

namespace GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells

theorem perModule {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolyFanOn bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
      ∃ e : X ≃ₗ[O] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms bar X, IsPrim bar (⟨t, ht⟩ : balForms bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone (bar := bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (GlobalTheory.T.cell_generator_mem_cone_of_smul_combination bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O),
    IsPolyFan bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong bar q φ M n := by
  intro O _ _ _ _ bar hb q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := hb.classes q
  haveI hfin : ∀ k, Module.Finite O (R k) := fun k => (hR k).1
  have key : ∀ k, ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar (R k))) →
        ∃ e : (R k) ≃ₗ[O] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    haveI := (hR k).2.1
    exact perModule bar φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily O := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim bar (⟨δ' i, hcell'.mem i⟩ : balForms bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiple_cells_among_polyhedral_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O),
    IsPolyFan bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong bar q φ M n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan | exact GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MultipleCells.multCellsAmong_of_isPolyFan <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicity
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity

theorem exists_round_lt_maxMult : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → maxMult bar q φ < ⊤ →
    2 ≤ maxMult bar q φ → ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧
      SimpLab bar q φ' lab' ∧ Subordinate bar q φ' φ ∧ maxMult bar q φ' < maxMult bar q φ := by
  intro O _ _ _ _ bar w0 hb q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult bar q φ).toNat with hMdef
  have hMe : maxMult bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.T.multiple_cells_among_polyhedral_fan O bar hb q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun O), IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab →
      SimpLab bar q φ lab → maxMult bar q φ ≤ M → MultCellsAmong bar q φ M n →
      ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
        Subordinate bar q φ' φ ∧ maxMult bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ :=
        GlobalTheory.T.star_subdivision_drops_mult_cells O bar w0 hb q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicityStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_fan_lower_max_multiplicity : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → maxMult bar q φ < ⊤ → 2 ≤ maxMult bar q φ → ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧ Subordinate bar q φ' φ ∧ maxMult bar q φ' < maxMult bar q φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult | exact GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult <;> assumption)
end
