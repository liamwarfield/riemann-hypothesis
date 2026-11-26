module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSums
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGauge
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGauge
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ArcLift

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem local_noeth {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) :
    IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

theorem exists_lift : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  intro hL hG E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb F _ _ _ S hS
  obtain ⟨_, _⟩ := local_noeth hb
  obtain ⟨N, ν, hν⟩ := GlobalTheory.T.exists_integral_degeneration_values hL O' a.D₀ a.even a.bimult F S hS
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hrW : H.rt0 ∈ W₀ := mem_of_pow_mem W₀ two_ne_zero (by
    rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W₀ _))
  have hzW : zeta l.A ∈ W₀ := mem_of_pow_mem W₀ l.A_pos.ne' (by
    rw [zeta, (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]; exact one_mem _)
  let r : c.V W₀ := ⟨⟨H.rt0, hr⟩, hrW⟩
  let z : c.V W₀ := ⟨⟨zeta l.A, hz⟩, hzW⟩
  obtain ⟨hdet, I, hζ, hA, hM⟩ := a.geom F r z rfl rfl _ rfl
  have hq := fun n (v : D.La) =>
    (((hG O' a.D₀ a.even a.bimult F N ν).2.2.2.2 n).1 (I.ev n v)).exists
  choose q hq using hq
  have hr2 : r ^ 2 = -(H.d : c.V W₀) := by
    apply Subtype.ext; apply Subtype.ext
    simpa [r] using H.sqrt_neg_disc_sq
  refine ⟨{ ρ := algebraMap (FractionRing O') F (algebraMap O' _ (b r))
            ρ_sq := by rw [← map_pow, ← map_pow, ← map_pow, hr2, map_neg, map_neg, map_neg, map_natCast, map_natCast, map_natCast]
            det := fun τ => by
              obtain ⟨n, h1, h2⟩ := hdet τ
              exact ⟨n, h1, by
                rw [h2]
                by_cases h : τ H.rt = algebraMap (FractionRing O') F (algebraMap O' _ (b r))
                · rw [if_pos h]; exact if_pos h
                · rw [if_neg h]; exact if_neg h⟩
            I := I, N := N, ν := ν, q := q, hq := hq
            be := { be := a.be.comp ν.eX.toIntLinearEquiv.toLinearMap ν.eX.toIntLinearEquiv.toLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ (by simpa using hy)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r' h => by
              obtain rfl : r' = r := Subtype.ext (Subtype.ext h)
              rfl
            ζ_eq := fun z' h => by
              obtain rfl : z' = z := Subtype.ext (Subtype.ext h)
              exact hζ
            levA := hA
            levM := hM
            closed := inferInstance }, hν⟩

end GlobalTheory.Ex.ArcLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGaugeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcIsometry_torsion_integralGauge : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  first | exact @GlobalTheory.Ex.ArcLift.exists_lift | exact GlobalTheory.Ex.ArcLift.exists_lift | (intros; apply GlobalTheory.Ex.ArcLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescentSubring
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem NumD.exists_descent_subring : ∀ (O F : Type) [CommRing O] [CommRing F] (io : O →+* F), Function.Injective io → ∀ (N : NumD F) (A₀ : Subgroup N.A), (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, ∃ a : Oˣ, io a = N.θ x y u) → (∀ x ∈ A₀, ∃ a : Oˣ, io a = N.σ x) → (∀ x ∈ A₀, ∃ a : O, io a = N.th x) → (∀ χ, ∃ a : Oˣ, io a = N.ψ χ) → ∃ (N₀ : NumD O) (I : NumD.Hom io N₀ N), I.lam = 1 ∧ ∀ (k : ℕ) (p : N.QT k), p.1.2.b ∈ A₀ → (∀ χ, ∃ a : Oˣ, io a = p.1.2.s χ) → ∃ p₀ : N₀.QT k, p.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p.1.2 := by
  intro O F _ _ io hio N A₀ hc hθ hσ hth hψ
  have hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u := fun x y u =>
    (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h
  have hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x := fun x =>
    (hσ x x.2).imp fun a h => Units.ext h
  have hth' : ∀ x : A₀, ∃ a : O, io a = N.th x := fun x => hth x x.2
  have hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ := fun χ =>
    (hψ χ).imp fun a h => Units.ext h
  choose θ eθ using hθ'
  choose σ eσ using hσ'
  choose th eth using hth'
  choose ψ eψ using hψ'
  have inj : Function.Injective (Units.map io.toMonoidHom) := Units.map_injective hio
  let B₀ : NumB O :=
    { A := A₀
      θ := θ
      cub :=
        { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _)
          s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _)
          s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _)
          coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; exact N.cub.coc _ _ _ _) }
      σ := σ
      σ_one := inj (by rw [eσ, map_one]; exact N.σ_one)
      σ_mul := fun x y => inj (by simp only [map_mul, eθ, eσ]; exact N.σ_mul _ _)
      th := th }
  let N₀ : NumD O :=
    { toNumB := B₀
      X := N.X
      c := fun χ => (⟨N.c χ, hc χ⟩ : A₀)
      c_add := fun a b => Subtype.ext (N.c_add a b)
      ψ := ψ
      even := fun χ => inj (by
        change Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _
        simp only [map_mul, eψ, eσ]; exact N.even χ)
      bimult := fun a a' b => inj (by
        change Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _
        simp only [map_mul, map_div, eψ, eθ]; exact N.bimult a a' b) }
  let I : NumD.Hom io N₀ N :=
    { φ := A₀.subtype
      h := fun _ => 1
      h_one := rfl
      θ_eq := fun (x y u : A₀) => by
        simp only [mul_one]; exact (eθ x y u).symm
      σ_eq := fun (x : A₀) => by
        simp only [mul_one]; exact (eσ x).symm
      lam := 1
      th_eq := fun (x : A₀) => by
        simp only [mul_one, Units.val_one, one_mul]; exact (eth x).symm
      e := AddEquiv.refl N.X
      c_eq := fun _ => rfl
      ψ_eq := fun (χ : N.X) => by
        simp only [mul_one]; exact (eψ χ).symm }
  let Φ : N₀.Gt →* N.Gt := MonoidHom.mk'
    (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by
      have := congrArg (Units.map io.toMonoidHom) (g.mult χ χ')
      rw [map_mul, map_mul] at this
      rw [← this]
      exact congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)
    (fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _
      rw [map_div, map_mul, eθ]; rfl))
  have Φinj : Function.Injective Φ := fun g g' h =>
    NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h))
      (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))
  have Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y := fun y =>
    NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _
      rw [map_div, map_div, eψ, eψ, eψ]; rfl)
  refine ⟨N₀, I, rfl, fun k p hb hs => ?_⟩
  have hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ := fun χ =>
    (hs χ).imp fun a h => Units.ext h
  choose s es using hs'
  let g₀ : N₀.Gt := ⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by
    change Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _
    simp only [map_mul, es, eθ]; exact p.1.2.mult χ χ')⟩
  have hg : Φ g₀ = p.1.2 := NumD.Gt.ext rfl (funext fun χ => es χ)
  refine ⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩
  · change Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))
    rw [map_pow, hg, Φio]; exact p.2
  · change p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1
    rw [es, mul_one, mul_one]

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebra
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.TorsDesc

theorem s_mem_of_basis {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ) (g : N.Gt) {ι : Type}
    (e : Module.Basis ι ℤ N.X) (hθ : ∀ χ χ', N.θ (N.c χ) (N.c χ') g.b ∈ U) (he : ∀ l, g.s (e l) ∈ U) (χ : N.X) :
    g.s χ ∈ U := by
  have hχ : χ ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; trivial
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact he l
  | zero => rw [NumD.Gt.s_zero]; exact U.one_mem
  | add x y _ _ hx hy =>
    rw [eq_div_iff_mul_eq'.2 (g.mult x y)]
    exact U.div_mem (U.mul_mem hx hy) (hθ _ _)
  | neg x _ hx =>
    have := g.mult x (-x)
    rw [add_neg_cancel, NumD.Gt.s_zero, one_mul] at this
    exact (U.mul_mem_cancel_left hx).1 (this ▸ hθ _ _)

theorem s_mem_of_root {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ)
    (hθ : ∀ x y u, N.θ x y u ∈ U) (hψ : ∀ χ, N.ψ χ ∈ U) {k : ℕ} (hU : ∀ u : Fˣ, u ^ k ∈ U → u ∈ U) (p : N.QT k)
    (χ : N.X) : p.1.2.s χ ∈ U := by
  refine hU _ ?_
  rw [← NumD.Gt.pow_s, N.mem_QT.1 p.2, NumD.io_s]
  exact U.mul_mem (U.div_mem (U.div_mem (hψ _) (hψ _)) (hψ _)) (U.prod_mem fun _ _ => hθ _ _ _)

theorem exists_finite_subalgebra (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F]
    (K : IntermediateField (FractionRing O) F) [FiniteDimensional (FractionRing O) K] :
    ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∀ x ∈ K, IsIntegral O x → x ∈ O₁ := by
  have : CharZero (FractionRing O) := IsFractionRing.charZero_of_isFractionRing O
  have : Module.Finite O (integralClosure O K) := IsIntegralClosure.finite O (FractionRing O) K _
  let v : K →ₐ[O] F := { K.val.toRingHom with commutes' := fun _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  refine ⟨(integralClosure O K).map v, Module.Finite.equiv ((integralClosure O K).equivMapOfInjective v hv).toLinearEquiv,
    fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff v hv).1 hi

theorem descend : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  intro O F _ _ _ _ _ _ _ _ _ _ S hS N K₁ A₀ hK hc hθ hσ hth hψ vθ vσ vth vψ Ix _ k p hk hp
  let e := Module.Free.chooseBasis ℤ N.X
  let T : Set F := Set.range fun il : Ix × Module.Free.ChooseBasisIndex ℤ N.X => ((p il.1).1.2.s (e il.2) : F)
  have : Finite T := (Set.finite_range _).to_subtype
  have : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K₂ := K₁ ⊔ IntermediateField.adjoin (FractionRing O) T
  have : FiniteDimensional (FractionRing O) K₂ := IntermediateField.finiteDimensional_sup _ _
  have h12 : K₁ ≤ K₂ := le_sup_left
  obtain ⟨O₁, hfin, hO⟩ := exists_finite_subalgebra O F K₂
  have hunit : ∀ u : Fˣ, (u : F) ∈ K₂ → S.valuation (u : F) = 1 → ∃ a : O₁ˣ, O₁.val.toRingHom a = u := by
    intro u hu hv
    have h1 : (u : F) ∈ O₁ := hO _ hu ((hS _).1 ((S.valuation_le_one_iff _).1 hv.le))
    have h2 : ((u⁻¹ : Fˣ) : F) ∈ O₁ := by
      rw [Units.val_inv_eq_inv_val]
      exact hO _ (K₂.inv_mem hu) ((hS _).1 ((S.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])))
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  let U : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ K₂}
      mul_mem' := fun ha hb => K₂.mul_mem ha hb
      one_mem' := K₂.one_mem
      inv_mem' := fun {u} hu => by
        change ((u⁻¹ : Fˣ) : F) ∈ K₂
        rw [Units.val_inv_eq_inv_val]
        exact K₂.inv_mem hu }
  let V : Subgroup Fˣ := (S.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom F)).ker
  obtain ⟨N₀, I, hI, h⟩ := GlobalTheory.Ex.NumD.exists_descent_subring O₁ F O₁.val.toRingHom Subtype.val_injective N A₀ hc
    (fun x hx y hy u hu => hunit _ (h12 (hθ x hx y hy u hu)) (vθ _ _ _))
    (fun x hx => hunit _ (h12 (hσ x hx)) (vσ _))
    (fun x hx => ⟨⟨_, hO _ (h12 (hth x hx)) ((hS _).1 (vth x))⟩, rfl⟩)
    (fun χ => hunit _ (h12 (hψ χ)) (vψ _))
  refine ⟨O₁, hfin, N₀, I, hI, fun i p' ⟨z, _, hz⟩ => h _ p' ?_ fun χ => hunit _ ?_ ?_⟩
  · rw [hz]
    exact A₀.mul_mem (hp i) (hc z)
  · have h1 : (p i).1.2.s χ ∈ U := s_mem_of_basis N U _ e (fun χ χ' => h12 (hθ _ (hc _) _ (hc _) _ (hp i)))
      (fun l => (le_sup_right : _ ≤ K₂) (IntermediateField.subset_adjoin _ _ ⟨(i, l), rfl⟩)) χ
    have hψU : ∀ χ, N.ψ χ ∈ U := fun χ => h12 (hψ χ)
    change p'.1.2.s χ ∈ U
    rw [hz, NumD.Gt.mul_s]
    exact U.div_mem (U.mul_mem h1 (U.div_mem (U.div_mem (hψU _) (hψU _)) (hψU _)))
      (h12 (hθ _ (hc _) _ (hp i) _ (hc z)))
  · refine s_mem_of_root N V vθ vψ (fun u hu => ?_) p' χ
    have : S.valuation (u : F) ^ k i = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val]; exact hu
    exact (pow_eq_one_iff_of_nonneg zero_le (hk i).ne').1 this

end GlobalTheory.Ex.TorsDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebraStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionClasses_descend_finite_algebra : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  first | exact @GlobalTheory.Ex.TorsDesc.descend | exact GlobalTheory.Ex.TorsDesc.descend | (intros; apply GlobalTheory.Ex.TorsDesc.descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FiniteValues
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_finset_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (B : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType B.hom] (p : TF (R := R) F ⟶ B) :
    ∃ S : Finset F, ∀ K : IntermediateField (FractionRing R) F, (S : Set F) ⊆ K →
      ∃ l : TF (R := R) K ⟶ B, extMap (R := R) (algebraMap K F) rfl ≫ l = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p.left := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p.left ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf, Spec.map_comp]
      exact Over.w p)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType R Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun K hK => ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hK (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(B.left, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Over.homMk (Spec.map f' ≫ hU.fromSpec) ?_, Over.OverMorphism.ext ?_⟩
  · change (Spec.map f' ≫ hU.fromSpec) ≫ B.hom = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hV r
  · change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
    rw [← hf, ← Spec.map_comp_assoc]
    rfl

theorem exists_finite_field_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  intro R _ _ D F _ _ _ N ν T hT
  haveI := D.P.isAb.proper
  choose S hS using fun x : N.A => exists_finset_point D.P.A (ν.eA x)
  let s : Set F := ⋃ x ∈ T, (S x : Set F)
  haveI : Finite s := (hT.biUnion fun x _ => (S x).finite_toSet).to_subtype
  let K := IntermediateField.adjoin (FractionRing R) s
  let f : K →+* F := algebraMap K F
  have hf : f.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) F := rfl
  let Φ : (TF (R := R) K ⟶ D.P.A) →* N.A :=
    MonoidHom.mk' (fun x => ν.eA.symm (extMap f hf ≫ x)) fun x y => by rw [MonObj.comp_mul, map_mul]
  have hΦ : ∀ x, ν.eA (Φ x) = extMap f hf ≫ x := fun x => ν.eA.apply_symm_apply _
  let J : (Sp K ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (spMap f ≫ ψ)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => by
    have h := ν.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F))
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (spMap f (IsLocalRing.closedPoint F))]
    exact h
  have hJ' : ∀ ψ, ν.J (spMap f ≫ ψ) = J ψ := fun _ => rfl
  have hm : ∀ a : K, f a ∈ K := fun a => a.2
  have hv : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), vF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [vF_ext f hJ hJ']; exact hm _
  have hw : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), sF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [sF_ext f hJ hJ']; exact hm _
  have hrig : rigVal ν ∈ K := by
    rw [rigVal, ← Over.w (extMap (R := R) f hf)]
    exact hv _ _
  refine ⟨K, Φ.range, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun x hx => ?_, fun χ => ?_, ?_, ?_, ?_, fun χ => ?_⟩
  · obtain ⟨l, hl⟩ := hS x K ((Set.subset_biUnion_of_mem (u := fun x => (S x : Set F)) hx).trans
      (IntermediateField.subset_adjoin _ _))
    exact ⟨l, ν.eA.injective ((hΦ l).trans hl)⟩
  · exact ⟨DegPre.cF D K (ν.eX χ), ν.eA.injective ((hΦ _).trans ((DVR.comp_cP D _ _).trans (ν.c_eq χ).symm))⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨u, rfl⟩
    rw [ν.θ_eq, hΦ, hΦ, hΦ, ← comp_lift, ← comp_lift]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    rw [ν.σ_eq, hΦ]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
    rw [eq_div_of_mul_eq h0 (ν.th_eq (Φ x)), hΦ]
    exact div_mem (hw _ _) hrig
  · rw [ν.ψ_eq]
    refine mul_mem ?_ hrig
    rw [← (extMap_jFK (R := R) f hf).trans (Category.id_comp _)]
    exact hv _ _

end GlobalTheory.FiniteValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_field_degenerationValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  first | exact @GlobalTheory.FiniteValues.exists_finite_field_of_values | exact GlobalTheory.FiniteValues.exists_finite_field_of_values | (intros; apply GlobalTheory.FiniteValues.exists_finite_field_of_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcF_values_add_ker_onto : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  intro hG E _ _ _ H D R _ _ F _ _ _ A n hn
  obtain ⟨-, -, hadd, -, hQ⟩ := hG R A.D₀ A.even A.bimult F A.N A.ν
  refine ⟨fun a b => ?_, fun a b => ?_, fun q => ?_⟩
  · obtain ⟨p, h₁, h₂, h₃⟩ := A.I.add n hn a b
    obtain ⟨q, hq⟩ := ((hQ n).1 p).exists
    have e : q = A.q n a * A.q n b := by
      refine Subtype.ext (Prod.ext ?_ ((hadd _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hq.2).1 h₂))
      apply Multiplicative.toAdd.injective
      apply A.ν.eX.injective
      rw [hq.1, h₁, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
      rfl
    rw [← e]
    exact ((hQ n).2.2 _ _ _ _ hq (A.hq n _)).1 h₃
  · rw [← (hQ n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
    exact A.I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 q
    obtain ⟨a, ha⟩ := A.I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (A.hq n a) hp₀).1 ha⟩

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective : BrGtSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (A : ArcF D R F) (n : ℕ), 0 < n → (∀ a b, A.N.QEq (A.q n a * A.q n b) (A.q n (a + b))) ∧ (∀ a b, A.N.QEq (A.q n a) (A.q n b) ↔ ∃ e, a = b + n • e) ∧ ∀ p, ∃ a, A.N.QEq (A.q n a) p := by
  first | exact @GlobalTheory.Ex.arcF_values_add_ker_onto | exact GlobalTheory.Ex.arcF_values_add_ker_onto | (intros; apply GlobalTheory.Ex.arcF_values_add_ker_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGe
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.TwistCoset

theorem tx_eq_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  refine Eq.trans (tsum_congr fun χ => ?_) ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)
  exact (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2

variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {l : ℕ}

theorem twRel_mul {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a') (hb : TwRel β u r b b') :
    TwRel β u r (a * b) (a' * b') := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨congrArg₂ (fun s t : Multiplicative N.X => s * t) a1 b1,
    congrArg₂ (fun s t : N.A => s * t) a2 b2, fun z => ?_⟩
  change a'.1.2.s z * b'.1.2.s z / N.θ (N.c z) a'.1.2.b b'.1.2.b =
    a.1.2.s z * b.1.2.s z / N.θ (N.c z) a.1.2.b b.1.2.b * r ^ β.be (a.1.1.toAdd + b.1.1.toAdd) z
  rw [a2, b2, a3, b3, map_add (f := _), LinearMap.add_apply, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twRel_qEq (hr : r ^ l = u) {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a')
    (hb : TwRel β u r b b') (h : N.QEq a b) : (N.twist β u).QEq a' b' := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (w : N.X) => ?_)⟩
  · rw [a1, b1]; exact h1
  · refine b2.trans ?_
    rw [h2]
    exact congrArg (fun s : N.A => s * N.c z) a2.symm
  · change b'.1.2.s w = a'.1.2.s w * (N.twist β u).τ z w / N.θ (N.c w) a'.1.2.b (N.c z)
    have e : r ^ ((l : ℤ) * β.be z w) = u ^ β.be z w := by rw [zpow_mul, zpow_natCast, hr]
    rw [b3, a3, a2, N.twist_τ, h1, h2, NumD.Gt.mul_s, NumD.io_s, NumD.io_b, map_add (f := _), LinearMap.add_apply, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul, zpow_add, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]; abel

theorem exists_twRel_of_eq_one (r : Oˣ) (h : (N.twist β u).QT l) (h1 : h.1.1 = 1) {e : ℕ} (he : h.1.2 ^ e = 1) :
    ∃ h₀ : N.QT l, h₀ ^ e = 1 ∧ TwRel β u r h₀ h := by
  let f : (N.twist β u).Gt →* N.Gt := MonoidHom.mk' (fun g => ⟨g.b, g.s, g.mult⟩) fun _ _ => rfl
  have hl : h.1.2 ^ l = 1 := by
    rw [(N.twist β u).mem_QT.1 h.2, h1]; exact (N.twist β u).io_zero
  refine ⟨⟨(1, f h.1.2), ?_⟩, Subtype.ext (Prod.ext (one_pow e) ?_), h1, rfl, fun z => ?_⟩
  · rw [NumD.mem_QT, ← map_pow, hl, map_one]; exact N.io_zero.symm
  · change f h.1.2 ^ e = 1
    rw [← map_pow, he, map_one]
  · change h.1.2.s z = h.1.2.s z * r ^ β.be 0 z
    rw [map_zero, LinearMap.zero_apply, zpow_zero, mul_one]

variable {La : Type} [AddCommGroup La] {q : La → N.QT l}

theorem qEq_zero (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) : N.QEq (q 0) 1 := by
  have E : Equivalence (N.QEq (k := l)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have := TateInh.qEq_mul N (hq 0 0) (E.refl (q 0)⁻¹)
  rwa [add_zero, mul_inv_cancel_right, mul_inv_cancel] at this

theorem qEq_nsmul (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (a : La) (e : ℕ) : N.QEq (q a ^ e) (q (e • a)) := by
  have E : Equivalence (N.QEq (k := l)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact E.symm (qEq_zero hq)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact E.trans (TateInh.qEq_mul N ih (E.refl _)) (hq _ _)

theorem qEq_pow {a b : N.QT l} (h : N.QEq a b) (e : ℕ) : N.QEq (a ^ e) (b ^ e) := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact ⟨0, by simp, by simp⟩
  | succ e ih => rw [pow_succ, pow_succ]; exact TateInh.qEq_mul N ih h

theorem eq_zero_of_pow_nsmul {n : ℕ} (hn : ∀ a : La, n • a = 0 → a = 0) (e : ℕ) (a : La) (h : n ^ e • a = 0) :
    a = 0 := by
  induction e with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih => exact ih (hn _ (by rwa [pow_succ', mul_smul] at h))

end GlobalTheory.TwistCoset


open GlobalTheory.TwistCoset in
theorem GlobalTheory.twist_tx_coset_norm_ge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  intro C _ _ _ _ N k β u r qf n g j hp ho hn hj hu hr hI hqf hT La _ q htf hadd hker honto p hpq
  have hm : Odd (n ^ j) := ho.pow
  have E : Equivalence (N.QEq (k := (n ^ j) ^ 2)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have hP : qf.PosDef := GlobalTheory.CosetCrit.posDef_of_tendsto (X := N.X) hI.pos
  have key : ∀ (x : La) (χ₀ : N.X), (∀ χ : N.X, qf ((q x).1.1.toAdd + n ^ j • χ₀) ≤ qf ((q x).1.1.toAdd + n ^ j • χ)) →
      ∃ e, Real.exp (-(qf ((q x).1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤
        ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • e))‖ := fun x χ₀ h₀ => by
    obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge (N := N.twist β u) (q := qf) hI hp ho hn hT hj (p x)
      (χ₀ := χ₀) (by rw [(hpq x).1]; exact h₀)
    obtain ⟨h', h4, h5⟩ := exists_twRel_of_eq_one r h h1 h2
    obtain ⟨a, ha⟩ := honto h'
    have h6 : N.QEq (q (n ^ (j + 1) • a)) (q 0) := by
      have := qEq_pow ha (n ^ (j + 1))
      rw [h4] at this
      exact E.trans (E.symm (qEq_nsmul hadd a _)) (E.trans this (E.symm (qEq_zero hadd)))
    obtain ⟨e, he⟩ := (hker _ _).1 h6
    have h7 : a = n ^ (j - 1) • e := by
      refine sub_eq_zero.1 (eq_zero_of_pow_nsmul htf (j + 1) _ ?_)
      rw [smul_sub, he, zero_add, ← mul_smul, ← pow_add, ← pow_mul, show j + 1 + (j - 1) = j * 2 by omega, sub_self]
    refine ⟨e, ?_⟩
    have h8 : N.QEq (q x * h') (q (x + a)) := E.trans (TateInh.qEq_mul N (E.refl _) (E.symm ha)) (hadd x a)
    rw [← h7, tx_eq_of_qEq _ hm (twRel_qEq hr (twRel_mul (hpq x) h5) (hpq (x + a)) h8)]
    rw [(hpq x).1] at h3
    exact h3
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨z, hz, -⟩ := E.symm (qEq_zero hadd)
    have hz0 : (q 0).1.1.toAdd + n ^ j • (-(n ^ j • z)) = 0 := by
      rw [hz, smul_neg, ← mul_smul, ← sq]
      exact (congrArg (· + -((n ^ j) ^ 2 • z)) (zero_add _)).trans (add_neg_cancel _)
    obtain ⟨e, he⟩ := key 0 (-(n ^ j • z)) fun χ => by rw [hz0, map_zero]; exact hP.nonneg _
    rw [hz0, map_zero, zero_div, neg_zero, Real.exp_zero] at he
    exact ⟨_, he⟩
  · obtain ⟨χ₀, h₀⟩ := (GlobalTheory.CosetCrit.tendsto_class (X := N.X) (q := qf) hI.pos (q x).1.1.toAdd
      hm.pos.ne').exists_forall_le
    obtain ⟨e, he⟩ := key x χ₀ h₀
    refine ⟨e, le_trans ?_ he⟩
    have h1 := h₀ 0
    rw [smul_zero, add_zero, hqf (q x).1.1.toAdd] at h1
    have h2 := hP.nonneg ((q x).1.1.toAdd + n ^ j • χ₀)
    set y := (q x).1.1.toAdd
    have hB : 0 ≤ β.be y y := by
      by_cases hy : y = 0
      · rw [hy, map_zero]
      · exact (β.pos y hy).le
    have h0 : 0 < ‖(u : C)‖ := norm_pos_iff.2 u.ne_zero
    have hL : Real.log ‖(u : C)‖ < 0 := Real.log_neg h0 hu
    have hc : (((β.be y y).toNat : ℕ) : ℝ) = (β.be y y : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hB]
    have hB' : (0 : ℝ) ≤ (β.be y y : ℝ) := by exact_mod_cast hB
    have hsq : (1 : ℝ) ≤ ((n ^ j : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm.pos)
    have h3 := div_le_self h2 hsq
    rw [← Real.exp_log (pow_pos h0 _), Real.log_pow, hc]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hB' (neg_pos.2 hL).le]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGeStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_tx_coset_norm_ge_alt : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  first | exact @GlobalTheory.twist_tx_coset_norm_ge | exact GlobalTheory.twist_tx_coset_norm_ge | (intros; apply GlobalTheory.twist_tx_coset_norm_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeries
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcSeries

theorem exists_root_system {K : Type} [Field K] [IsAlgClosed K] (u : Kˣ) : ∃ r, Roots u r := by
  have hs : ∀ (n : ℕ) (x : Kˣ), ∃ y : Kˣ, y ^ (n + 1) = x := fun n x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) n.succ_pos
    exact ⟨Units.mk0 y fun e => x.ne_zero (by rw [← hy, e]; simp), Units.ext hy⟩
  choose rt hrt using hs
  let s : ℕ → Kˣ := fun n => Nat.rec u (fun n x => rt n x) n
  have h1 : ∀ n d, s (n + d) ^ ((n + d).factorial / n.factorial) = s n := fun n d => by
    induction d with
    | zero => simp [Nat.div_self n.factorial_pos]
    | succ d ih =>
      rw [← add_assoc, Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)),
        pow_mul]
      exact (congrArg (· ^ _) (hrt _ _)).trans ih
  refine ⟨fun n => s n ^ (n.factorial / n), ?_, fun n m hn hm => ?_⟩
  · change s 1 ^ 1 = u
    exact hrt 0 u
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_right n hm)
    have a := h1 n d
    rw [← hd] at a
    change (s (n * m) ^ ((n * m).factorial / (n * m))) ^ m = s n ^ (n.factorial / n)
    rw [← a, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨p, hp⟩ := Nat.dvd_factorial (Nat.mul_pos hn hm) le_rfl
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hn le_rfl
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)
    have e1 : (n * m).factorial / (n * m) = p := by rw [hp]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos hn hm)
    have e2 : n.factorial / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
    have e3 : (n * m).factorial / n.factorial = t := by rw [ht]; exact Nat.mul_div_cancel_left _ n.factorial_pos
    rw [e1, e2, e3]
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [hp, hq] at ht
    linarith

theorem base_local {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    IsLocalRing O ∧ IsPrincipalIdealRing O := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_reps {n : ℕ} (hn : 0 < n) : ∃ (Ix : Type) (_ : Finite Ix) (t : Ix → D.La), ∀ a, ∃ i e, t i = a + n • e := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let P : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • LinearMap.id)
  have : Finite (D.La ⧸ P) := Module.finite_of_fg_torsion (M := D.La ⧸ P) fun x => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero P).2 ⟨x, rfl⟩
  refine ⟨D.La ⧸ P, this, Quotient.out, fun a => ?_⟩
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq P).1 (Quotient.out_eq (Submodule.Quotient.mk a : D.La ⧸ P))
  exact ⟨_, e, by rw [← natCast_zsmul]; exact (eq_add_of_sub_eq' he.symm)⟩

theorem eq_zero_of_nsmul {n : ℕ} (hn : n ≠ 0) (a : D.La) (h : n • a = 0) : a = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun x => D.EF x y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hn, false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

theorem exists_series : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → Nonempty (Ser a K (algebraMap _ K)) := by
  intro hHV _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB K _ _ _ _ _ _ hK
  have hL : Laws := hHV.1.1
  have hL2 : Laws2 := hHV.1.2.1
  have gt := GlobalTheory.T.torus_torsion_points_correspond_values
  have wp := GlobalTheory.T.torsionPairing_values_of_familiesValues gt (GlobalTheory.T.families_values_correspond hL hL2)
  obtain ⟨_, _⟩ := base_local hB
  let F := AlgebraicClosure (FractionRing O')
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR O' ϖ hB F
  have hin : ∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S₀ := fun r =>
    (hS₀ _).2 (by rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap)
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.exists_arcIsometry_torsion_integralGauge hL gt E H D l Xo c W₀ Y O' b ϖ a hB F S₀ hin
  let io : F →+* K := (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).toRingHom
  have hio : io.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') K :=
    (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).comp_algebraMap
  obtain ⟨A, -, I₀, l₀, -, -, x₀, q₀⟩ :=
    GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB F K io hio ⊤ (fun _ => trivial) A₀
  have hinj := FaithfulSMul.algebraMap_injective (PowerSeries O') K
  have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  obtain ⟨r, hr⟩ := exists_root_system (Units.mk0 _ hX)
  have hr1 : (r 1 : K) = algebraMap (PowerSeries O') K PowerSeries.X := by rw [hr.1]; rfl
  obtain ⟨iθ, iσ, ith, iψ⟩ := GlobalTheory.T.integralGauge_values_are_valuationUnits O' a.D₀ F S₀ hin A₀.N A₀.ν hA₀
  have level : ∀ (m j : ℕ) (z : D.La), ∃ (R₁ : Subalgebra (PowerSeries O') K) (v w : D.La → K), Odd m → 0 < j →
      Module.Finite (PowerSeries O') R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O') io A₀.N A₀.be.be m j (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j)) v w := by
    intro m j z
    by_cases h : Odd m ∧ 0 < j
    swap
    · exact ⟨⊥, 0, 0, fun a b => (h ⟨a, b⟩).elim⟩
    obtain ⟨hm, hj⟩ := h
    have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
    obtain ⟨Ix, _, t, ht⟩ := exists_reps D hm2
    let k : Option Ix → ℕ := fun i => i.elim j fun _ => m ^ 2
    let p : ∀ i, A₀.N.QT (k i) := fun i => match i with
      | none => A₀.q j z
      | some i => A₀.q (m ^ 2) (t i)
    obtain ⟨K₁, A₁, f1, f2, f3, f4, f5, f6, f7⟩ :=
      GlobalTheory.T.exists_finiteDimensional_field_degenerationValues O' a.D₀ F A₀.N A₀.ν (Set.range fun i => (p i).1.2.b) (Set.finite_range _)
    obtain ⟨O₁, _, N₀, I, hI, hp⟩ := GlobalTheory.T.torsionClasses_descend_finite_algebra O' F S₀ hS₀ A₀.N K₁ A₁ f1 f3 f4 f5 f6 f7 iθ iσ ith (iψ a.gen) (Option Ix) k p
      (fun i => by cases i; exacts [hj, hm2]) fun i => f2 _ ⟨i, rfl⟩
    have : FaithfulSMul O' F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
      rw [IsScalarTower.algebraMap_eq O' (FractionRing O') F]
      exact (algebraMap (FractionRing O') F).injective.comp (IsFractionRing.injective O' _))
    have : Module.Free O' O₁ := Module.free_of_finite_type_torsion_free'
    obtain ⟨R₁, v, w, h⟩ := exists_sums (O := O') O₁.val.toRingHom io (fun x => by
        rw [← hK, ← hio]; rfl) A₀.be.be hm hj (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j))
      (by rw [← Units.val_pow_eq_pow_val, hr.pow (Nat.mul_pos hm2 hj)]; rfl) I hI
      (fun x => by
        obtain ⟨i, e, he⟩ := ht x
        exact hp (some i) _ (((GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' F A₀.arc _ hm2).2.1 _ _).2 ⟨e, he⟩))
      (hp none _ ((A₀.N.qEq_equivalence _).refl _))
    exact ⟨R₁, v, w, fun _ _ => h⟩
  choose R₁ v w hlev using level
  have ext : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [Algebra (FractionRing O') C] (gam : K →+* C),
      (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) →
      (∀ f, ‖gam (algebraMap (PowerSeries O') K f)‖ ≤ 1) → ∃ A' : Lift a C, A'.ν.IntN ∧ A.arc.Over gam A'.arc ∧
        ∃ I : NumD.Hom (gam.comp io) A₀.N A'.N, I.lam = 1 ∧ (∀ y z, A'.be.be (I.e y) (I.e z) = A₀.be.be y z) ∧
          ∀ n x, (A'.q n x).1.1.toAdd = I.e (A₀.q n x).1.1.toAdd ∧ I.Rel (A₀.q n x).1.2 (A'.q n x).1.2 := by
    intro C _ _ _ _ gam h1 h2
    obtain ⟨S, hS⟩ := exists_ball C
    obtain ⟨A', hA', I₁, l₁, r₁, z₁, x₁, q₁⟩ := GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB K C gam
      (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x => (congrArg gam (hK x)).trans (h1 x).symm))
      S (fun x => (hS _).2 (by rw [h1]; exact h2 _)) A
    refine ⟨A', ⟨S, hS, hA'⟩, ⟨I₁, r₁, z₁, fun s y => A'.ν.eX.injective ?_, fun n x _ =>
      ⟨A'.q n x, (q₁ n x).1, (q₁ n x).2, (A'.N.qEq_equivalence _).refl _⟩⟩, homComp I₀ I₁ _ fun _ => rfl, ?_, fun y z => ?_,
      fun n x => ⟨(q₁ n x).1.trans (congrArg I₁.e (q₀ n x).1), homComp_rel _ _ _ _ (q₀ n x).2 (q₁ n x).2⟩⟩
    · change A'.ν.eX (I₁.e (A.ν.eX.symm (s • A.ν.eX y))) = A'.ν.eX (A'.ν.eX.symm (s • A'.ν.eX (I₁.e y)))
      exact ((x₁ _).trans (A.ν.eX.apply_symm_apply _)).trans
        ((A'.ν.eX.apply_symm_apply _).trans (congrArg (s • ·) (x₁ y))).symm
    · change I₁.lam * Units.map _ I₀.lam = 1
      rw [l₁, l₀, map_one, _root_.mul_one]
    · change A'.be.be (I₁.e (I₀.e y)) (I₁.e (I₀.e z)) = _
      rw [A'.be_eq, A₀.be_eq, x₁, x₁, x₀, x₀]
  have hrm : ∀ m j, Odd m → 0 < j → r (m ^ 2) = r (m ^ 2 * j) ^ j ∧ r j = r (m ^ 2 * j) ^ m ^ 2 := fun m j hm hj =>
    ⟨(hr.2 _ _ (pow_pos hm.pos 2) hj).symm, by rw [mul_comm]; exact (hr.2 _ _ hj (pow_pos hm.pos 2)).symm⟩
  refine ⟨⟨⟨inferInstance, hinj, fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x, hK⟩, A, r, hr1,
    ⟨rfl, hr.2⟩, fun m => v m 1 0, w, ?_, ?_⟩⟩
  · intro n j hp ho hu hj S hS
    have hm : Odd (n ^ j) := ho.pow
    obtain ⟨hfin, hmem, hsum⟩ := hlev (n ^ j) 1 0 hm one_pos
    have hvS : ∀ x, v (n ^ j) 1 0 x ∈ S := fun x =>
      mem_of_isIntegral S hS ((Algebra.IsIntegral.isIntegral (⟨_, hmem x⟩ : R₁ (n ^ j) 1 0)).map (R₁ _ _ _).val)
    have key : ∀ e : ℕ, ∃ (C : Type) (_ : NormedField C) (gam : K →+* C) (u : ℝ), 0 < u ∧ u < 1 ∧
        (∀ x, S.valuation (v (n ^ j) 1 0 x) < 1 → ‖gam (v (n ^ j) 1 0 x)‖ < 1 ∧
          (S.valuation (algebraMap (PowerSeries O') K PowerSeries.X) = 1 → ‖gam (v (n ^ j) 1 0 x)‖ ≤ u ^ e)) ∧
        (∃ x, 1 ≤ ‖gam (v (n ^ j) 1 0 x)‖) ∧ ∀ x, ∃ h, u ^ (A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
          (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat ≤ ‖gam (v (n ^ j) 1 0 (x + n ^ (j - 1) • h))‖ := by
      intro e
      obtain ⟨C, _, _, _, _, gam, g1, g2, g3⟩ := GlobalTheory.T.exists_valuedField_valuationCentre_le_pow (PowerSeries O') K PowerSeries.X
        (fun h => not_isUnit_zero (by simpa using h.map PowerSeries.constantCoeff : IsUnit (0 : O')))
        PowerSeries.X_ne_zero _ hfin S hS e
      letI : Algebra (FractionRing O') C := (gam.comp (algebraMap _ K)).toAlgebra
      have h1 : ∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) =
          gam (algebraMap (PowerSeries O') K (PowerSeries.C x)) := fun x => congrArg gam (hK x)
      have hce : CExt O' ⊥ C := ⟨fun x => by rw [h1]; exact g1 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx]; simp⟩
      obtain ⟨A', hN, -, I, hI, hβ, hq⟩ := ext C gam h1 g1
      let r' : ℕ → Cˣ := fun n => Units.map gam.toMonoidHom (r n)
      have hu' : (r' 1 : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) := congrArg gam hr1
      have hu1 : ‖(r' 1 : C)‖ < 1 := hu' ▸ g2
      have hpow : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = r' 1 := by
        rw [← map_pow, hr.pow (pow_pos hm.pos 2), ← hr.1]
      have hn : ‖(n : C)‖ = 1 := by
        obtain ⟨y, hy⟩ := hu.exists_right_inv
        have a1 := hce.1 n
        have a2 := hce.1 y
        have a3 := congrArg (fun x => ‖algebraMap (FractionRing O') C (algebraMap O' _ x)‖) hy
        simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a1 a3
        nlinarith [norm_nonneg (n : C)]
      obtain ⟨qf, hq1, hq2⟩ := (GlobalTheory.T.arcTorsionValues_norms_integral_positive E H D l Xo c W₀ Y O' b ϖ a hB C hce A' hN).2.2 (r' 1) hu1
      choose p hp' using fun x => (existsUnique_twRel A'.be (r' 1) _ hpow (A'.q _ x)).exists
      obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' C A'.arc _ (pow_pos hm.pos 2)
      obtain ⟨c1, c2⟩ := GlobalTheory.T.twist_tx_coset_norm_ge_alt C A'.N _ A'.be (r' 1) _ qf n _ j hp ho hn hj hu1 hpow hq1 hq2
        (GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) O' a.D₀ a.even a.bimult C hce A'.N A'.ν hN n hp ho hn)
        D.La (A'.q _) (eq_zero_of_nsmul D hp.ne_zero) t1 t2 t3 p hp'
      have hv := (hsum C gam g1 g2 A'.N I _ A'.be hI hβ (r' 1) (r' ((n ^ j) ^ 2)) (r' 1) hu'
        (by rw [← (hrm _ 1 hm one_pos).1]; rfl) (by rw [← (hrm _ 1 hm one_pos).2]; rfl) (A'.q _) p (hq _) hp').1
      refine ⟨C, inferInstance, gam, ‖(r' 1 : C)‖, norm_pos_iff.2 (r' 1).ne_zero, hu1,
        fun x hx => hu' ▸ g3 _ (hmem x) hx, by simpa only [hv] using c1, fun x => ?_⟩
      simpa only [hv, (hq _ x).1, hβ] using c2 x
    have hlt : ∀ x, S.valuation (v (n ^ j) 1 0 x) ≠ 1 → S.valuation (v (n ^ j) 1 0 x) < 1 := fun x h =>
      lt_of_le_of_ne ((S.valuation_le_one_iff _).2 (hvS x)) h
    refine ⟨hvS, ?_, fun hXu x => ?_⟩
    · obtain ⟨C, _, gam, u, -, -, k1, ⟨x, hx⟩, -⟩ := key 0
      exact ⟨x, not_not.1 fun h => (k1 x (hlt x h)).1.not_ge hx⟩
    · obtain ⟨C, _, gam, u, u0, u1, k1, -, k2⟩ := key ((A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
        (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat + 1)
      obtain ⟨h, hh⟩ := k2 x
      exact ⟨h, not_not.1 fun hne => (hh.trans ((k1 _ (hlt _ hne)).2 hXu)).not_gt
        (pow_lt_pow_right_of_lt_one₀ u0 u1 (Nat.lt_succ_self _))⟩
  · intro C _ _ _ _ _ gam u h1 g1 hu hu1
    obtain ⟨A', hN, hO, I, hI, hβ, hq⟩ := ext C gam h1 g1
    refine ⟨A', fun n => Units.map gam.toMonoidHom (r n), hN, hO, fun _ => rfl, fun m hm p hp => ?_⟩
    have S := fun j z hj => (hlev m j z hm hj).2.2 C gam g1 (by rw [hu] at hu1; exact hu1) A'.N I _ A'.be hI hβ u
      (Units.map gam.toMonoidHom (r (m ^ 2))) (Units.map gam.toMonoidHom (r j)) hu
      (by rw [← (hrm _ j hm hj).1]; rfl) (by rw [← (hrm _ j hm hj).2]; rfl) (A'.q _) p (hq _) hp
    exact ⟨⟨1, fun x => by rw [Units.val_one, _root_.one_mul]; exact (S 1 0 one_pos).1 x⟩,
      fun j hj z q hq' => (S j z hj).2 (A'.q j z) q (hq j z).1 (hq j z).2 hq'⟩

end GlobalTheory.ArcSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeriesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcSeries_integral_algebraic_over_powerSeries : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → Nonempty (Ser a K (algebraMap _ K)) := by
  first | exact @GlobalTheory.ArcSeries.exists_series | exact GlobalTheory.ArcSeries.exists_series | (intros; apply GlobalTheory.ArcSeries.exists_series <;> assumption)
end
