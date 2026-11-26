module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairs
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtensionSplitSpecialFibrePoint
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalChartPointsOverFieldPoint
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NotNondegenerateOfDegenerateSeriesDirection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonality
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonality
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair


set_option maxHeartbeats 800000 in
theorem transfer_of_unif : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  intro W _ _ I D Av G _ _ U Ω _ β hβ τ hτ n A _ _ x y h
  let β₀ : W ⧸ I ^ (0 + 1) →+* A := Ideal.Quotient.lift _ ((algebraMap Ω A).comp β) fun a ha => by
    rw [zero_add, pow_one] at ha
    rw [RingHom.comp_apply, hβ a ha, map_zero]
  let T₀ : Over (Spec (CommRingCat.of (W ⧸ I ^ (0 + 1)))) := Over.mk (spMap β₀)
  have hT : T₀.hom ≫ Out.thick W I 0 = (overAt (spMap β) A).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let ρ : overAt (spMap β) A ⟶ Over.mk (T₀.hom ≫ Out.thick W I 0) :=
    Over.homMk (𝟙 (Sp A)) ((Category.id_comp _).trans hT)
  let φ : (T₀ ⟶ Out.thickObj W I 0 G) →* (overAt (spMap β) A ⟶ G) :=
    (preHom ρ).comp (UU.toBaseHom (UU.toBase_mul_pullback G (Out.thick W I 0)) T₀)
  have hφ : ∀ r, (φ r).left = r.left ≫ (Out.fstG I 0 G).left := fun r => Category.id_comp _
  have hψ : ∀ r, (τ A (φ r)).left = r.left ≫ (U.gt 0).pG.left := fun r => hτ A _ _ (hφ r).symm
  have inj : Function.Injective φ := fun r s e => Over.OverMorphism.ext (pullback.hom_ext
    ((hφ r).symm.trans ((congrArg (·.left) e).trans (hφ s))) ((Over.w r).trans (Over.w s).symm))
  have surj : Function.Surjective φ := fun v =>
    ⟨Over.homMk (pullback.lift v.left T₀.hom ((Over.w v).trans hT.symm)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  obtain ⟨x, rfl⟩ := surj x
  obtain ⟨y, rfl⟩ := surj y
  have hx : x ^ n = 1 := inj ((map_pow φ x n).trans (h.1.trans (map_one φ).symm))
  have hy : y ^ n = 1 := inj ((map_pow φ y n).trans (h.2.1.trans (map_one φ).symm))
  refine ⟨by rw [← map_pow, h.1, map_one], by rw [← map_pow, h.2.1, map_one], fun z J hJ => ?_⟩
  obtain ⟨N, hN⟩ := UU.exists_good_pt U.LG.isLB (Z := Sp A) z
  have key : ∀ a b d : T₀ ⟶ Out.thickObj W I 0 G,
      cubV D.toPre.cub z J (τ A (φ a)) (τ A (φ b)) (τ A (φ d)) *
        TorusInvariance.wVal U 0 z J N (a * b).left * TorusInvariance.wVal U 0 z J N (a * d).left *
        TorusInvariance.wVal U 0 z J N (b * d).left * TorusInvariance.wVal U 0 z J N (1 : T₀ ⟶ _).left =
      TorusInvariance.wVal U 0 z J N (a * b * d).left * TorusInvariance.wVal U 0 z J N a.left *
        TorusInvariance.wVal U 0 z J N b.left * TorusInvariance.wVal U 0 z J N d.left *
        cubV U.cubG z N (φ a) (φ b) (φ d) := by
    intro a b d
    have e := TorusInvariance.cube_val U (T := T₀) ![a, b, d] hJ hN
    have t₁ : WCub.tri (Out.thick W I 0) (U.gt 0).pG ![a, b, d] =
        (lift (τ A (φ a)) (lift (τ A (φ b)) (τ A (φ d)))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hψ] <;> rfl
    have t₂ : WCub.tri (Out.thick W I 0) (Out.fstG I 0 G) ![a, b, d] =
        (lift (φ a) (lift (φ b) (φ d))).left := hom_ext_triple _ fun i => by
      rw [← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, lift_fst,
        lift_snd_assoc, lift_snd, hφ] <;> rfl
    have p : ∀ k : thK.{0}, (psum (Out.thickObj W I 0 G) ![a, b, d] k.down).left =
        (lift a (lift b d)).left ≫ thφ _ (x3 (Out.thickObj W I 0 G)) k := fun k =>
      congrArg (·.left) ((congrArg (fun q => psum _ q k.down) (funext fun i => by
        fin_cases i <;> simp [x3, preHom])).trans
        (psum_hom (preHom (lift a (lift b d))) (x3 (Out.thickObj W I 0 G)) k.down).symm)
    rw [t₁, t₂] at e
    simp only [p] at e
    exact UU.cub_alg (e.trans (congrArg₂ (· * ·) (prod_cub a b d (TorusInvariance.wVal U 0 z J N)) rfl))
  refine UU.cubN_ratio_twist ((τ A).comp φ) (fun r => TorusInvariance.wVal U 0 z J N r.left)
    (θ := cubV D.toPre.cub z J) (θ' := fun a b d => cubV U.cubG z N (φ a) (φ b) (φ d)) key hx hy ?_
  simpa only [cubN, map_mul, map_pow, map_one] using h.2.2 z N hN

end GlobalTheory.AlphaPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonalityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_projection_respects_orthogonality : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  first | exact @GlobalTheory.AlphaPair.transfer_of_unif | exact GlobalTheory.AlphaPair.transfer_of_unif | (intros; apply GlobalTheory.AlphaPair.transfer_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedField
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.ResField

variable {C : Type} [Field C] (V : VF C)

theorem nonneg (x : V.RR) : 0 ≤ V.v (x : C) := by
  have h : ((0 : ℝ) : WithTop ℝ) ≤ V.v (x : C) := x.2
  simpa using h

def mm : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {x y} hx hy => V.v.map_lt_add hx hy
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left (nonneg V c))

theorem mm_isMaximal : (mm V).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · have h1 : 0 < V.v ((1 : V.RR) : C) := h
    simp at h1
  · have hx' : ¬ 0 < V.v (x : C) := hx
    have hx0 : V.v (x : C) = 0 := le_antisymm (not_lt.mp hx') (nonneg V x)
    have hne : (x : C) ≠ 0 := by
      intro h
      rw [h, AddValuation.map_zero] at hx0
      exact WithTop.top_ne_zero hx0
    have hinv : ((0 : ℝ) : WithTop ℝ) ≤ V.v ((x : C)⁻¹) := by
      rw [AddValuation.map_inv, hx0]
      simp
    let y : V.RR := ⟨(x : C)⁻¹, hinv⟩
    have hyx : y * x = 1 := Subtype.ext (by simp [y, hne])
    rw [← hyx]
    exact J.mul_mem_left y hxJ

theorem integers : (AddValuation.toValuation V.v).Integers V.RR :=
  Valuation.integer.integers (AddValuation.toValuation V.v)

theorem isAlgClosed_of_surjective [IsAlgClosed C] {Ω : Type} [Field Ω] (ρ : V.RR →+* Ω)
    (hρ : Function.Surjective ρ) : IsAlgClosed Ω := by
  refine IsAlgClosed.of_exists_root Ω fun p hp hirr => ?_
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective ρ hρ p)) hp
  have hdeg : (q.map (algebraMap V.RR C)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (integers V).hom_inj, hqdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral V.RR z := ⟨q, hqmon, hz⟩
  obtain ⟨y, rfl⟩ := (integers V).exists_of_le_one ((integers V).mem_of_integral hint)
  rw [Polynomial.eval₂_at_apply] at hz
  have hy : q.eval y = 0 := (integers V).hom_inj (by rw [hz, map_zero])
  refine ⟨ρ y, ?_⟩
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

theorem exists_residueField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  intro C _ V _
  have := mm_isMaximal V
  let _ : Field (V.RR ⧸ mm V) := Ideal.Quotient.field (mm V)
  have hl : ((V.l : ℕ) : V.RR ⧸ mm V) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (mm V)), Ideal.Quotient.eq_zero_iff_mem]
    show 0 < V.v (((V.l : ℕ) : V.RR) : C)
    have hc : (((V.l : ℕ) : V.RR) : C) = ((V.l : ℕ) : C) := by simp
    rw [hc, V.v_l]
    exact zero_lt_one
  have : CharP (V.RR ⧸ mm V) V.l := (CharP.charP_iff_prime_eq_zero V.l_prime).2 hl
  exact ⟨V.RR ⧸ mm V, inferInstance, isAlgClosed_of_surjective V _ Ideal.Quotient.mk_surjective,
    inferInstance, Ideal.Quotient.mk (mm V), fun x => Ideal.Quotient.eq_zero_iff_mem⟩

end GlobalTheory.AlphaPair.ResField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosed_residueField_valuedField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  first | exact @GlobalTheory.AlphaPair.ResField.exists_residueField | exact GlobalTheory.AlphaPair.ResField.exists_residueField | (intros; apply GlobalTheory.AlphaPair.ResField.exists_residueField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootTorusPointNilpotentAugmentedExtStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootTorusPointNilpotentAugmentedExt
open Polynomial

namespace GlobalTheory.TorusRoot

theorem exists_root_one (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
    (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π))
    (a : Aˣ) (ha : π a.val = 1) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      π' s.val = 1 ∧ s ^ p = Units.map (f : A →* A') a := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : Nontrivial A := π.toRingHom.domain_nontrivial
  let P : A[X] := X ^ p - C a.val
  have hP : P.Monic := monic_X_pow_sub_C _ hp0
  let f : A →ₐ[Ω] AdjoinRoot P := IsScalarTower.toAlgHom Ω A (AdjoinRoot P)
  have hf : ∀ x, f x = AdjoinRoot.of P x := fun x => rfl
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hx
    by_contra hx0
    refine hP.not_dvd_of_degree_lt (C_ne_zero.2 hx0) ?_ hx
    rw [degree_C hx0, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp0)]
    exact_mod_cast Nat.pos_of_ne_zero hp0
  have hev : P.eval₂ (π : A →+* Ω) 1 = 0 := by
    simp [P, eval₂_sub, ha]
  let g : AdjoinRoot P →+* Ω := AdjoinRoot.lift (π : A →+* Ω) 1 hev
  have hg : ∀ x, g (f x) = π x := fun x => by
    rw [hf]; exact AdjoinRoot.lift_of hev
  have hgr : g (AdjoinRoot.root P) = 1 := AdjoinRoot.lift_root hev
  let π' : AdjoinRoot P →ₐ[Ω] Ω :=
    { g with
      commutes' := fun c => by
        have : algebraMap Ω (AdjoinRoot P) c = f (algebraMap Ω A c) := (f.commutes c).symm
        change g _ = _
        rw [this, hg, π.commutes] }
  have hroot : AdjoinRoot.root P ^ p = f a.val := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, eval₂_sub, eval₂_X_pow, eval₂_C] at h
    exact sub_eq_zero.1 h
  have hu : IsUnit (AdjoinRoot.root P) := by
    rw [← isUnit_pow_iff hp0, hroot]
    exact a.isUnit.map f
  haveI : Nontrivial (AdjoinRoot P) := g.domain_nontrivial
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap Ω (AdjoinRoot P)).injective p
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, f, π', hu.unit, hinj, ?_, ?_, hgr, ?_⟩
  · ext x; exact hg x
  · set I : Ideal (AdjoinRoot P) := (RingHom.ker π).map f with hI
    have hIn : IsNilpotent I := by
      obtain ⟨n, hn⟩ := hπ
      refine ⟨n, ?_⟩
      rw [hI, ← Ideal.map_pow, hn]
      exact Ideal.map_bot
    set J : Ideal (AdjoinRoot P) := Ideal.span {AdjoinRoot.root P - 1} with hJ
    have hJn : IsNilpotent J := by
      obtain ⟨n, hn⟩ := hIn
      refine ⟨p * n, ?_⟩
      rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
      apply Ideal.pow_right_mono
      rw [hJ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, sub_pow_char, hroot,
        one_pow, ← map_one f, ← map_sub]
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
    obtain ⟨n, hn⟩ := (Commute.all I J).isNilpotent_add hIn hJn
    refine ⟨n, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    apply Ideal.pow_right_mono
    intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨r, hr⟩ : (X - C 1 : A[X]) ∣ q - C (q.eval 1) := X_sub_C_dvd_sub_C_eval
    have h1 : AdjoinRoot.mk P q = f (q.eval 1) + (AdjoinRoot.root P - 1) * AdjoinRoot.mk P r := by
      have := congrArg (AdjoinRoot.mk P) hr
      simp only [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one] at this
      rw [hf, ← this]; ring
    have hx' : g (AdjoinRoot.mk P q) = 0 := hx
    rw [h1, map_add (f := _), map_mul, map_sub, hgr, map_one, sub_self, zero_mul, add_zero, hg] at hx'
    rw [h1, Ideal.add_eq_sup]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · ext
    simpa using hroot

theorem exists_root_fin (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (_ : IsNilpotent (RingHom.ker π))
    (a : Fin n → Aˣ) (_ : ∀ i, π (a i).val = 1),
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : Fin n → A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      (∀ i, π' (s i).val = 1) ∧ ∀ i, s i ^ p = Units.map (f : A →* A') (a i) := by
  induction n with
  | zero =>
    intro A _ _ π hπ a _
    exact ⟨A, inferInstance, inferInstance, AlgHom.id Ω A, π, a, Function.injective_id, rfl, hπ,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro A _ _ π hπ a ha
    obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
      ih A π hπ (fun i => a i.succ) (fun i => ha i.succ)
    have h0 : ρ (Units.map (f : A →* B) (a 0)).val = 1 := by
      have := congrArg (fun φ : A →ₐ[Ω] Ω => φ (a 0).val) hρ
      simpa [ha 0] using this
    obtain ⟨C, _, _, g, σ, t, hg, hσ, hσn, ht1, ht⟩ :=
      exists_root_one Ω p B ρ hρn _ h0
    refine ⟨C, inferInstance, inferInstance, g.comp f, σ,
      Fin.cons t (fun i => Units.map (g : B →* C) (s i)), hg.comp hf, ?_, hσn, ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hσ, hρ]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ht1
      · have := congrArg (fun φ : B →ₐ[Ω] Ω => φ (s j).val) hσ
        simpa [hs1 j] using this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, ht]; rfl
      · rw [Fin.cons_succ, ← map_pow, hs j]; rfl

theorem exists_root_character :
    ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ,
    (∀ x, π (χ x).val = 1) →
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧
      χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  intro Ω _ p _ _ X _ _ _ A _ _ π hπ χ hχ
  let b := Module.finBasis ℤ X
  obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
    exists_root_fin Ω p _ A π hπ (fun i => χ (Multiplicative.ofAdd (b i))) (fun i => hχ _)
  let l : X →ₗ[ℤ] Additive Bˣ := b.constr ℤ (fun i => Additive.ofMul (s i))
  have hl : ∀ i, l (b i) = Additive.ofMul (s i) := fun i => b.constr_basis ℤ _ i
  let χ' : Multiplicative X →* Bˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  have hχ' : ∀ i, χ' (Multiplicative.ofAdd (b i)) = s i := fun i => by
    change Additive.toMul (l (b i)) = _
    rw [hl]; rfl
  have key : ∀ {G : Type} [CommGroup G] (φ ψ : Multiplicative X →* G),
      (∀ i, φ (Multiplicative.ofAdd (b i)) = ψ (Multiplicative.ofAdd (b i))) → φ = ψ := by
    intro G _ φ ψ h
    have : (MonoidHom.toAdditiveRight φ).toIntLinearMap =
        (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
      b.ext fun i => congrArg Additive.ofMul (h i)
    refine MonoidHom.ext fun x => ?_
    exact congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  refine ⟨B, inferInstance, inferInstance, f, ρ, χ', hf, hρ, hρn, ?_, ?_⟩
  · have : (Units.map (ρ : B →* Ω)).comp χ' = 1 := key _ _ fun i => by
      ext
      simpa [hχ'] using hs1 i
    intro x
    exact congrArg Units.val (DFunLike.congr_fun this x)
  · exact key _ _ fun i => by
      rw [MonoidHom.pow_apply, hχ', hs]; rfl

end GlobalTheory.TorusRoot
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pth_root_torus_point_nilpotent_augmented_ext : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ, (∀ x, π (χ x).val = 1) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω) (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧ χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  first | exact @GlobalTheory.TorusRoot.exists_root_character | exact GlobalTheory.TorusRoot.exists_root_character | (intros; apply GlobalTheory.TorusRoot.exists_root_character <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOne
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Alg

open Polynomial

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime]

theorem root_pow_eq_zero : AdjoinRoot.root ((X : Polynomial Ω) ^ p) ^ p = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

def truncLift {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    AdjoinRoot ((X : Polynomial Ω) ^ p) →ₐ[Ω] A :=
  Ideal.Quotient.liftₐ _ (aeval a) (by
    intro f hf
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.1 hf
    simp [ha])

theorem truncLift_mk {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) (f : Polynomial Ω) :
    truncLift a ha (AdjoinRoot.mk _ f) = aeval a f := rfl

theorem truncLift_root {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    truncLift (Ω := Ω) a ha (AdjoinRoot.root _) = a := by
  rw [← AdjoinRoot.mk_X, truncLift_mk, aeval_X]

theorem isLocalRing_trunc : IsLocalRing (AdjoinRoot ((X : Polynomial Ω) ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Nontrivial (AdjoinRoot ((X : Polynomial Ω) ^ p)) :=
    (truncLift (0 : Ω) (zero_pow hp)).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  have hn : IsNilpotent (AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (X * f.divX)) := by
    refine ⟨p, ?_⟩
    rw [map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_eq_zero, zero_mul]
  rw [← X_mul_divX_add f, map_add (f := _)]
  by_cases hc : f.coeff 0 = 0
  · right
    rw [hc, C_0, map_zero, add_zero]
    exact hn.isUnit_one_sub
  · left
    exact hn.isUnit_add_right_of_commute ((isUnit_C.2 (Ne.isUnit hc)).map _) (Commute.all _ _)

theorem mk_eq_const_of_derivative [CharP Ω p] (f : Polynomial Ω)
    (h : AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (derivative f) = 0) :
    AdjoinRoot.mk ((X : Polynomial Ω) ^ p) f = algebraMap Ω _ (aeval (0 : Ω) f) := by
  rw [AdjoinRoot.mk_eq_zero, X_pow_dvd_iff] at h
  change _ = AdjoinRoot.mk _ (C _)
  rw [AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro d hd
  rcases d with _ | d
  · simp [coeff_zero_eq_eval_zero]
  · have h1 := h d (by omega)
    rw [coeff_derivative] at h1
    have h2 : ((d : Ω) + 1) ≠ 0 := by
      intro h0
      have : ((d + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h0
      exact absurd (Nat.le_of_dvd (Nat.succ_pos d) ((CharP.cast_eq_zero_iff Ω p _).1 this)) (by omega)
    simpa [coeff_C] using (mul_eq_zero.1 h1).resolve_right h2

end Alg

theorem spMap_comp_eq_of_equalizer {R B : Type} [CommRing R] [CommRing B] [IsLocalRing R] {Y : Scheme.{0}}
    (y : Sp R ⟶ Y) (d₁ d₀ : R →+* B) (e : R →+* R) (he : ∀ x, d₁ x = d₀ x → e x = x)
    (h : spMap d₁ ≫ y = spMap d₀ ≫ y) : spMap e ≫ y = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Y, V) ⟶ CommRingCat.of R, Spec.map φ ≫ hV.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact he _ (congrArg (fun k => k.hom a) h')

theorem IsAlpha.eq_one_of_tangent (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0})
    (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) (hg : IsAlpha p s G g)
    (h1 : g (DualNumber Ω) DualNumber.eps = 1) (A : Type) [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    g A a = 1 := by
  have hp : p.Prime := Fact.out
  let R := AdjoinRoot ((Polynomial.X : Polynomial Ω) ^ p)
  haveI : IsLocalRing R := isLocalRing_trunc
  let t : R := AdjoinRoot.root _
  have ht : t ^ p = 0 := root_pow_eq_zero
  have heps : ∀ (B : Type) [CommRing B], (DualNumber.eps : DualNumber B) ^ p = 0 := fun B _ =>
    pow_eq_zero_of_le hp.two_le (by rw [sq, DualNumber.eps_mul_eps])
  haveI : CharP R p := charP_of_injective_algebraMap (algebraMap Ω R).injective p
  haveI : CharP (DualNumber R) p := charP_of_injective_algebraMap (algebraMap Ω (DualNumber R)).injective p
  let t' : DualNumber R := TrivSqZeroExt.inl t
  have ht' : t' ^ p = 0 := by
    change TrivSqZeroExt.inlAlgHom Ω R R t ^ p = 0
    rw [← map_pow, ht, map_zero]
  have hs : (t' + DualNumber.eps) ^ p = 0 := by rw [add_pow_char, ht', heps, add_zero]
  have he : g (DualNumber R) DualNumber.eps = 1 := by
    let j : DualNumber Ω →ₐ[Ω] DualNumber R :=
      DualNumber.lift ⟨(Algebra.ofId _ _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
    have hj : j DualNumber.eps = DualNumber.eps := DualNumber.lift_apply_eps _
    rw [← hj, hg.1 _ _ j _ (heps Ω), h1, MonObj.comp_one]
  have key : homAt s (truncLift _ hs) ≫ g R t = homAt s (truncLift _ ht') ≫ g R t := by
    rw [← hg.1 _ _ _ _ ht, ← hg.1 _ _ _ _ ht, truncLift_root, truncLift_root, hg.2 _ _ _ ht' (heps R), he, _root_.mul_one]
  let e : R →ₐ[Ω] R := truncLift 0 (zero_pow hp.ne_zero)
  have hr : homAt s e ≫ g R t = g R t := by
    apply Over.OverMorphism.ext
    refine spMap_comp_eq_of_equalizer (g R t).left (truncLift _ hs).toRingHom (truncLift _ ht').toRingHom
      e.toRingHom ?_ (congrArg (·.left) key)
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    change Polynomial.aeval (t' + DualNumber.eps) f = Polynomial.aeval t' f at hx
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, DualNumber.eps_mul_eps]), add_eq_left] at hx
    have h3 : Polynomial.aeval t' (Polynomial.derivative f) =
        TrivSqZeroExt.inl (Polynomial.aeval t (Polynomial.derivative f)) :=
      Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom Ω R R) t _
    have h4 := congrArg TrivSqZeroExt.snd hx
    rw [h3] at h4
    have h5 : Polynomial.aeval t (Polynomial.derivative f) = 0 := by simpa using h4
    rw [AdjoinRoot.aeval_eq] at h5
    rw [mk_eq_const_of_derivative f h5]
    exact e.commutes _
  have h0 : g R t = 1 := by
    rw [← hr, ← hg.1 _ _ _ _ ht, truncLift_root, hg.zero hp.ne_zero]
  have := hg.1 _ _ (truncLift a ha) t ht
  rwa [truncLift_root, h0, MonObj.comp_one] at this

end GlobalTheory.AlphaPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_tangent_vector_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G), IsAlpha p s G g → g (DualNumber Ω) DualNumber.eps = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → g A a = 1 := by
  first | exact @GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | exact GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | (intros; apply GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdeal
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorExtPoints

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem exists_lift {X Y : Scheme.{0}} (q : X ⟶ Y) [Smooth q] {A : Type} [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω) (hn : IsNilpotent (RingHom.ker π)) (y : Sp A ⟶ Y) (x₀ : Sp Ω ⟶ X)
    (h : x₀ ≫ q = spMap (π : A →+* Ω) ≫ y) : ∃ x : Sp A ⟶ X, spMap (π : A →+* Ω) ≫ x = x₀ ∧ x ≫ q = y := by
  have hπ : Function.Surjective π := fun a => ⟨algebraMap Ω A a, π.commutes a⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair q (x₀ (closedPoint Ω)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen q hU hV hVU (CommRingCat.ofHom (π : A →+* Ω)) y x₀ h ?_
    (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · rintro _ ⟨p, rfl⟩
    obtain ⟨z, hz⟩ : p ∈ Set.range (PrimeSpectrum.comap (π : A →+* Ω)) := by
      refine (range_comap_of_surjective _ (π : A →+* Ω) hπ).ge ?_
      obtain ⟨n, hn⟩ := hn
      exact (Ideal.IsPrime.pow_le_iff (P := p.asIdeal) (hP := p.isPrime) n.succ_ne_zero).1 (by
        rw [pow_succ]
        exact Ideal.mul_le_left.trans (hn.le.trans bot_le))
    obtain rfl : z = closedPoint Ω := Subsingleton.elim _ _
    have e : q (x₀ (closedPoint Ω)) = y (spMap (π : A →+* Ω) (closedPoint Ω)) := congr($h (closedPoint Ω))
    rw [← hz]
    exact e ▸ hVU hxV
  · intro R C _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

def torPt (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra Ω A] :
    (overAt s A ⟶ splitTorus S X) ≃* (Multiplicative X →* Aˣ) :=
  (splitTorusPointsEquiv S X (overAt s A)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv).monoidHomCongrRight

theorem torPt_nat (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] {A A' : Type} [CommRing A] [Algebra Ω A]
    [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (t : overAt s A ⟶ splitTorus S X) :
    torPt s X A' (homAt s f ≫ t) = (Units.map (f : A →* A')).comp (torPt s X A t) := by
  ext x
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
      (splitTorusPointsEquiv S X _ (homAt s f ≫ t) (Multiplicative.ofAdd x)).val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd x)).val)
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))) _)

theorem isTorExt_of_kernel (s : Sp Ω ⟶ S) {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Smooth q.left]
    (hk : IsPullback i (toUnit _) q η[B]) :
    IsTorExt s s G B X (fun A _ _ => IsMonHom.monoidHom q (overAt s A))
      (fun A _ _ => (IsMonHom.monoidHom i (overAt s A)).comp (torPt s X A).symm.toMonoidHom) := by
  refine ⟨fun A A' _ _ _ _ f x => Category.assoc _ x q, fun A A' _ _ _ _ f χ => ?_, fun A _ _ χ χ' h => ?_,
    fun A _ _ x => ⟨fun h => ?_, ?_⟩, fun A _ _ π hn y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (torPt s X A).surjective χ
    rw [← torPt_nat]
    change (torPt s X A').symm _ ≫ i = _ ≫ (torPt s X A).symm _ ≫ i
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc]
  · exact (torPt s X A).symm.injective (hk.hom_ext h (toUnit_unique _ _))
  · refine ⟨torPt s X A (hk.lift x (toUnit _) h), ?_⟩
    change (torPt s X A).symm _ ≫ i = _
    rw [MulEquiv.symm_apply_apply]
    exact hk.lift_fst _ _ _
  · rintro ⟨χ, rfl⟩
    change (_ ≫ i) ≫ q = toUnit _ ≫ η[B]
    rw [Category.assoc, hk.w, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit _)]
  · have h1 : (1 : overAt s Ω ⟶ G) ≫ q = homAt s π ≫ y := (map_one (IsMonHom.monoidHom q _)).trans hy.symm
    obtain ⟨x, hx, hq⟩ := exists_lift q.left π hn y.left (1 : overAt s Ω ⟶ G).left (congrArg (·.left) h1)
    exact ⟨Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w y), Over.OverMorphism.ext hx,
      Over.OverMorphism.ext hq⟩

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') {t : T.left ⟶ S} (ht : t = T.hom ≫ f) :
    ∃ E : (T ⟶ G') ≃* (Over.mk t ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  subst ht
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_isTorExt_of_pullback {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj G'] [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φ)
    (hB : IsGrpPullback B' B f ψ) {s' : Sp Ω ⟶ S'} {s : Sp Ω ⟶ S} (hs : s' ≫ f = s) {X : Type} [AddCommGroup X]
    {τ' : PtHom s' s' G' B'} {io' : TorHom s' G' X} (h : IsTorExt s' s' G' B' X τ' io') :
    ∃ (τ : PtHom s s G B) (io : TorHom s G X), IsTorExt s s G B X τ io ∧
      ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), ∃ x' : overAt s' A ⟶ G',
        x'.left ≫ φ = x.left ∧ (τ A x).left = (τ' A x').left ≫ ψ := by
  have ht : ∀ (A : Type) [CommRing A] [Algebra Ω A], spMap (algebraMap Ω A) ≫ s = (overAt s' A).hom ≫ f :=
    fun A _ _ => by rw [← hs]; exact (Category.assoc _ _ _).symm
  choose E hE using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hG (overAt s' A) (ht A)
  choose F hF using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hB (overAt s' A) (ht A)
  have nE : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ G'), E A' (homAt s' g ≫ x) = homAt s g ≫ E A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hE A' _).trans ((Category.assoc _ x.left φ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hE A x).symm)))
  have nF : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ B'), F A' (homAt s' g ≫ x) = homAt s g ≫ F A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hF A' _).trans ((Category.assoc _ x.left ψ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hF A x).symm)))
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun A _ _ => ((F A).toMonoidHom.comp (τ' A)).comp (E A).symm.toMonoidHom,
    fun A _ _ => (E A).toMonoidHom.comp (io' A),
    ⟨fun A A' _ _ _ _ g x => ?_, fun A A' _ _ _ _ g χ => ?_, fun A _ _ => (E A).injective.comp (h₃ A),
      fun A _ _ x => ?_, fun A _ _ π hn y hy => ?_⟩, fun A _ _ x => ?_⟩
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A' (τ' A' ((E A').symm _)) = _ ≫ F A (τ' A ((E A).symm _))
    rw [← nE, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h₁, nF]
  · change E A' (io' A' _) = _ ≫ E A (io' A χ)
    rw [h₂, nE]
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A (τ' A ((E A).symm _)) = 1 ↔ ∃ χ, E A (io' A χ) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, h₄]
    exact exists_congr fun χ => (E A).injective.eq_iff.symm
  · obtain ⟨y, rfl⟩ := (F A).surjective y
    rw [← nF, MulEquiv.map_eq_one_iff] at hy
    obtain ⟨x, hx, rfl⟩ := h₅ A π hn y hy
    refine ⟨E A x, by rw [← nE, hx, map_one], ?_⟩
    change F A (τ' A ((E A).symm _)) = _
    rw [MulEquiv.symm_apply_apply]
  · refine ⟨(E A).symm x, (hE A _).symm.trans ?_, hF A _⟩
    rw [MulEquiv.apply_symm_apply]

theorem exists_isTorExt : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  intro W _ _ I D G _ _ g Ω _ β hβ
  let β₀ : W ⧸ I ^ (0 + 1) →+* Ω := Ideal.Quotient.lift _ β (by simpa using hβ)
  have e : spMap β₀ ≫ Out.thick W I 0 = spMap β := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (W ⧸ I ^ (0 + 1))) D.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨τ, io, h, hτ⟩ := exists_isTorExt_of_pullback (isGrpPullback_pullback G (Out.thick W I 0))
    (isGrpPullback_pullback D.P.A (Out.thick W I 0)) e (isTorExt_of_kernel (spMap β₀) g.i g.q g.isKernel)
  refine ⟨τ, io, h, fun A _ _ x x₀ hx => ?_⟩
  obtain ⟨x', h₁, h₂⟩ := hτ A x
  have : IsClosedImmersion (Out.thick W I 0) := .spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain rfl : x₀ = x'.left := (cancel_mono (pullback.fst G.hom (Out.thick W I 0))).1 (hx.trans h₁.symm)
  exact h₂.trans (Category.assoc _ _ _)

end GlobalTheory.TorExtPoints
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  first | exact @GlobalTheory.TorExtPoints.exists_isTorExt | exact GlobalTheory.TorExtPoints.exists_isTorExt | (intros; apply GlobalTheory.TorExtPoints.exists_isTorExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding preHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Steps

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] [CharP Ω p] {S S' : Scheme.{0}} {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'}
  {G : Over S} [GrpObj G] {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}

theorem pow_p_of_sq {A : Type} [CommRing A] {e : A} (he : e ^ 2 = 0) : e ^ p = 0 :=
  pow_eq_zero_of_le (Fact.out : p.Prime).two_le he

theorem eps_pow : (DualNumber.eps : DualNumber Ω) ^ p = 0 :=
  pow_p_of_sq (by rw [pow_two, DualNumber.eps_mul_eps])

theorem eq_one_of_torus (h : IsTorExt s s' G B X τ io) {g : Fam s G} (hg : IsAlpha p s G g)
    (h1 : τ _ (g (DualNumber Ω) DualNumber.eps) = 1) : g (DualNumber Ω) DualNumber.eps = 1 := by
  classical
  have h2 := GlobalTheory.T.eq_one_of_tangent_vector_eq_one Ω p S' s' B _ (hg.map h) h1
  have h3 : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ χ, a ^ p = 0 → io A χ = g A a := fun A _ _ a => by
    by_cases ha : a ^ p = 0
    · obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A _).1 (h2 A a ha)
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun k => absurd k ha⟩
  choose χ hχ using h3
  have h4 : χ (DualNumber Ω) DualNumber.eps = 1 := MonoidHom.ext fun x =>
    GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one Ω p (fun A _ _ a => χ A a x) (fun A A' _ _ _ _ f a ha => by
      have ha' : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
      have : χ A' (f a) = (Units.map (f : A →* A')).comp (χ A a) :=
        h.2.2.1 A' (by rw [hχ A' _ ha', h.2.1, hχ A a ha, hg.1 A A' f a ha])
      exact DFunLike.congr_fun this x) (fun A _ _ a a' ha ha' => by
      have hs : (a + a') ^ p = 0 := by
        rcases subsingleton_or_nontrivial A with _ | _
        · exact Subsingleton.elim _ _
        · have := charP_of_injective_algebraMap (algebraMap Ω A).injective p
          rw [add_pow_char, ha, ha', add_zero]
      have : χ A (a + a') = χ A a * χ A a' :=
        h.2.2.1 A (by rw [map_mul, hχ A _ hs, hχ A a ha, hχ A a' ha', hg.2 A a a' ha ha'])
      exact DFunLike.congr_fun this x) _ _ eps_pow
  rw [← hχ _ _ eps_pow, h4, map_one]

variable [IsCommMonObj G] [IsCommMonObj B] {L : RigLB G} {c : CubicalStr G L} {M : RigLB B} {c' : CubicalStr B M}

theorem Orth.map [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    {g : Fam s G} (hg : IsAlpha p s G g) (ho : Orth p s G c g) : Orth p s' B c' (fun A _ _ a => τ A (g A a)) := by
  intro A _ _ π hπ e he y hy hyp
  have hp := (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx, rfl⟩ := h.2.2.2.2 A π hπ y hy
  obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A (x ^ p)).1 (by rw [map_pow, hyp])
  have h1 : (Units.map (π : A →* Ω)).comp χ = 1 :=
    h.2.2.1 Ω (by rw [h.2.1, hχ, MonObj.comp_pow, hx, one_pow, map_one])
  obtain ⟨A', _, _, f, π', χ', hf, hc, hn, h2, h3⟩ := GlobalTheory.T.exists_pth_root_torus_point_nilpotent_augmented_ext Ω p X A π hπ χ fun a =>
    congrArg Units.val (DFunLike.congr_fun h1 a)
  have h4 : (Units.map (π' : A' →* Ω)).comp χ' = 1 := MonoidHom.ext fun a => Units.ext (h2 a)
  have k := ht A' _ _ (ho A' π' hn (f e) (by rw [← map_pow, he, map_zero]) ((homAt s f ≫ x) * (io A' χ')⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← h.2.1, h4, map_one, inv_one, _root_.mul_one, ← Category.assoc, hom_comp,
      hc, hx])
    (by rw [mul_pow, inv_pow, ← map_pow, h3, h.2.1, hχ, MonObj.comp_pow, mul_inv_cancel]))
  rw [hg.1 A A' f e (pow_p_of_sq he), map_mul, map_inv, (h.2.2.2.1 A' _).2 ⟨χ', rfl⟩, inv_one, _root_.mul_one,
    h.1, h.1] at k
  exact cubWeil_of_injective f hf ((hg.map h).pow_eq_one hp (pow_p_of_sq he)) hyp k

theorem NonDeg.of_torExt [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    (hB : NonDeg p s' B c') : NonDeg p s G c := fun _ hg ho =>
  eq_one_of_torus h hg (hB _ (hg.map h) (ho.map h ht hg))

theorem NonDeg.of_perf [IsAlgClosed Ω] (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hP : Perf p G c) :
    NonDeg p s G c := by
  intro g hg ho
  have hp := (Fact.out : p.Prime).ne_zero
  have : Module.Finite Ω (DualNumber Ω) := inferInstanceAs (Module.Finite Ω (Ω × Ω))
  refine hP _ _ (hg.pow_eq_one hp eps_pow) (GlobalTheory.T.cubicalWeil_trivial_of_localArtinian_points Ω S s G L c p hf (DualNumber Ω) _ (hg.pow_eq_one hp eps_pow)
    fun A _ _ π hπ f y hy => ?_)
  have he : f DualNumber.eps ^ 2 = 0 := by rw [← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero]
  have hx : (homAt s π ≫ y) ^ p = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have k₁ := GlobalTheory.T.alphaP_homomorphism_cubicalWeil_trivial_rational_torsion Ω p S s G L c g hg _ hx A _ (pow_p_of_sq he)
  have k₂ := ho A π hπ _ he (y * (homAt s (Algebra.ofId Ω A) ≫ homAt s π ≫ y)⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc (homAt s π), hom_comp,
      Subsingleton.elim (π.comp (Algebra.ofId Ω A)) (AlgHom.id Ω Ω), hom_id, Category.id_comp, mul_inv_cancel])
    (by rw [mul_pow, inv_pow, hy, k₁.2.1, inv_one, _root_.mul_one])
  have k := cubWeil_mul_right k₂ k₁
  rwa [inv_mul_cancel_right, hg.1 _ A f _ eps_pow] at k

end Steps

theorem perf_of_polAV {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (P : Out.PolAV (Sp O))
    [IsCommMonObj P.A] [IsNoetherianRing O] (L : RigLB P.A) (hL : L.L = P.L) (c : CubicalStr P.A L) {n : ℕ} (hn : 1 ≤ n) :
    IsFinite ((𝟙 P.A) ^ n : P.A ⟶ P.A).left ∧ Perf n P.A c := by
  have hl := GlobalTheory.firstFiveLaws.1
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) := by
    rw [IsScalarTower.algebraMap_eq O (FractionRing O) K]
    exact (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  have : CharZero K := charZero_of_injective_algebraMap hi
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme hl O P.A P.isAb P.L P.isLB P.ample n hn
  refine ⟨f₁, GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic O K hi P.A P.g P.smoothDim L c n hn f₁ f₂
    ((hl.mulN _ P n hn).2.2.2.2 K _ hnK) fun y hy hp => ?_⟩
  have ht := CubNondeg.main hl _ P.A P.isAb L c K _ n hnK f₁ f₂ f₃ y hy hp
  rw [hL] at ht
  obtain ⟨u, hu⟩ := ht
  exact P.ktriv K _ y fun _ => ⟨⊤, trivial, _, LB.isGen_genPull _ u hu _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonDeg_of_polAt {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V))
    (ht : GlobalTheory.LN.PolAt t (Out.jK V)) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
    (β : V →+* Ω) (hβ : ∀ a ∈ maximalIdeal V, β a = 0) : NonDeg p (spMap β) t.G t.cub := by
  obtain ⟨W, _, _, _, f, β', t', m, hW, hf, hβ', ht', hs⟩ := GlobalTheory.T.exists_finite_extension_split_special_fibre_point E H V hV t ht Ω β hβ
  obtain ⟨τ, io, h₁, h₂⟩ := GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint E H _ _ _ t t' m Ω (spMap β) (spMap β') (by
    rw [← hf]; exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom β')).symm) p
  refine NonDeg.of_torExt h₁ h₂ ?_
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t' ht' hs
  obtain ⟨τ', io', k₁, k₂⟩ := GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal W _ P.D.toPre t'.G (P.U.gt 0) Ω β' hβ'
  have k₃ := GlobalTheory.T.abelianPart_projection_respects_orthogonality W _ P.D P.A t'.G P.U.toUnifPre Ω β' hβ' τ' k₂ p
  have := hW.1
  have := hW.2.2
  obtain ⟨f₁, f₂⟩ := perf_of_polAV P.D.toPre.P ⟨_, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ rfl
    P.D.toPre.cub (Fact.out : p.Prime).one_le
  have k₄ := NonDeg.of_torExt k₁ k₃ (NonDeg.of_perf f₁ f₂)
  have key : ∀ (L : RigLB t'.G) (_ : L = t'.PP) (c : CubicalStr t'.G L), NonDeg p (spMap β') t'.G c →
      NonDeg p (spMap β') t'.G t'.cub := by
    rintro L rfl c hc
    rwa [PtGermCompare.cubical_unique (PtGermCompare.surjective_cube P.U.toUnifPre) t'.cub c]
  exact key _ P.bundle _ k₄

theorem ev_map_eq_one {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') {d : ℕ} (f : PS R 3 d)
    (a : Fin 3 → Germ.Pt R 2 d) (a' : Fin 3 → Germ.Pt R' 2 d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (h' : ∀ j i, a' j i = MvPowerSeries.map β (a j i)) (h : ev a f = 1) : ev a' (MvPowerSeries.map β f) = 1 := by
  have := MvPowerSeries.map_subst (a := fun q : Fin 3 × Fin d => a q.1 q.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2) (h := β) f
  rw [show MvPowerSeries.subst (fun q : Fin 3 × Fin d => a q.1 q.2) f = 1 from h, map_one] at this
  unfold ev
  simp only [h']
  exact this.symm

theorem ndg_at_chart : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) [StarRing (NumberField.RingOfIntegers E)], NondegenerateCharts Xo c := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C3 C _ _ V ι' hι k Y hY
  obtain rfl := PowGerm.starSt E H inst hstar
  letI := H.starRing
  letI := io.toAlgebra
  by_contra hN
  obtain ⟨Ω, _, _, _, ρ, hρ⟩ := GlobalTheory.T.exists_algClosed_residueField_valuedField C V Y.algClosed
  obtain ⟨j, hj, hjm⟩ := GlobalTheory.T.exists_ringHom_valuationRing_of_embOK T C V ι' hι
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  obtain ⟨BT, hF, -, h1, h2, -⟩ := integralChart_formalBiext E H Dw l Xo c T io y C3
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (C3.FT i) = 0 := fun i => hF ▸ BT.G.const i
  have e : V.RR.subtype.comp j = ι'.comp (algebraMap T.V T.Fr) := RingHom.ext hj
  have hD := GlobalTheory.T.degenerate_direction_of_not_nondegenerate C V _ _ Y T.V j C3.FT C3.ph2T hF0
    (fun i => by rw [hY.F, e, MvPowerSeries.map_comp]; exact congrArg _ (C3.gen.1.1 i))
    (by rw [hY.ph2, e, MvPowerSeries.map_comp]; exact congrArg _ C3.gen.1.2.2.2.1) Ω ρ hρ hN
  obtain ⟨P, hP, hL⟩ := GlobalTheory.T.exists_formalChart_point_nilpotent_coordinates E H T.V C3.I.G _ _ _ _ _ _ C3.chartT hF0 Ω (ρ.comp j)
  refine GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction Ω V.l _ _ C3.I.G.G _ C3.I.G.cub _ _ (MvPowerSeries.map (ρ.comp j) C3.ph1T) _ P
    (fun i => by rw [MvPowerSeries.constantCoeff_map, hF0, map_zero]) ?_ ?_ ?_ hL
    (GlobalTheory.T.universalChart_points_over_field_point E H T.V C3.I.G _ _ (PowGerm.univSt_holds E H Dw l Xo c T io y C3) Ω _ P hP)
    (GlobalTheory.T.frame_partial_laws_nilpotent_coordinates E H T.V C3.I.G _ _ _ _ _ _ _ _ _ C3.frameT hF0 Ω _ P hP) hD
    (nonDeg_of_polAt ⟨T.dvr, T.cpl, T.ch0⟩ C3.I.G (GlobalTheory.T.integralFramedPoint_model_polarised_generic_fibre E H Dw l Xo c T io y.1 C3.I) V.l _
      fun a ha => (hρ _).2 (hjm a ha))
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_snd) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h2 ▸ BT.cocycleRight_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]

end GlobalTheory.AlphaPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) [StarRing (NumberField.RingOfIntegers E)], NondegenerateCharts Xo c := by
  first | exact @GlobalTheory.AlphaPair.ndg_at_chart | exact GlobalTheory.AlphaPair.ndg_at_chart | (intros; apply GlobalTheory.AlphaPair.ndg_at_chart <;> assumption)
end
