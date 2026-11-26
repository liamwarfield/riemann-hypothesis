module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.CompleteDVRExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtDown
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing in
private theorem fpd_prec_finite {O M : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M :=
  _root_.UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite I

private theorem fpd_prec_cofinal {R : Type} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem fpd_complete {R R' : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    fpd_prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (fpd_prec_finite _))
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

open IsLocalRing in
private theorem fpd_ext {A k k₁ : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] [Field k] [Field k₁] [Finite k₁]
    (f : k →+* k₁) (j : k →+* A) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (φ : A →+* B) (j₁ : k₁ →+* B),
      IsAdicComplete (maximalIdeal B) B ∧ Finite (ResidueField B) ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∀ a, j₁ (f a) = φ (j a) := by
  classical
  let K := FractionRing A
  let Kb := AlgebraicClosure K
  letI : Algebra k k₁ := f.toAlgebra
  letI : Algebra k Kb := ((algebraMap A Kb).comp j).toAlgebra
  haveI : Module.Finite k k₁ := Module.Finite.of_finite
  haveI : Module.IsTorsionFree k k₁ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree k Kb := DivisionSemiring.to_moduleIsTorsionFree
  let g : k₁ →ₐ[k] Kb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hint : ∀ x : k₁, IsIntegral A (g x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simpa using isIntegral_zero
    · have h1 : IsOfFinOrder (Units.mk0 x hx) := isOfFinOrder_of_finite _
      obtain ⟨m, hm, h2⟩ := isOfFinOrder_iff_pow_eq_one.1 h1
      have h3 : x ^ m = 1 := by simpa using congrArg Units.val h2
      refine IsIntegral.of_pow hm ?_
      rw [← map_pow, h3, map_one]
      exact isIntegral_one
  let L := IntermediateField.adjoin K (Set.range g)
  haveI : Finite (Set.range g) := (Set.finite_range g).to_subtype
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨x, rfl⟩
      exact (hint x).tower_top)
  obtain ⟨hfin, hdvr⟩ := UpperTheory.V.Pr.T.completeDVRExt (A := A) (K := K) (L := L)
  let gL : k₁ →+* L := (g : k₁ →+* Kb).codRestrict L fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  have hmem : ∀ x, gL x ∈ integralClosure A L := fun x =>
    (isIntegral_algHom_iff (L.val.restrictScalars A) Subtype.val_injective).1 (hint x)
  have hinj : Function.Injective (algebraMap A (integralClosure A L)) := by
    intro x y h
    have h' : algebraMap A L x = algebraMap A L y := congrArg Subtype.val h
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L y] at h'
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  have hf : (algebraMap A (integralClosure A L)).Finite := RingHom.finite_algebraMap.2 hfin
  haveI hl : IsLocalHom (algebraMap A (integralClosure A L)) := hf.to_isIntegral.isLocalHom hinj
  refine ⟨integralClosure A L, inferInstance, inferInstance, hdvr, algebraMap _ _,
    gL.codRestrict (integralClosure A L) hmem, fpd_complete (R := A), Module.finite_of_finite (ResidueField A),
    hinj, hl, fun a => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact g.commutes a

open IsLocalRing UpperTheory.V.Alg in
private theorem fpd_cont {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] {x : Γ → A} (h : AdicCont (maximalIdeal A) x) :
    AdicCont (maximalIdeal B) fun g => φ (x g) := by
  intro N
  have hle : maximalIdeal A ^ N ≤ (maximalIdeal B ^ N).comap φ := by
    refine le_trans ?_ (Ideal.le_comap_pow φ N)
    exact Ideal.pow_right_mono (fun a ha => map_nonunit φ a ha) N
  exact (h N).comp (Ideal.quotientMap _ φ hle)

open IsLocalRing UpperTheory.V.Fr in
theorem UpperTheory.V.Pr.finPtDown :
    UpperTheory.V.Pr.FinPtDown := by
  intro l _ c c₁ f _ _ Φ n H A _ _ hA _ _ ρ hρ hψ g
  haveI : IsDiscreteValuationRing A := hA.toIsDiscreteValuationRing
  haveI := UpperTheory.V.UnitaryThreeInertia.Coef.finite_residue c₁
  obtain ⟨B, _, _, hB, φ, j₁, hc, hfin, hinj, hloc, hj⟩ :=
    fpd_ext (A := A) f (algebraMap (ResidueField c.O) A)
  letI : Algebra (ResidueField c₁.O) B := j₁.toAlgebra
  letI : Algebra c₁.O B := (j₁.comp (residue c₁.O)).toAlgebra
  haveI : IsScalarTower c₁.O (ResidueField c₁.O) B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hl : IsLocalHom (algebraMap c₁.O B) := RingHom.isLocalHom_comp j₁ (residue c₁.O)
  haveI : IsCD c₁.O B := { toIsDiscreteValuationRing := hB, complete := hc, isLocalHom := hl, fin := hfin }
  let ρ₀ := ρ.map φ
  let ρ₁ : NRep (Φ.ext f) n B := ⟨ρ₀.r, ρ₀.ψ, ρ₀.pol, ρ₀.diag, ρ₀.ord⟩
  have key : ∀ a, ResidueField.map φ (ResidueField.map (algebraMap c.O A) a) =
      ResidueField.map (algebraMap c₁.O B) (f a) := by
    intro a
    obtain ⟨b, hb⟩ := residue_surjective (f a)
    obtain ⟨a, rfl⟩ := residue_surjective a
    rw [← hb, ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue,
      IsScalarTower.algebraMap_apply c.O (ResidueField c.O) A, ← hj]
    exact congrArg (fun t => residue B (j₁ t)) hb.symm
  have hz : ∀ (s : Φ.Γ) (m : ℤ), (((Φ.ext f).Ψ s ^ m : (ResidueField c₁.O)ˣ) : ResidueField c₁.O) =
      f ((Φ.Ψ s ^ m : (ResidueField c.O)ˣ) : ResidueField c.O) := by
    intro s m
    show ((Units.map f.toMonoidHom (Φ.Ψ s) ^ m : (ResidueField c₁.O)ˣ) : ResidueField c₁.O) = _
    rw [← map_zpow]
    rfl
  have h1 : IsLiftA c₁.O ρ₁ := by
    refine ⟨⟨fun i j => fpd_cont φ (hρ.cont.1 i j), fun v i => fpd_cont φ (hρ.cont.2 v i)⟩,
      ⟨fun s i => ?_, fun v i s => ?_⟩, fun s i j hij => ?_⟩
    · exact (congrArg (ResidueField.map φ) (hρ.bar.1 s i)).trans ((key _).trans (congrArg _ (hz _ _).symm))
    · exact (congrArg (ResidueField.map φ) (hρ.bar.2 v i s)).trans ((key _).trans (congrArg _ (hz _ _).symm))
    · exact (congrArg (ResidueField.map φ) (hρ.diag s i j hij)).trans (map_zero _)
  have h2 := H B ρ₁ h1 (fun v i s hs h => by
    have h' : Φ.Ψ (Φ.loc v s) = 1 := Units.ext (f.injective ((congrArg Units.val h).trans (map_one f).symm))
    show Units.map φ.toMonoidHom (ρ.ψ v i s) = 1
    rw [hψ v i s hs h', map_one]) g
  apply Polynomial.map_injective φ hinj
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  refine h2.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ← hj]
  exact congrArg (fun t => Polynomial.X - Polynomial.C (j₁ t)) (hz _ _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg

namespace UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}

structure Ad (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) where
  lM : l ∣ M
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ Ψ.ker
  c : galEmb ℚ (W.Lp L) Ω s.c = σ
  St : ∀ u, u ∈ s.St ↔ ((M : ℕ) : 𝓞 (W.Lp L)) ∈ u.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal
  e : W.Vl l L ≃ Φ.V
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (e v)
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  v0Ψ : ∀ g ∈ Dec (F := L) (s.A s.v0), Φ.Ψ (k.p0 g) = 1
  v0ω : ∃ g ∈ Dec (F := L) (s.A s.v0), PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1


variable (Ω L) in
def toUpl : G (W.Lp L) Ω →* upl Ω L :=
  (galEmb ℚ (W.Lp L) Ω).codRestrict _ fun g x hx => g.commutes ⟨x, hx⟩

theorem toUpl_surj : Function.Surjective (toUpl Ω L) := by
  rintro ⟨s, hs⟩
  refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) (fun x => hs x.1 x.2), ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  rfl

theorem toUpl_inj : Function.Injective (toUpl Ω L) := by
  intro g h hgh
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun u : upl Ω L => (u : G ℚ Ω) x) hgh
  exact this

theorem galEmb_resP (g : G L Ω) : galEmb ℚ (W.Lp L) Ω (W.resP L Ω g) = galEmb ℚ L Ω g := rfl

theorem GalLink.galois_link_projection_coe (k : GalLink η Ψ σ g₁ B M L Φ) (g : G L Ω) : (k.p0 g).1 = k.p (toUpl Ω L (W.resP L Ω g)) := rfl

theorem GalLink.mem_range_resP (k : GalLink η Ψ σ g₁ B M L Φ) (g : G (W.Lp L) Ω) :
    g ∈ (W.resP L Ω).range ↔ η (galEmb ℚ (W.Lp L) Ω g) = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [galEmb_resP]
    have hm : galEmb ℚ L Ω h ∈ galOf ℚ L Ω := fun x => h.commutes x
    rw [k.2] at hm
    exact hm.2
  · intro hη
    have hm : galEmb ℚ (W.Lp L) Ω g ∈ upl Ω L ⊓ η.ker := ⟨(toUpl Ω L g).2, hη⟩
    rw [← k.2] at hm
    refine ⟨AlgEquiv.ofRingEquiv (f := (galEmb ℚ (W.Lp L) Ω g).toRingEquiv) (fun x => hm x), ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

def GalLink.p0h (k : GalLink η Ψ σ g₁ B M L Φ) : G L Ω →* Φ.G0 where
  toFun := k.p0
  map_one' := Subtype.ext (by rw [k.galois_link_projection_coe, map_one, map_one, map_one]; rfl)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, k.galois_link_projection_coe, k.galois_link_projection_coe, k.galois_link_projection_coe, map_mul, map_mul, map_mul])

theorem GalLink.surjective_levelChangeBaseGroupHom (k : GalLink η Ψ σ g₁ B M L Φ) : Function.Surjective k.p0 := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs⟩ := k.p_surj y
  have hη : η s = 1 := by
    rw [← k.del s, hs]
    exact hy
  obtain ⟨g', hg'⟩ := toUpl_surj s
  have hη' : η (galEmb ℚ (W.Lp L) Ω g') = 1 := by
    rw [← hg'] at hη
    exact hη
  obtain ⟨g, rfl⟩ := (k.mem_range_resP g').2 hη'
  refine ⟨g, Subtype.ext ?_⟩
  rw [k.galois_link_projection_coe, hg', hs]

end

section

variable {k E Ω : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E]
  [IsScalarTower k E Ω]

theorem galEmb_mem_Dec (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Dec (F := k) A ↔ g ∈ Dec (F := E) A := Iff.rfl

theorem galEmb_mem_Ine (A : ValuationSubring Ω) (g : G E Ω) : galEmb k E Ω g ∈ Ine (F := k) A ↔ g ∈ Ine (F := E) A := Iff.rfl

theorem natCast_place {A : ValuationSubring Ω} {v : W.Plc E} (h : IsPlaceOver A v) (m : ℕ) :
    A.valuation (m : Ω) < 1 ↔ ((m : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  unfold IsPlaceOver at h
  rw [← h (m : 𝓞 E)]
  simp only [map_natCast]

end

theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨y, hy⟩
  have hs : Function.Surjective (toGS Ω V.S') := by
    unfold toGS
    exact QuotientGroup.mk'_surjective _
  obtain ⟨g', rfl⟩ := hs y
  obtain ⟨g, rfl⟩ := (V.6 g').1 hy
  exact ⟨g, rfl⟩

def CrE : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), B.valuation (l : Ω) < 1 →
    ∃ e : W.Vl l L ≃ Φ.V, ∀ v : W.Vl l L, IsPlaceOver (k.pl (e v)) v.1

def ExistsPrimeSplitInKernelWithNontrivialCyclotomic : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ), IsOpen (Φ.Ψ.ker : Set Φ.Γ) →
    ∀ g : G L Ω, Φ.Ψ (k.p0 g) = 1 → PadicInt.toZMod ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 → ∀ M' : ℕ, M' ≠ 0 →
    ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M' ∧ normV v = p ∧
      ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧
      (∀ t ∈ Dec (F := L) A, Φ.Ψ (k.p0 t) = 1) ∧
      ∃ t ∈ Dec (F := L) A, PadicInt.toZMod ((cycZ L Ω l t : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1

def CrLam : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (v : Φ.V) (A : ValuationSubring Ω),
    A = k.pl v → A.valuation (M : Ω) < 1 →
    ∃ lam : Dec (F := L) A ≃ₜ* Φ.Gv v, ∀ g : Dec (F := L) A, (k.j v (lam g)).1 = galEmb ℚ L Ω g

def CrPi : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∃ π : V.frame.G₀ →* Φ.G0, Continuous π ∧ (∀ g, π (V.pr g) = k.p0 g) ∧
      (∀ g, π (V.frame.conj g) = Φ.conj (π g)) ∧ ∀ g : V.frame.G₀, Φ.eps (π g) = V.frame.ε g

def CrKer : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ π : V.frame.G₀ →* Φ.G0, (∀ g, π (V.pr g) = k.p0 g) →
    ∀ N : Subgroup V.frame.G₀, N.Normal → IsClosed (N : Set V.frame.G₀) → (∀ g ∈ N, V.frame.conj g ∈ N) →
      (∀ u, ∀ g ∈ V.frame.Iu u, Φ.Ψ (π g) = 1 → g ∈ N) → V.frame.I0 ≤ N → π.ker ≤ N

def CrKap : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)}
    (k : GalLink η Ψ σ g₁ B M L Φ) (s : W.HidaSetting l L Ω) (_ : Ad k s) (V : s.Lev), V.S' = s.S →
    ∀ (c₁ : Coef l) (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ), IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    ∃ κ : V.frame.G₀ →* c₁.Oˣ, (∀ g, (κ (V.pr g)).val.1 = (ka g).val) ∧
      (AdicCont (maximalIdeal c₁.O) fun g => (κ g : c₁.O)) ∧
      ∀ g, κ g * κ (V.frame.conj g) = V.frame.eps c₁.O c₁.O g ^ (1 - (n : ℤ))

def CrResid : Prop :=
  ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (F : Fr.Frame l (ResidueField O))
    (G : W.GFrame l) (n : ℕ), n = 2 ∨ n = 3 → IsOpen (F.Ψ.ker : Set F.Γ) → F.Ψ F.g0 ^ 2 ≠ 1 →
    ∀ π : G.G₀ →* F.G0, Continuous π → Function.Surjective π → (∀ g, π (G.conj g) = F.conj (π g)) →
    ∀ κ : G.G₀ →* Oˣ, (AdicCont (maximalIdeal O) fun g => (κ g : O)) →
    (∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))) →
    ∃ r : W.Resid G O n, (∀ i g, r.chib i g = F.Ψ (π g) ^ Fr.w n i * W.pushCh (residue O) κ g) ∧
      ∀ v i g, r.psib v i g = r.chib i (G.φ v g)

end UpperTheory.V.Pr

end
end
