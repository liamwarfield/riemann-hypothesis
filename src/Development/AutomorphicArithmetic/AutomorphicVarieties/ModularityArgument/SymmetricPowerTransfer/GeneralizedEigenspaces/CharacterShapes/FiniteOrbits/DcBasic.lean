module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem coe_mem_orbit (U : Subgroup G) (a g : G) :
    (g : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) ↔ g ∈ DC U a := by
  constructor
  · rintro ⟨u, hu⟩
    have h : ((u.1 * a : G) : G ⧸ U) = g := by rw [← hu]; rfl
    rw [QuotientGroup.eq] at h
    exact ⟨u.1, u.2, (u.1 * a)⁻¹ * g, h, by group⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * u' : G) : G ⧸ U)
    rw [QuotientGroup.eq, show (u * a)⁻¹ * (u * a * u') = u' by group]
    exact hu'

private theorem out_mem_orbit (U : Subgroup G) (a : G) (y : G ⧸ U) :
    y ∈ MulAction.orbit U (a : G ⧸ U) ↔ y.out ∈ DC U a := by
  rw [← coe_mem_orbit, QuotientGroup.out_eq']

private theorem val_out (U : Subgroup G) {φ : G → V} (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g)
    (g y : G) (q : G ⧸ U) (h : (y : G ⧸ U) = q) : φ (g * q.out) = φ (g * y) := by
  have hm : y⁻¹ * q.out ∈ U := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact h
  have e := hφ _ hm (g * y)
  rw [show g * y * (y⁻¹ * q.out) = g * q.out by group] at e
  exact e

private theorem dcF_eq_mem (U : Subgroup G) (a : G) (φ : G → V) :
    dcF U a φ = (∑ᶠ q ∈ MulAction.orbit U (a : G ⧸ U), rightReg ℂ G V q.out) φ := by
  show (∑ᶠ q : ↑(MulAction.orbit U (a : G ⧸ U)), rightReg ℂ G V (Quotient.out (q : G ⧸ U))) φ = _
  rw [finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ U => rightReg ℂ G V q.out)]

private theorem dcF_apply (U : Subgroup G) (a : G) (h : (MulAction.orbit U (a : G ⧸ U)).Finite)
    (φ : G → V) (g : G) :
    dcF U a φ g = ∑ y ∈ Set.Finite.toFinset h, φ (g * y.out) := by
  rw [dcF_eq_mem, finsum_mem_eq_finite_toFinset_sum _ h]
  simp [LinearMap.sum_apply, Finset.sum_apply, rightReg, LinearMap.funLeft]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcBasic :
    UpperTheory.V.Z.Sym.So.DcBasic := by
  intro G V _ _ _ U a hfin0 φ hφ
  classical
  have hfin : (MulAction.orbit U (a : G ⧸ U)).Finite := hfin0
  have hO : ∀ (v : U) (y : G ⧸ U), y ∈ MulAction.orbit U (a : G ⧸ U) →
      v • y ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro v y ⟨w, rfl⟩
    exact ⟨v * w, mul_smul v w _⟩
  have h5 : ∀ (R : Finset G), (∀ y ∈ R, y ∈ DC U a) →
      (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) → ∀ g, dcF U a φ g = ∑ r ∈ R, φ (g * r) := by
    intro R hR hu g
    rw [dcF_apply U a hfin φ g]
    symm
    refine Finset.sum_bij (fun r _ => (r : G ⧸ U)) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Set.Finite.mem_toFinset]
      exact (coe_mem_orbit U a r).mpr (hR r hr)
    · intro r1 hr1 r2 hr2 he
      have h12 : r1⁻¹ * r2 ∈ U := QuotientGroup.eq.mp he
      have h22 : r2⁻¹ * r2 ∈ U := by rw [inv_mul_cancel]; exact U.one_mem
      exact (hu r2 (hR r2 hr2)).unique ⟨hr1, h12⟩ ⟨hr2, h22⟩
    · intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨r, ⟨hr, hry⟩, -⟩ := hu _ ((out_mem_orbit U a y).mp hy)
      refine ⟨r, hr, ?_⟩
      show (r : G ⧸ U) = y
      rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
      exact hry
    · intro r hr
      exact (val_out U hφ g r (r : G ⧸ U) rfl).symm
  refine ⟨?_, ?_, ?_, ?_, h5⟩
  · intro u hu g
    rw [dcF_apply U a hfin φ, dcF_apply U a hfin φ]
    let u' : U := ⟨u, hu⟩
    refine Finset.sum_nbij' (fun y => u' • y) (fun y => u'⁻¹ • y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u' y hy
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u'⁻¹ y hy
    · intro y _
      exact inv_smul_smul u' y
    · intro y _
      exact smul_inv_smul u' y
    · intro y _
      have hq : ((u * y.out : G) : G ⧸ U) = u' • y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [mul_assoc]
      exact (val_out U hφ g (u * y.out) (u' • y) hq).symm
  · intro g
    rw [dcF_apply U a hfin φ g, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp only [out_mem_orbit]
  · intro b hb
    rw [dcF_eq_mem, dcF_eq_mem, MulAction.orbit_eq_iff.mpr ((coe_mem_orbit U a b).mpr hb)]
  · intro ha
    funext g
    rw [h5 {1} ?_ ?_ g, Finset.sum_singleton, mul_one]
    · intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨a⁻¹, U.inv_mem ha, 1, U.one_mem, by group⟩
    · rintro y ⟨v, hv, v', hv', rfl⟩
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
      · rw [inv_one, one_mul]
        exact U.mul_mem (U.mul_mem hv ha) hv'
      · rintro r ⟨hr, -⟩
        exact Finset.mem_singleton.mp hr

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) (i : Fin n) :
    Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i

private theorem abs_one_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 = (absPow k (-1))⁻¹ := by
  have h0 : absPow k 0 = 1 := by
    ext x
    simp [val_absPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]

private theorem abs_zero_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 0 = 1 := by
  ext x
  simp [val_absPow]

theorem UpperTheory.V.Z.Sym.So.expoEq :
    UpperTheory.V.Z.Sym.So.ExpoEq := by
  intro k _ _ _ _ a
  have hA : ∀ x : kˣ, absPow k 1 x = (absPow k (-1) x)⁻¹ := by
    intro x
    rw [abs_one_eq]
    rfl
  have hZ : ∀ x : kˣ, absPow k 0 x = 1 := by
    intro x
    rw [abs_zero_eq]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have m0 : modExp (fun _ : Fin 3 => Unit) 0 = 2 := by decide
    have m1 : modExp (fun _ : Fin 3 => Unit) 1 = 0 := by decide
    have m2 : modExp (fun _ : Fin 3 => Unit) 2 = -2 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1, m2]
    have e0 : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
    have e1 : ((0 : ℤ) : ℂ) / 2 = 0 := by norm_num
    have e2 : ((-2 : ℤ) : ℂ) / 2 = -1 := by norm_num
    rw [e0, e1, e2, hA, hZ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, map_div]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_one]
    simp
    ring
  · intro t
    have m0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have m1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1]
    have hh : absPow k ((1 : ℤ) / 2) = absPow k 1 * absPow k ((-1 : ℤ) / 2) := by
      rw [← absPow_add]
      congr 1
      push_cast
      ring
    rw [hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      MonoidHom.one_apply, MonoidHom.mul_apply, hA, map_inv]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  · intro n ψ
    refine ⟨fun d => Units.ne_zero _, ?_, ?_⟩
    · unfold Dict.expo
      simp
    · intro d d'
      unfold Dict.expo
      rw [← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, mul_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {S U : Subgroup G}

private theorem dc_up {x g : S} (h : g ∈ DC (U.subgroupOf S) x) : (g : G) ∈ DC U (x : G) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := h
  exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u', Subgroup.mem_subgroupOf.mp hu', by simp⟩

private theorem dc_left {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : w * z ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨w * u, U.mul_mem hw hu, u', hu', by simp only [mul_assoc]⟩

private theorem dc_right {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : z * w ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨u, hu, u' * w, U.mul_mem hu' hw, by simp only [mul_assoc]⟩

private theorem dc_rep {x : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    {y : G} (hy : y ∈ DC U (x : G)) :
    ∃ t : S, t ∈ U.subgroupOf S ∧ ((t * x : S) : G)⁻¹ * y ∈ U := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨c, hc, hcx, hcS⟩ := hx u hu
  refine ⟨⟨u * c⁻¹, hcS⟩, Subgroup.mem_subgroupOf.mpr (U.mul_mem hu (U.inv_mem hc)), ?_⟩
  have e : ((⟨u * c⁻¹, hcS⟩ * x : S) : G)⁻¹ * (u * (x : G) * u') = c * u' := by
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc c, hcx]
    group
  rw [e]
  exact U.mul_mem hc hu'

private theorem dc_down {x g : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    (hg : (g : G) ∈ DC U (x : G)) : g ∈ DC (U.subgroupOf S) x := by
  obtain ⟨t, ht, hw⟩ := dc_rep hx hg
  refine ⟨t, ht, (t * x)⁻¹ * g, Subgroup.mem_subgroupOf.2 (by simpa using hw), ?_⟩
  group

private theorem mk_eq_of {r r' : S} (h : (r : G)⁻¹ * r' ∈ U) :
    (r : S ⧸ U.subgroupOf S) = r' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h

private theorem finOrb_sub {a : S} (h : AlgebraTools.FinOrb U U (a : G)) :
    AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a := by
  have inj : Function.Injective
      (fun q : S ⧸ U.subgroupOf S => (((Quotient.out q : S) : G) : G ⧸ U)) := by
    intro q1 q2 e
    dsimp only at e
    have e' := QuotientGroup.eq.mp e
    calc q1 = ((Quotient.out q1 : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q1).symm
      _ = ((Quotient.out q2 : S) : S ⧸ U.subgroupOf S) := mk_eq_of e'
      _ = q2 := QuotientGroup.out_eq' q2
  apply Set.Finite.of_finite_image _ inj.injOn
  apply h.subset
  rintro _ ⟨q, ⟨k, rfl⟩, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (k.1 * a)
  refine ⟨⟨((k.1 : S) : G), k.2⟩, ?_⟩
  have hq : (k • (a : S ⧸ U.subgroupOf S)) = ((k.1 * a : S) : S ⧸ U.subgroupOf S) := rfl
  dsimp only
  rw [hq, ht]
  show ((((k.1 : S) : G) * (a : G) : G) : G ⧸ U) = _
  rw [QuotientGroup.eq]
  convert Subgroup.mem_subgroupOf.mp t.2 using 1
  simp only [Subgroup.coe_mul]
  group

private theorem uf_sub {a b : S}
    (hab : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ c * (b : G) = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (hUF : UF U (a : G) (b : G)) : UF (U.subgroupOf S) a b := by
  have ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, -, h3, -⟩ := hab u hu
    exact ⟨c, hc, h1, h3⟩
  have hb : ∀ u ∈ U, ∃ c ∈ U, c * (b : G) = b * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, -, h2, h3, -⟩ := hab u hu
    exact ⟨c, hc, h2, h3⟩
  have hab' : ∀ u ∈ U, ∃ c ∈ U, c * ((a * b : S) : G) = ((a * b : S) : G) * c ∧ u * c⁻¹ ∈ S :=
    fun u hu => by
      obtain ⟨c, hc, h1, h2, h3, -⟩ := hab u hu
      refine ⟨c, hc, ?_, h3⟩
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  intro g
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · have hg' : (g : G) ∈ DC U ((a : G) * b) := by
      rw [← Subgroup.coe_mul]
      exact dc_up hg
    obtain ⟨Y, ⟨hY1, hY2⟩, hYu⟩ := (hUF g).1 hg'
    obtain ⟨t, ht, htY⟩ := dc_rep ha hY1
    have hrg : (t * a)⁻¹ * g ∈ DC (U.subgroupOf S) b := by
      apply dc_down hb
      have e : (((t * a)⁻¹ * g : S) : G)
          = (((t * a : S) : G)⁻¹ * Quotient.out Y) * ((Quotient.out Y)⁻¹ * g) := by
        push_cast
        group
      rw [e]
      exact dc_left htY hY2
    have hrY : ((((t * a : S) : G)) : G ⧸ U) = Y := by
      rw [← QuotientGroup.out_eq' Y]
      exact QuotientGroup.eq.mpr htY
    have key : ∀ s : G, s ∈ DC U a → s⁻¹ * g ∈ DC U b → (s : G ⧸ U) = Y := by
      intro s hs1 hs2
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U s
      refine hYu _ ⟨?_, ?_⟩
      · rw [hk]
        exact dc_right k.2 hs1
      · rw [hk, mul_inv_rev, mul_assoc]
        exact dc_left (inv_mem k.2) hs2
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · rw [hk]
      exact dc_right k.2 ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    · rw [hk, mul_inv_rev, mul_assoc]
      exact dc_left (inv_mem k.2) hrg
    · rintro z ⟨hz1, hz2⟩
      have hz : (((Quotient.out z : S) : G) : G ⧸ U) = Y :=
        key _ (dc_up hz1) (by simpa using dc_up hz2)
      calc z = ((Quotient.out z : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' z).symm
        _ = _ := mk_eq_of (QuotientGroup.eq.mp (hz.trans hrY.symm))
  · have h1 := (hUF g).2 y (dc_up hy) (by simpa using dc_up hyg)
    apply dc_down hab'
    rw [Subgroup.coe_mul]
    exact h1

private theorem reps_sub {a : S} (ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S)
    (hfin : AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a) :
    ∃ R : Finset S, (∀ y ∈ R, y ∈ DC (U.subgroupOf S) a) ∧
      (∀ y ∈ DC (U.subgroupOf S) a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U.subgroupOf S) ∧
      ∀ y ∈ DC U (a : G), ∃! r : S, r ∈ R ∧ (r : G)⁻¹ * y ∈ U := by
  classical
  have orb : ∀ k : S, k ∈ U.subgroupOf S →
      ((k * a : S) : S ⧸ U.subgroupOf S) ∈
        MulAction.orbit (U.subgroupOf S) (a : S ⧸ U.subgroupOf S) :=
    fun k hk => ⟨⟨k, hk⟩, rfl⟩
  refine ⟨hfin.toFinset.image (fun q => Quotient.out q), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.mp hq
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) ((k : S) * a)
    have hq' : k • (a : S ⧸ U.subgroupOf S) = (((k : S) * a : S) : S ⧸ U.subgroupOf S) := rfl
    dsimp only
    rw [hq', hh]
    exact dc_right h.2 ⟨k, k.2, 1, one_mem _, (mul_one _).symm⟩
  · intro y hy
    obtain ⟨u, hu, u', hu', rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (u * a)
    refine ⟨Quotient.out ((u * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb u hu), rfl⟩
    · rw [hh]
      have e : (u * a * (h : S))⁻¹ * (u * a * u') = (h : S)⁻¹ * u' := by group
      rw [e]
      exact mul_mem (inv_mem h.2) hu'
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((u * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = ((u * a * u' : S) : S ⧸ U.subgroupOf S) := QuotientGroup.eq.mpr hry
          _ = _ := QuotientGroup.eq.mpr (by
            rw [show (u * a * u')⁻¹ * (u * a) = u'⁻¹ by group]
            exact inv_mem hu')
      rw [e]
  · intro y hy
    obtain ⟨t, ht, hty⟩ := dc_rep ha hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨Quotient.out ((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb t ht), rfl⟩
    · rw [hh]
      have e : ((t * a * (h : S) : S) : G)⁻¹ * y
          = ((h : S) : G)⁻¹ * (((t * a : S) : G)⁻¹ * y) := by
        push_cast
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp h.2)) hty
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((t * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = _ := mk_eq_of (by
            have m := U.mul_mem hry (U.inv_mem hty)
            convert m using 1
            group)
      rw [e]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcSub :
    UpperTheory.V.Z.Sym.So.DcSub := by
  intro G V _ _ _ S U a hfin ha _
  have ha' : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, h2, _⟩ := ha u hu
    exact ⟨c, hc, h1, h2⟩
  have hfin' := finOrb_sub hfin
  exact ⟨hfin', fun g => ⟨dc_up, dc_down ha'⟩, fun b hb hUF => uf_sub hb hUF, reps_sub ha' hfin'⟩

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem out_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ i ∈ U, ((g : G ⧸ U)).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem orb_iff {G : Type} [Group G] (U : Subgroup G) (a : G) (p : G ⧸ U) :
    p ∈ MulAction.orbit U (a : G ⧸ U) ↔ p.out ∈ DC U a := by
  have key : ∀ u : U, u • (a : G ⧸ U) = (((u : G) * a : G) : G ⧸ U) := fun u => rfl
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((u : G) * a)
    refine ⟨u, u.2, i, hi, ?_⟩
    dsimp only
    rw [key, h]
  · rintro ⟨u, hu, u', hu', h⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp only
    rw [key, ← QuotientGroup.out_eq' p, h]
    refine QuotientGroup.eq.mpr ?_
    rw [inv_mul_cancel_left]
    exact hu'

private theorem dcF_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G)
    [Fintype (MulAction.orbit U (a : G ⧸ U))] (φ : G → V) (g : G) :
    dcF U a φ g = ∑ q : MulAction.orbit U (a : G ⧸ U), φ (g * (q : G ⧸ U).out) := by
  simp only [dcF, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Finset.sum_apply]
  rfl

private theorem mul_mem_dc_of_mem_subgroup {G : Type} [Group G] (U : Subgroup G) (c x i : G) (hx : x ∈ DC U c) (hi : i ∈ U) :
    x * i ∈ DC U c := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hx
  exact ⟨u, hu, u' * i, U.mul_mem hu' hi, mul_assoc _ _ _⟩

private theorem quotient_out_mem_dc_iff {G : Type} [Group G] (U : Subgroup G) (c x : G) :
    ((x : G ⧸ U)).out ∈ DC U c ↔ x ∈ DC U c := by
  obtain ⟨i, hi, h⟩ := out_mul U x
  rw [h]
  constructor
  · intro hx
    simpa using mul_mem_dc_of_mem_subgroup U c _ i⁻¹ hx (U.inv_mem hi)
  · intro hx
    exact mul_mem_dc_of_mem_subgroup U c x i hx hi

theorem UpperTheory.V.Z.Sym.So.uFMul :
    UpperTheory.V.Z.Sym.So.UFMul := by
  intro G V _ _ _ U a b ha hb hab huf φ hφ
  haveI : Fintype (MulAction.orbit U (a : G ⧸ U)) := Set.Finite.fintype ha
  haveI : Fintype (MulAction.orbit U (b : G ⧸ U)) := Set.Finite.fintype hb
  haveI : Fintype (MulAction.orbit U ((a * b : G) : G ⧸ U)) := Set.Finite.fintype hab
  funext g
  rw [dcF_sum U a _ g, dcF_sum U (a * b) φ g]
  simp only [dcF_sum U b φ]
  rw [← Fintype.sum_prod_type']
  have hmem : ∀ x : MulAction.orbit U (a : G ⧸ U) × MulAction.orbit U (b : G ⧸ U),
      (((x.1 : G ⧸ U).out * (x.2 : G ⧸ U).out : G) : G ⧸ U) ∈ MulAction.orbit U ((a * b : G) : G ⧸ U) := by
    intro x
    refine (orb_iff U (a * b) _).mpr ((quotient_out_mem_dc_iff U _ _).mpr ((huf _).2 _ ((orb_iff U a _).mp x.1.2) ?_))
    rw [inv_mul_cancel_left]
    exact (orb_iff U b _).mp x.2.2
  refine Fintype.sum_bijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩ _ _ ?_
  · rintro ⟨q, r⟩ ⟨q', r'⟩ hx
    have hx' : (((q : G ⧸ U).out * (r : G ⧸ U).out : G) : G ⧸ U) =
        (((q' : G ⧸ U).out * (r' : G ⧸ U).out : G) : G ⧸ U) := congrArg Subtype.val hx
    obtain ⟨i, hi, hs⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    obtain ⟨i', hi', hs'⟩ := out_mul U ((q' : G ⧸ U).out * (r' : G ⧸ U).out)
    have hsab : (q : G ⧸ U).out * (r : G ⧸ U).out * i ∈ DC U (a * b) := by
      have := (orb_iff U (a * b) _).mp (hmem (q, r))
      rwa [hs] at this
    rw [hx'] at hs
    have he : (q : G ⧸ U).out * (r : G ⧸ U).out * i = (q' : G ⧸ U).out * (r' : G ⧸ U).out * i' :=
      hs.symm.trans hs'
    obtain ⟨y, -, huniq⟩ := (huf _).1 hsab
    have h1 : (q : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q.2, by
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i ((orb_iff U b _).mp r.2) hi⟩
    have h2 : (q' : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q'.2, by
      rw [he]
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i' ((orb_iff U b _).mp r'.2) hi'⟩
    have hq : q = q' := Subtype.ext (h1.trans h2.symm)
    subst hq
    have hr : (r : G ⧸ U).out * i = (r' : G ⧸ U).out * i' := by
      rw [mul_assoc, mul_assoc] at he
      exact mul_left_cancel he
    have hr' : (r : G ⧸ U) = r' := by
      rw [← QuotientGroup.out_eq' (r : G ⧸ U), ← QuotientGroup.out_eq' (r' : G ⧸ U),
        ← QuotientGroup.mk_mul_of_mem (r : G ⧸ U).out hi, hr, QuotientGroup.mk_mul_of_mem _ hi']
    exact Prod.ext rfl (Subtype.ext hr')
  · rintro ⟨s, hs⟩
    have hsd : (s : G ⧸ U).out ∈ DC U (a * b) := (orb_iff U (a * b) s).mp hs
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := (huf _).1 hsd
    refine ⟨(⟨y, (orb_iff U a y).mpr hy1⟩,
      ⟨((y.out⁻¹ * s.out : G) : G ⧸ U), (orb_iff U b _).mpr ((quotient_out_mem_dc_iff U _ _).mpr hy2)⟩), ?_⟩
    apply Subtype.ext
    obtain ⟨i, hi, h⟩ := out_mul U (y.out⁻¹ * s.out)
    dsimp only
    rw [h, ← mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ hi, QuotientGroup.out_eq']
  · rintro ⟨q, r⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    dsimp only
    rw [h, ← mul_assoc, ← mul_assoc, hφ i hi]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Box

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K U : ∀ v, Subgroup (Gv v)}

private theorem memBox (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) :
    g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

private theorem smulMk {A : Type} [Group A] (W W' : Subgroup A) (u : W) (x : A) :
    u • (x : A ⧸ W') = (((u : A) * x : A) : A ⧸ W') := rfl

end Box

end UpperTheory.V.Z.Sym.So

private theorem mem_doubleCoset_iff_exists_eq_mul_mul {A : Type} [Group A] {W : Subgroup A} {a x : A} :
    x ∈ DC W a ↔ ∃ u ∈ W, ∃ u' ∈ W, x = u * a * u' := Iff.rfl

private theorem mul_mem_doubleCoset_of_mem_doubleCoset_of_mem {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : x * c ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨u, hu, u' * c, mul_mem hu' hc, by simp only [mul_assoc]⟩

private theorem mul_mem_doubleCoset_of_mem_of_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : c * x ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨c * u, mul_mem hc hu, u', hu', by simp only [mul_assoc]⟩

private theorem out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a b g x : A}
    (h1 : x ∈ DC W a) (h2 : x⁻¹ * g ∈ DC W b) :
    Quotient.out (x : A ⧸ W) ∈ DC W a ∧ (Quotient.out (x : A ⧸ W))⁻¹ * g ∈ DC W b := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul W x
  rw [hc]
  refine ⟨mul_mem_doubleCoset_of_mem_doubleCoset_of_mem h1 c.2, ?_⟩
  rw [mul_inv_rev, mul_assoc]
  exact mul_mem_doubleCoset_of_mem_of_mem_doubleCoset h2 (inv_mem c.2)

private theorem quotientGroup_coe_out_eq_self {A : Type} [Group A] (W : Subgroup A) (y : A ⧸ W) :
    ((Quotient.out y : A) : A ⧸ W) = y := Quotient.out_eq y

theorem UpperTheory.V.Z.Sym.So.uFBox :
    UpperTheory.V.Z.Sym.So.UFBox := by
  intro I G _ Gv _ K U P S _ a ha
  classical
  have hB : ∀ g, g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := memBox P U
  have glue : ∀ x : (v : I) → Gv v, (∀ v ∉ S, x v = 1) → ∃ h : G, ∀ v, P.p v h = x v := by
    intro x hx
    apply P.surj
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
    intro v hv
    by_contra hvS
    exact hv (by rw [hx v hvS]; exact one_mem _)
  have key : ∀ c : G, (∀ v ∉ S, P.p v c ∈ U v) → ∀ g : G, g ∈ DC (P.box U) c ↔
      (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v c)) ∧ ∀ v ∉ S, P.p v g ∈ U v := by
    intro c hc g
    constructor
    · intro hg
      obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hg
      rw [hB] at hu hu'
      refine ⟨fun v _ => mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨P.p v u, hu v, P.p v u', hu' v, by rw [map_mul, map_mul]⟩, fun v hv => ?_⟩
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hu v) (hc v hv)) (hu' v)
    · rintro ⟨h1, h2⟩
      have h1' : ∀ v ∈ S, ∃ u ∈ U v, ∃ u' ∈ U v, P.p v g = u * P.p v c * u' :=
        fun v hv => mem_doubleCoset_iff_exists_eq_mul_mul.1 (h1 v hv)
      choose! u hu u' hu' hg using h1'
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then u v else 1) (fun v hv => if_neg hv)
      refine mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨w, ?_, c⁻¹ * w⁻¹ * g, ?_, by group⟩
      · rw [hB]
        intro v
        rw [hw]
        split_ifs with hv
        exacts [hu v hv, one_mem _]
      · rw [hB]
        intro v
        rw [map_mul, map_mul, map_inv, map_inv, hw]
        split_ifs with hv
        · rw [hg v hv]
          have e : (P.p v c)⁻¹ * (u v)⁻¹ * (u v * P.p v c * u' v) = u' v := by group
          rw [e]
          exact hu' v hv
        · rw [inv_one, mul_one]
          exact mul_mem (inv_mem (hc v hv)) (h2 v hv)
  refine ⟨key a ha, ?_, ?_⟩
  · intro hf
    unfold UpperTheory.V.AlgebraTools.FinOrb at hf ⊢
    have hout : ∀ u : P.box U, ∀ v ∉ S,
        P.p v (Quotient.out (u • (a : G ⧸ P.box U))) ∈ U v := by
      intro u v hv
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      rw [smulMk, hc, map_mul, map_mul]
      exact mul_mem (mul_mem ((hB _).1 u.2 v) (ha v hv)) ((hB _).1 c.2 v)
    apply Set.Finite.of_finite_image
      (f := fun (y : G ⧸ P.box U) (v : S) => ((P.p v.1 (Quotient.out y) : Gv v.1) : Gv v.1 ⧸ U v.1))
    · refine (Set.Finite.pi (t := fun v : S =>
        MulAction.orbit (U v.1) ((P.p v.1 a : Gv v.1) : Gv v.1 ⧸ U v.1)) (fun v => hf v.1 v.2)).subset ?_
      rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
      rw [Set.mem_univ_pi]
      intro v
      refine ⟨⟨P.p v.1 u, (hB _).1 u.2 v.1⟩, ?_⟩
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      simp only [smulMk]
      rw [hc, QuotientGroup.eq]
      convert (hB _).1 c.2 v.1 using 1
      simp only [map_mul, Subgroup.coe_mk]
      group
    · rintro _ ⟨u1, rfl⟩ _ ⟨u2, rfl⟩ h12
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans ((QuotientGroup.eq.2 ?_).trans (quotientGroup_coe_out_eq_self _ _))
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      by_cases hv : v ∈ S
      · exact QuotientGroup.eq.1 (congrFun h12 ⟨v, hv⟩)
      · exact mul_mem (inv_mem (hout u1 v hv)) (hout u2 v hv)
  · intro b hb hloc g
    have hab : ∀ v ∉ S, P.p v (a * b) ∈ U v := fun v hv => by
      rw [map_mul]
      exact mul_mem (ha v hv) (hb v hv)
    constructor
    · intro hg
      obtain ⟨hgS, hgN⟩ := (key _ hab g).1 hg
      have hgl : ∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a * P.p v b) := fun v hv => by
        rw [← map_mul]
        exact hgS v hv
      have hl : ∀ v ∈ S, ∃ z, z ∈ DC (U v) (P.p v a) ∧ z⁻¹ * P.p v g ∈ DC (U v) (P.p v b) := by
        intro v hv
        obtain ⟨y, hy, -⟩ := (hloc v hv (P.p v g)).1 (hgl v hv)
        exact ⟨_, hy⟩
      choose! z hz1 hz2 using hl
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then z v else 1) (fun v hv => if_neg hv)
      have hw1 : w ∈ DC (P.box U) a := (key a ha w).2
        ⟨fun v hv => by rw [hw, if_pos hv]; exact hz1 v hv,
         fun v hv => by rw [hw, if_neg hv]; exact one_mem _⟩
      have hw2 : w⁻¹ * g ∈ DC (P.box U) b := (key b hb _).2
        ⟨fun v hv => by rw [map_mul, map_inv, hw, if_pos hv]; exact hz2 v hv,
         fun v hv => by rw [map_mul, map_inv, hw, if_neg hv, inv_one, one_mul]; exact hgN v hv⟩
      refine ⟨(w : G ⧸ P.box U), out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hw1 hw2, ?_⟩
      rintro y ⟨hy1, hy2⟩
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans (QuotientGroup.eq.2 ?_)
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      have ha1 := (key a ha _).1 hy1
      have hb1 := (key b hb _).1 hy2
      by_cases hv : v ∈ S
      · have hb2 := hb1.1 v hv
        rw [map_mul, map_inv] at hb2
        have hz2' := hz2 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz2'
        have hz1' := hz1 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz1'
        have e := ((hloc v hv (P.p v g)).1 (hgl v hv)).unique
          (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset (ha1.1 v hv) hb2) (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hz1' hz2')
        exact QuotientGroup.eq.1 e
      · rw [hw, if_neg hv]
        exact mul_mem (inv_mem (ha1.2 v hv)) (one_mem _)
    · intro y hy1 hy2
      refine (key _ hab g).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := ((key b hb _).1 hy2).1 v hv
        rw [map_mul, map_inv] at h2
        rw [map_mul]
        exact (hloc v hv (P.p v g)).2 (P.p v y) (((key a ha y).1 hy1).1 v hv) h2
      · have h1 := ((key a ha y).1 hy1).2 v hv
        have h2 := ((key b hb _).1 hy2).2 v hv
        rw [map_mul, map_inv] at h2
        have h3 := mul_mem h1 h2
        rwa [mul_inv_cancel_left] at h3

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcLocal
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_end_apply {α M : Type} [AddCommGroup M] [Module ℂ M] [Finite α]
    (f : α → Module.End ℂ M) (x : M) : (∑ᶠ a, f a) x = ∑ᶠ a, f a x := by
  cases nonempty_fintype α
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Z.Sym.So.dcLocal :
    UpperTheory.V.Z.Sym.So.DcLocal := by
  intro H G V _ _ _ _ j p J U hpj hU hJ d hd

  have hin : ∀ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) →
      ((j h : G) : G ⧸ U) ∈ MulAction.orbit U ((j d : G) : G ⧸ U) := by
    rintro h ⟨a, ha⟩
    have h1 : (((a : H) * d : H) : H ⧸ J) = (h : H ⧸ J) := ha
    have h2 : ((a : H) * d)⁻¹ * h ∈ J := QuotientGroup.eq.1 h1
    have h3 : (j ((a : H) * d))⁻¹ * j h ∈ U := by
      have := hJ _ h2
      simpa [map_mul] using this
    refine ⟨⟨j a, hJ _ a.2⟩, ?_⟩
    change ((j a * j d : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [map_mul] using h3

  have hsurj : ∀ y ∈ MulAction.orbit U ((j d : G) : G ⧸ U),
      ∃ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) ∧ ((j h : G) : G ⧸ U) = y := by
    rintro y ⟨u, rfl⟩
    obtain ⟨hpu, hc⟩ := hU u u.2
    set c : G := (u : G) * (j (p u))⁻¹ with hcdef
    have hcU : c ∈ U := U.mul_mem u.2 (U.inv_mem (hJ _ hpu))
    refine ⟨p u * d, ⟨⟨p u, hpu⟩, rfl⟩, ?_⟩
    change ((j (p u * d) : G) : G ⧸ U) = (((u : G) * j d : G) : G ⧸ U)
    have hfac : (u : G) * j d = j (p u * d) * c := by
      have h1 : (u : G) = c * j (p u) := by simp [hcdef]
      calc (u : G) * j d = c * j (p u * d) := by rw [map_mul, ← mul_assoc, ← h1]
        _ = j (p u * d) * c := hc _
    rw [hfac]
    exact (QuotientGroup.mk_mul_of_mem _ hcU).symm
  have hfin : AlgebraTools.FinOrb U U (j d) := by
    refine (hd.image fun q : H ⧸ J => ((j q.out : G) : G ⧸ U)).subset ?_
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hsurj y hy
    refine ⟨(h : H ⧸ J), hh, ?_⟩
    change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
    have := hJ _ h1
    simpa [map_mul] using this
  refine ⟨hfin, fun φ hφ => ?_⟩
  haveI : Finite (MulAction.orbit J (d : H ⧸ J)) := Set.Finite.to_subtype hd
  haveI : Finite (MulAction.orbit U ((j d : G) : G ⧸ U)) := Set.Finite.to_subtype hfin

  let e : MulAction.orbit J (d : H ⧸ J) → MulAction.orbit U ((j d : G) : G ⧸ U) := fun q =>
    ⟨((j (q : H ⧸ J).out : G) : G ⧸ U), hin _ (by simpa using q.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hqq
      have h1 : ((j (q : H ⧸ J).out : G) : G ⧸ U) = ((j (q' : H ⧸ J).out : G) : G ⧸ U) :=
        congrArg Subtype.val hqq
      have h2 : (j (q : H ⧸ J).out)⁻¹ * j (q' : H ⧸ J).out ∈ U := QuotientGroup.eq.1 h1
      have h3 := (hU _ h2).1
      have h4 : ((q : H ⧸ J).out)⁻¹ * (q' : H ⧸ J).out ∈ J := by
        simpa [map_mul, map_inv, hpj] using h3
      have h5 : (((q : H ⧸ J).out : H) : H ⧸ J) = (((q' : H ⧸ J).out : H) : H ⧸ J) :=
        QuotientGroup.eq.2 h4
      apply Subtype.ext
      simpa using h5
    · rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := hsurj y hy
      refine ⟨⟨(h : H ⧸ J), hh⟩, Subtype.ext ?_⟩
      change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
      refine QuotientGroup.eq.2 ?_
      have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
      have := hJ _ h1
      simpa [map_mul] using this
  unfold dcF dc
  rw [finsum_end_apply, finsum_end_apply, ← finsum_comp e he]
  refine finsum_congr fun q => ?_
  funext g
  have h1 : (((e q : G ⧸ U)).out)⁻¹ * j (q : H ⧸ J).out ∈ U := QuotientGroup.eq.1 (by simp [e])
  have h2 := hφ _ h1 (g * ((e q : G ⧸ U)).out)
  change φ (g * ((e q : G ⧸ U)).out) = φ (g * j (q : H ⧸ J).out)
  rw [← h2]
  congr 1
  group

end
end
