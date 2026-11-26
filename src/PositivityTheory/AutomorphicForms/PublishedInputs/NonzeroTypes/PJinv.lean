module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJinv
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

namespace P_Jinv

def CcUm : Prop :=
  ∀ a b c : Fin G.s, cc G.μ a a = 0 ∧ cc G.μ a b = cc G.μ b a ∧ cc G.μ a c ≤ max (cc G.μ a b) (cc G.μ b c)

def fe (i j : Fin n) : ℕ := if G.bl j < G.bl i then cc G.μ (G.bl j) (G.bl i) else 0

theorem fe_self (i : Fin n) : fe G i i = 0 := by simp [fe]

theorem fe_tri (hU : CcUm G) (i l j : Fin n) : fe G i j ≤ fe G i l + fe G l j := by
  by_cases hij : G.bl j < G.bl i
  · have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rw [e1]
    rcases le_or_gt (G.bl l) (G.bl j) with hlj | hjl
    · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos (lt_of_le_of_lt hlj hij)
      rw [e2]
      exact le_add_right (G.ball _ _ _ _ hlj hij le_rfl)
    · rcases le_or_gt (G.bl i) (G.bl l) with hil | hli
      · have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e3]
        exact le_add_left (G.ball _ _ _ _ le_rfl hij hil)
      · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos hli
        have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e2, e3]
        have := (hU (G.bl j) (G.bl l) (G.bl i)).2.2
        omega
  · have e1 : fe G i j = 0 := if_neg hij
    omega

def S (hU : CcUm G) : Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {A | ∀ i j, A i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ fe G i j}
  mul_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => ?_
    refine Ideal.pow_le_pow_right (fe_tri G hU i l j) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (hA i l) (hB l j)
  one_mem' := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _
  add_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    exact Ideal.add_mem _ (hA i j) (hB i j)
  zero_mem' := fun _ _ => zero_mem _
  algebraMap_mem' := by
    intro r i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _

theorem inv_mem (hU : CcUm G) (h : GL (Fin n) 𝒪[k])
    (hh : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU) :
    ((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
  set A : Matrix (Fin n) (Fin n) 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]) with hAdef
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right hdet
  have h0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add A.charpoly, map_add (f := _), map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have h1 : A * Polynomial.aeval A A.charpoly.divX = -algebraMap 𝒪[k] _ (A.charpoly.coeff 0) :=
    eq_neg_of_add_eq_zero_left h0
  have key : A * (-((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • Polynomial.aeval A A.charpoly.divX) = 1 := by
    rw [mul_smul_comm, h1, neg_smul_neg, ← hu, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
  have hinv := Units.eq_inv_of_mul_eq_one_left key
  rw [← hinv]
  refine Subalgebra.smul_mem _ ?_ _
  have hval : Polynomial.aeval A A.charpoly.divX =
      (S G hU).val (Polynomial.aeval (⟨A, hh⟩ : S G hU) A.charpoly.divX) :=
    (Polynomial.aeval_algHom_apply (S G hU).val (⟨A, hh⟩ : S G hU) A.charpoly.divX)
  rw [hval]
  exact Subtype.prop _

end P_Jinv

open P_Jinv in
theorem step_Jinv : JacquetInverseProp G := by
  intro hU0 hB g hg
  have hU : CcUm G := hU0 G.s G.μ (fun a b => ⟨_, hB.2.2.2 a b⟩)
  obtain ⟨hK, hJ⟩ := hg
  obtain ⟨h, rfl⟩ := hK
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hmem : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
    intro a b
    by_cases hab : G.bl b < G.bl a
    · obtain ⟨y, hy, hyx⟩ := hJ a b hab
      have hy' : y = (h : Matrix (Fin n) (Fin n) 𝒪[k]) a b := hinj hyx
      have e1 : fe G a b = cc G.μ (G.bl b) (G.bl a) := if_pos hab
      rw [e1, ← hy']
      exact hy
    · have e1 : fe G a b = 0 := if_neg hab
      rw [e1, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have hi := inv_mem G hU h hmem
  refine ⟨⟨h⁻¹, (map_inv _ h)⟩, fun i j hij => ?_⟩
  refine ⟨((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j, ?_, ?_⟩
  · have := hi i j
    have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rwa [e1] at this
  · rw [← map_inv]
    rfl

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowAlgebraMap
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

abbrev red (n r : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ r))


variable (k) in
def H (n r : ℕ) : Subgroup (GL (Fin n) k) := (red (k := k) n r).ker.map (incl n)

theorem inPow_algebraMap (r : ℕ) (y : 𝒪[k]) :
    InPow r (algebraMap 𝒪[k] k y) ↔ y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  constructor
  · rintro ⟨z, hz, e⟩
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_sub (n : ℕ) (u : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (((incl n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) =
      algebraMap 𝒪[k] k ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) := by
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

theorem red_eq_one_iff (n r : ℕ) (u : GL (Fin n) 𝒪[k]) :
    red (k := k) n r u = 1 ↔ ∀ i j, ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) ∈
      IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  rw [Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [← Ideal.Quotient.eq]
    split_ifs with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
  · intro h
    ext i j
    have h' := Ideal.Quotient.eq.2 (h i j)
    split_ifs at h' with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'

theorem mem_KC_iff (n r : ℕ) (g : GL (Fin n) k) : g ∈ KC k n r ↔ g ∈ H k n r := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hP⟩
    refine ⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩
    have := hP i j
    rwa [entry_sub, inPow_algebraMap] at this
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [entry_sub, inPow_algebraMap]
    exact (red_eq_one_iff n r u).1 hu i j

theorem coe_H (n r : ℕ) : (H k n r : Set (GL (Fin n) k)) = KC k n r :=
  Set.ext fun g => (mem_KC_iff n r g).symm

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  let A : AddSubgroup k :=
    (IsLocalRing.maximalIdeal 𝒪[k] ^ r).toAddSubgroup.map (algebraMap 𝒪[k] k).toAddMonoidHom
  have hA : (A : Set k) = {x : k | InPow r x} := by
    ext x
    simp only [A, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq, InPow]
    rfl
  rw [← hA]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field 𝒪[k])
  have hc : (algebraMap 𝒪[k] k w) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    exact hw0 (Subtype.val_injective h)
  refine A.isOpen_of_mem_nhds (g := 0) ?_
  rw [mem_nhds_iff]
  refine ⟨(fun x => (algebraMap 𝒪[k] k w) ^ r * x) '' (𝒪[k] : Set k), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨w ^ r * ⟨y, hy⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw r), ?_⟩
    show algebraMap 𝒪[k] k (w ^ r * ⟨y, hy⟩) = algebraMap 𝒪[k] k w ^ r * y
    rw [map_mul, map_pow]
    rfl
  · have := (Homeomorph.mulLeft₀ _ hc).isOpenMap _ (Valuation.isOpen_integer (v := valuation k))
    simpa using this
  · exact ⟨0, zero_mem _, mul_zero _⟩

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x : k | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_inPow r).preimage ?_)
  have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
  fun_prop

end UpperTheory.TNZ.Grp.P_KC

namespace UpperTheory.TNZ.Grp

open P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_KC {n : ℕ} (G : Grp k n) : CompactOpenKernelProp G := by
  intro hB r
  refine ⟨?_, ?_, isOpen_KC n r, fun g hg => hg.1, ?_⟩
  · show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r
    rw [← coe_H, Subgroup.closure_eq]
  · intro g hg u hu
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := (mem_KC_iff n r u).1 hu
    refine (mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  · intro hr g hg
    refine ⟨hg.1, fun i j hij => ?_⟩
    have hne : i ≠ j := fun h => (ne_of_lt hij) (h ▸ rfl)
    obtain ⟨y, hy, e⟩ := hg.2 i j
    rw [if_neg hne, sub_zero] at e
    have hc : cc G.μ (G.bl j) (G.bl i) ≤ r := (hB.2.1 (G.bl j) (G.bl i)).le.trans hr
    exact ⟨y, Ideal.pow_le_pow_right hc hy, e⟩

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamBasic
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_triv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1 := by
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hker : (μ.ker : Set kˣ) ∈ nhds (1 : kˣ) := hμ.mem_nhds (one_mem _)
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hker
  obtain ⟨U, hU, hUsub⟩ := hker
  rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at hU
  obtain ⟨γ, hγ⟩ := hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hϖ1 : valuation k (ϖ : k) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hϖ.not_isUnit
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hϖ1 γ
  refine ⟨c, fun u hu => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨z, hz⟩ := hu
  have hz1 : valuation k (z : k) ≤ 1 := (Valuation.mem_integer_iff _ _).mp z.2
  have hv : valuation k (((unitIncl k u : kˣ) : k) - 1) < γ := by
    have h1 : ((unitIncl k u : kˣ) : k) - 1 = (ϖ : k) ^ c * (z : k) := by
      change ((u : 𝒪[k]) : k) - 1 = _
      have := congrArg (fun x : 𝒪[k] => (x : k)) hz
      push_cast at this
      exact this
    rw [h1, map_mul, map_pow]
    calc valuation k (ϖ : k) ^ c * valuation k (z : k) ≤ valuation k (ϖ : k) ^ c * 1 := by gcongr
      _ = valuation k (ϖ : k) ^ c := mul_one _
      _ < γ := hc
  exact hUsub (hγ hv)

theorem triv_cond (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (u : 𝒪[k]ˣ)
    (hu : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res μ)) : res μ u = 1 := by
  obtain ⟨c, hc⟩ := exists_triv μ hμ
  exact Nat.sInf_mem (s := {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1})
    ⟨c, hc⟩ u hu

theorem minor_unit {n r : ℕ} (hr : 1 ≤ r) {g : GL (Fin n) k} (hg : g ∈ KC k n r) {ι : Type} {_ : Fintype ι}
    {_ : DecidableEq ι} (f : ι → Fin n) (hf : Function.Injective f) :
    ∃ u : 𝒪[k]ˣ, ((g : Matrix (Fin n) (Fin n) k).submatrix f f).det = algebraMap 𝒪[k] k u ∧
      (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  obtain ⟨⟨h, rfl⟩, hc⟩ := hg
  set I := IsLocalRing.maximalIdeal 𝒪[k] ^ r
  set M : Matrix ι ι 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix f f with hM
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hentry : ∀ i j, (M i j) - (if i = j then 1 else 0) ∈ I := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hc (f i) (f j)
    have : y = M i j - (if i = j then 1 else 0) := by
      apply hinj
      rw [hyx]
      simp only [hM, Matrix.submatrix_apply, map_sub, hf.eq_iff]
      split_ifs <;> simp [Matrix.GeneralLinearGroup.map]
    rw [← this]
    exact hy
  have hmk : M.map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply]
    have := Ideal.Quotient.eq.mpr (hentry i j)
    rw [this]
    split_ifs <;> simp
  have hD : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.mapMatrix_apply, hmk, Matrix.det_one, map_one]
  have hDm : M.det - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := Ideal.pow_le_self (by omega) hD
  have hunit : IsUnit M.det := by
    by_contra hn
    have h1 : M.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 hDm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, RingHom.map_det]
    rfl
  · rw [IsUnit.unit_spec]
    exact hD

theorem chk_unit (μ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) : chk μ (algebraMap 𝒪[k] k u) = ((res μ u : ℂˣ) : ℂ) := by
  have h0 : algebraMap 𝒪[k] k u ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.val_injective (by simpa using h))
  rw [chk, dite_eq_right h0, show Units.mk0 _ h0 = unitIncl k u from Units.ext rfl]
  rfl

end UpperTheory.TNZ.Grp.P_lamBasic

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamBasic {n : ℕ} (G : Grp k n) : LambdaBasicProp G := by
  intro hb
  obtain ⟨-, hlt, hcond, hq⟩ := hb
  have hlev : 1 ≤ G.lev := by unfold lev; omega
  have key : ∀ g ∈ KC k n G.lev, G.lam g = 1 := by
    intro g hg
    unfold lam
    refine Finset.prod_eq_one fun a _ => ?_
    obtain ⟨u, hu, hu1⟩ := minor_unit hlev hg (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n)
      Subtype.val_injective
    have hΔ : G.Δ a g = algebraMap 𝒪[k] k u := hu
    rw [hΔ, chk_unit]
    unfold μnext
    split_ifs with h
    · have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h⟩ :=
        Ideal.pow_le_pow_right (hlt a _).le
      rw [hq a ⟨a + 1, h⟩ u (hle hu1)]
      rfl
    · rw [div_one]
      have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res (G.μ a)) :=
        Ideal.pow_le_pow_right (hcond a).le
      rw [triv_cond (G.μ a) (G.smooth a) u (hle hu1)]
      rfl
  have hone : (1 : GL (Fin n) k) ∈ KC k n G.lev := by
    refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
    simp [Matrix.one_apply]
  refine ⟨key 1 hone, fun g => ?_, key⟩
  unfold lam
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  unfold chk
  split_ifs
  · exact one_ne_zero
  · exact Units.ne_zero _

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowMono
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_PJ

variable {n : ℕ} (G : Grp k n)

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem KC_mono {a b : ℕ} (hab : a ≤ b) : KC k n b ⊆ KC k n a := fun _ hg =>
  ⟨hg.1, fun i j => inPow_mono hab (hg.2 i j)⟩

def Jsub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : Subgroup (GL (Fin n) k) where
  carrier := G.JSet
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

theorem Jg_sub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) {g : GL (Fin n) k} (hg : g ∈ G.Jg) : g ∈ G.JSet :=
  (Subgroup.closure_le (K := Jsub G h1 hmul hinv)).2 (fun _ hx => hx) hg

theorem Jg_le_KO (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : G.Jg ≤ KO k (Fin n) := fun _ hg =>
  (Jg_sub G h1 hmul hinv hg).1

theorem core (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    (hlM : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h)
    (hlB : G.lam 1 = 1 ∧ (∀ g, G.lam g ≠ 0) ∧ ∀ g ∈ KC k n G.lev, G.lam g = 1)
    (hKC : ∀ r : ℕ, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r) ∧
      (∀ g ∈ KO k (Fin n), ∀ u ∈ KC k n r, g * u * g⁻¹ ∈ KC k n r) ∧ IsOpen (KC k n r) ∧
        KC k n r ⊆ (KO k (Fin n) : Set _) ∧ (G.lev ≤ r → KC k n r ⊆ G.JSet))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) (hr : G.lev ≤ r) :
    Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
    ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
      G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
      (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v) := by
  obtain ⟨hKCeq, hKCn, hKCo, -, -⟩ := hKC r
  have hJ : ∀ {g : GL (Fin n) k}, g ∈ G.Jg → g ∈ G.JSet := fun hg => Jg_sub G h1 hmul hinv hg
  have hJK := Jg_le_KO G h1 hmul hinv
  have hKCmem : ∀ {u : GL (Fin n) k}, u ∈ KCg k n r → u ∈ KC k n r := fun hu => by
    rw [← hKCeq]; exact hu

  have hfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := by
    have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
    have : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 hc
    have ho : IsOpen (((KCg k n r).subgroupOf (KO k (Fin n)) : Subgroup (KO k (Fin n))) : Set (KO k (Fin n))) := by
      have : IsOpen (KCg k n r : Set (GL (Fin n) k)) := by rw [hKCeq]; exact hKCo
      exact this.preimage continuous_subtype_val
    have : Finite (KO k (Fin n) ⧸ (KCg k n r).subgroupOf (KO k (Fin n))) := Subgroup.quotient_finite_of_isOpen _ ho
    have h0 : (KCg k n r).relIndex (KO k (Fin n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h0' : (KCg k n r).relIndex G.Jg ≠ 0 := fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hJK h)
    have : ((KCg k n r).subgroupOf G.Jg).FiniteIndex := ⟨h0'⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  refine ⟨hfin, fun v hv => ?_⟩
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hN : ((KCg k n r).subgroupOf G.Jg).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.subset_closure (hKCn _ (hJK g.2) _ (hKCmem hh))⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ↥G.Jg → V, ∀ x, f x = (G.lam x)⁻¹ • π x v := ⟨_, fun _ => rfl⟩
  have hlamH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → G.lam h = 1 := fun h hh =>
    hlB.2.2 _ (KC_mono hr (hKCmem (Subgroup.mem_subgroupOf.1 hh)))
  have hπH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → π h v = v := fun h hh =>
    hv _ (hKCmem (Subgroup.mem_subgroupOf.1 hh))
  have hf : ∀ x y : ↥G.Jg, (x : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) = y → f x = f y := by
    intro x y hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ (KCg k n r).subgroupOf G.Jg, y = x * h :=
      ⟨x⁻¹ * y, QuotientGroup.eq.1 hxy, by group⟩
    rw [hfdef, hfdef, Subgroup.coe_mul, hlM _ (hJ x.2) _ (hJ h.2), hlamH h hh, mul_one, map_mul,
      Module.End.mul_apply, hπH h hh]
  have hPJ : ∀ w : V, G.PJ π r w = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
      (G.lam ((Quotient.out c : ↥G.Jg) : GL (Fin n) k))⁻¹ • π ((Quotient.out c : ↥G.Jg) : GL (Fin n) k) w :=
    fun w => finsum_eq_sum_of_fintype _
  have hPJv : G.PJ π r v = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg, f (Quotient.out c) := by
    rw [hPJ]; simp only [hfdef]
  have hA : ∀ g ∈ G.JSet, π g (G.PJ π r v) = G.lam g • G.PJ π r v := by
    intro g hg
    have hg0 := hlB.2.1 g
    have hterm : ∀ x : ↥G.Jg, π g (f x) = G.lam g • f (⟨g, Subgroup.subset_closure hg⟩ * x) := by
      intro x
      rw [hfdef, hfdef, Subgroup.coe_mul, Subgroup.coe_mk, hlM g hg _ (hJ x.2), map_smul, map_mul,
        Module.End.mul_apply, smul_smul]
      congr 1
      field_simp
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f (⟨g, Subgroup.subset_closure hg⟩ * Quotient.out c) =
          f (Quotient.out ((QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) * c)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPJv, map_sum, Finset.smul_sum]
    simp_rw [hterm, hmv]
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)) _ _ (fun c => rfl)
  refine ⟨fun g hg => hA g hg, fun j hj => ?_, fun hEv => ?_⟩
  · have hjinv := hinv j hj
    have h1' : G.lam j⁻¹ * G.lam j = 1 := by rw [← hlM _ hjinv _ hj, inv_mul_cancel, hlB.1]
    have hterm : ∀ x : ↥G.Jg, (G.lam x)⁻¹ • π x (π j v) =
        π j (f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro x
      have hx := hJ x.2
      have e : (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = j⁻¹ * x * j := rfl
      have hl : G.lam (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = G.lam x := by
        rw [e, hlM _ (hmul _ hjinv _ hx) _ hj, hlM _ hjinv _ hx]
        linear_combination G.lam x * h1'
      rw [hfdef, hl, map_smul, e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * Quotient.out c * ⟨j, Subgroup.subset_closure hj⟩) =
          f (Quotient.out ((QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹ * c *
            QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
    rw [hPJ (π j v)]
    simp_rw [hterm, hmv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← hA j hj, hPJv]
    congr 1
    exact Fintype.sum_equiv ((Equiv.mulLeft (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹).trans (Equiv.mulRight (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg))) _ _ (fun c => rfl)
  · have hfv : ∀ x : ↥G.Jg, f x = v := fun x => by
      rw [hfdef, hEv _ (hJ x.2), smul_smul, inv_mul_cancel₀ (hlB.2.1 _), one_smul]
    rw [hPJv]
    simp_rw [hfv]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

end P_PJ

theorem step_PJ {n : ℕ} (G : Grp k n) : ParabolicJacquetProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  exact P_PJ.core G hJone.1 (hJmul hcb hccB) (hJinv hcb hccB) (hlM hcb hΔU hΔM hccB) (hlB hccB) (hKC hccB)

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTzInj
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem KC_anti {n r r' : ℕ} (h : r ≤ r') : KC k n r' ⊆ KC k n r := by
  rintro g ⟨hg, hP⟩
  refine ⟨hg, fun i j => ?_⟩
  obtain ⟨y, hy, e⟩ := hP i j
  exact ⟨y, Ideal.pow_le_pow_right h hy, e⟩

theorem eq_zero_of_inPow {x : k} (hx : ∀ r, InPow r x) : x = 0 := by
  obtain ⟨y, -, rfl⟩ := hx 0
  have hy : ∀ r : ℕ, y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro r
    obtain ⟨z, hz, e⟩ := hx r
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  have hmem : y ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal 𝒪[k] ^ r := (Submodule.mem_iInf _).2 hy
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top] at hmem
  rw [(Ideal.mem_bot).1 hmem, map_zero]

theorem eq_one_of_KC {n : ℕ} {g : GL (Fin n) k} (hg : ∀ r, g ∈ KC k n r) : g = 1 := by
  ext i j
  have h := eq_zero_of_inPow (fun r => (hg r).2 i j)
  rw [sub_eq_zero] at h
  rw [h]
  simp [Matrix.one_apply]

theorem exists_KC_subset {n : ℕ} (hsub : ∀ r, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r))
    (hop : ∀ r, IsOpen (KC k n r)) (U : Set (GL (Fin n) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r, KC k n r ⊆ U := by
  have hcl : ∀ r, IsClosed (KC k n r) := by
    intro r
    have := Subgroup.isClosed_of_isOpen (KCg k n r) (by rw [hsub r]; exact hop r)
    rwa [hsub r] at this
  have hst : (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ r, (KC k n r ∩ Uᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg.2
    have h1' : g = 1 := eq_one_of_KC fun r => (hg' r).1
    exact (hg' 0).2 (h1' ▸ h1)
  have hdt : Directed (· ⊇ ·) (fun r => KC k n r ∩ Uᶜ) := by
    intro a b
    exact ⟨max a b, Set.inter_subset_inter_left _ (KC_anti (le_max_left a b)),
      Set.inter_subset_inter_left _ (KC_anti (le_max_right a b))⟩
  obtain ⟨r, hr⟩ := ((GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).elim_directed_family_closed
    (fun r => KC k n r ∩ Uᶜ) (fun r => (hcl r).inter hU.isClosed_compl) (Set.disjoint_iff_inter_eq_empty.2 hst) hdt).imp (fun _ => Disjoint.inter_eq)
  refine ⟨r, fun g hg => ?_⟩
  by_contra hgU
  have : g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) ∩ (KC k n r ∩ Uᶜ) := ⟨hg.1, hg, hgU⟩
  rw [hr] at this
  exact this

variable {n : ℕ} (G : Grp k n)

theorem conj_unip (ϖ : kˣ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ)⁻¹ * u * G.zEl ϖ ∈ unipRad k G.e := by
  have hz : G.zEl ϖ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) :=
    leviEmb_mem_normalizer k G.e _
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hz) u).1 hu
  simpa using this

theorem mem_zN (ϖ : kˣ) (u : ↥G.NO) :
    u ∈ G.zN ϖ 1 ↔ ∃ w ∈ G.NO, G.zEl ϖ * w * (G.zEl ϖ)⁻¹ = (u : GL (Fin n) k) := by
  simp [Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply]

theorem PJ_zero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) :
    G.PJ π r 0 = 0 := by
  simp [Grp.PJ]

end UpperTheory.TNZ.Grp.P_TzInj

namespace UpperTheory.TNZ.Grp

open P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_TzInj {n : ℕ} (G : Grp k n) : TorusCentreInjectiveProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V _ _ π hs x hx hT
  have h3 : ∀ a b c : GL (Fin n) k, ∀ v : V, π (a * b * c) v = π a (π b (π c v)) := fun a b c v => by
    rw [map_mul, map_mul]; rfl
  have hQfin : Finite (↥G.NO ⧸ G.zN ϖ 1) := (hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).1
  let _ : Fintype (↥G.NO ⧸ G.zN ϖ 1) := Fintype.ofFinite _

  have hsum : ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = 0 := by
    have e0 : π (G.zEl ϖ)⁻¹ (G.Tz π ϖ 1 x) = 0 := by rw [hT, map_zero]
    have e1 : G.Tz π ϖ 1 x = ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
        π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ 1) x) := by
      unfold Grp.Tz
      exact finsum_eq_sum_of_fintype _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum] at e0
    rw [← e0]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h3, pow_one]

  let U : Set (GL (Fin n) k) := {g | π g x = x} ∩ ⋂ c : ↥G.NO ⧸ G.zN ϖ 1,
    {g | π g (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x}
  have hUo : IsOpen U := (hs x).inter (isOpen_iInter_of_finite fun c => hs _)
  have hU1 : (1 : GL (Fin n) k) ∈ U := by
    refine ⟨by simp, Set.mem_iInter.2 fun c => ?_⟩
    simp
  obtain ⟨r0, hr0⟩ := exists_KC_subset (fun r => (hKC hccB r).1) (fun r => (hKC hccB r).2.2.1) U hUo hU1
  set r := max r0 G.lev with hr
  have hrl : G.lev ≤ r := le_max_right _ _
  have hKCr : KC k n r ⊆ U := (KC_anti (le_max_left _ _)).trans hr0
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC V π r hrl
  have hJfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := hPJ'.1
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hlin : ∀ f : ↥G.NO ⧸ G.zN ϖ 1 → V,
      G.PJ π r (∑ c, f c) = ∑ c, G.PJ π r (f c) := by
    intro f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Grp.PJ, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  have hsum' := congrArg (G.PJ π r) hsum
  rw [hlin, PJ_zero] at hsum'
  let c1 : ↥G.NO ⧸ G.zN ϖ 1 := QuotientGroup.mk (1 : ↥G.NO)
  rw [Finset.sum_eq_single c1] at hsum'
  ·
    have hu1 : (Quotient.out c1 : ↥G.NO) ∈ G.zN ϖ 1 := by
      have h : (QuotientGroup.mk (Quotient.out c1) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        Quotient.out_eq c1
      have := QuotientGroup.eq.1 h
      simpa using this
    obtain ⟨w, hw, hwe⟩ := (mem_zN G ϖ _).1 hu1
    have hyw : (G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ = w := by
      rw [← hwe]; group
    have hfix1 : π ((G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = x := by
      rw [hyw, hx w (hlU.1 w hw).1, (hlU.1 w hw).2, one_smul]
    rw [hfix1] at hsum'
    have hxfix : ∀ u ∈ KC k n r, π u x = x := fun u hu => (hKCr hu).1
    rw [(hPJ'.2 x hxfix).2.2 hx] at hsum'
    have hcard : (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (smul_eq_zero.1 hsum').resolve_left hcard
  ·
    intro c _ hc
    have hfix : ∀ u ∈ KC k n r, π u (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
        π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x :=
      fun u hu => Set.mem_iInter.1 (hKCr hu).2 c
    have hmem : ((Quotient.out c : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e ⊓ KO k (Fin n) := (Quotient.out c).2
    have hyU := conj_unip G ϖ (Subgroup.mem_inf.1 hmem).1
    have hyK : (G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ ∉ KO k (Fin n) := by
      intro hK
      apply hc
      have hin : (Quotient.out c : ↥G.NO) ∈ G.zN ϖ 1 := by
        refine (mem_zN G ϖ _).2 ⟨_, Subgroup.mem_inf.2 ⟨hyU, hK⟩, ?_⟩
        group
      have h : (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        QuotientGroup.eq.2 (by simpa using inv_mem hin)
      exact (Quotient.out_eq c).symm.trans h
    exact hkill hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC hPJ V π r hrl x hx _ hfix
      (hni hcb hccB _ hyU hyK)
  · intro h
    exact absurd (Finset.mem_univ c1) h

end UpperTheory.TNZ.Grp
end
end
