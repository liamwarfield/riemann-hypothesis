module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem isHomogeneous_multiset_prod_map {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hφ a).mul ih

theorem isHomogeneous_hsymm (N a : ℕ) : (hsymm (Fin N) ℤ a).IsHomogeneous a := by
  have h : ∀ t : Multiset (Fin N),
      ((t.map X).prod : MvPolynomial (Fin N) ℤ).IsHomogeneous (Multiset.card t) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (Fin N) ℤ
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact (isHomogeneous_X ℤ b).mul ih
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  simpa [s.2] using h s.1

theorem FlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hSeg : HsymmPairFlagIndependence.Statement) (hSym : SymmetricSpanHsymm.Statement) :
    FlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 m G hGm hGsym Gs Hs hGs hHs Q hQ
  classical

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x u i - Fin.append x' u' i)
      (Fin.append f f₂ i) (Fin.append g g₂ i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hF1.vertical i
    · simp only [Fin.append_right]
      exact hF2.vertical i
  have hind : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As Bs, A.IsHomogeneous m →
      IsPairExpansion m A As → IsPairExpansion m A Bs →
      pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) As Q =
        pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) Bs Q :=
    fun A As Bs hA h1 h2 => hExp O ϖ hϖ K ι _ d hV (N + N) _ _ _ _ hvert m A hA As Bs h1 h2 Q hQ

  let ex : MvPolynomial (Fin (N + N)) ℤ → Fin (N + N) → MvPolynomial (Fin (N + N) ⊕ Fin (N + N)) ℤ :=
    fun A => Classical.choose (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  have hex : ∀ A, IsPairExpansion m (homogeneousComponent m A) (ex A) :=
    fun A => Classical.choose_spec (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  let pn : MvPolynomial (Fin (N + N)) ℤ →+ ℤ := AddMonoidHom.mk'
    (fun A => pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
      (Fin.append g g₂) (ex A) Q)
    (by
      intro A B'
      have h2 : IsPairExpansion m (homogeneousComponent m (A + B')) (ex A + ex B') := by
        rw [map_add (f := _)]
        exact isPairExpansion_add (hex A) (hex B')
      rw [hind _ _ _ (homogeneousComponent_isHomogeneous m _) (hex (A + B')) h2]
      exact map_add (pairNumHom (pointIdeal O y) (Fin.append x u) (Fin.append x' u')
        (Fin.append f f₂) (Fin.append g g₂) Q) (ex A) (ex B'))
  have pn_eq : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As, A.IsHomogeneous m →
      IsPairExpansion m A As →
      pn A = pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
        (Fin.append g g₂) As Q := by
    intro A As hA h
    have h1 := hex A
    rw [homogeneousComponent_eq_self hA] at h1
    exact hind A _ _ hA h1 h

  have seg : ∀ (a r : ℕ) (R : MvPolynomial (Fin (N + N)) ℤ), R.IsHomogeneous r → a + r = m →
      pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R) =
        pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R) := by
    intro a r R hR har
    have hH : (hsymmTimes N (N + N) a R).IsHomogeneous (a + r) :=
      (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
    obtain ⟨As, hAs⟩ := exists_isPairExpansion hH
    have key := hSeg O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' v v' x x' u u' f g f₂ g₂ hF1 hF2
      (N + N) _ _ _ _ hvert a r R hR As As hAs hAs Q (by rw [har]; exact hQ)
    let σx : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.castAdd N) id
    let σu : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.natAdd N) id
    have cx : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σx = Fin.append a₁ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σx, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have cu : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σu = Fin.append a₂ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σu, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have rx : rename σx (hsymmTimes N (N + N) a R) =
        rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σx ∘ Fin.castAdd (N + N) = Fin.castAdd N := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_left]
      have e2 : σx ∘ Fin.natAdd N = id := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have ru : rename σu (hsymmTimes N (N + N) a R) =
        rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σu ∘ Fin.castAdd (N + N) = Fin.natAdd N := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_left]
      have e2 : σu ∘ Fin.natAdd N = id := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have hpx := isPairExpansion_push σx hAs
    have hpu := isPairExpansion_push σu hAs
    rw [rx, har] at hpx
    rw [ru, har] at hpu
    rw [pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpx,
      pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpu,
      pairNum_pushExpansion, pairNum_pushExpansion, cx, cx, cx, cx, cu, cu, cu, cu]
    exact key

  have hX : ∀ b, (rename (Fin.castAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have hU : ∀ b, (rename (Fin.natAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have tele : ∀ (t : Multiset ℕ) (s : ℕ) (S : MvPolynomial (Fin (N + N)) ℤ), S.IsHomogeneous s →
      s + t.sum = m →
      pn (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) =
        pn (S * (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intros; rfl
    | cons a t ih =>
      intro s S hS hst
      rw [Multiset.sum_cons] at hst
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hpX := isHomogeneous_multiset_prod_map _ hX t
      calc pn (S * (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod))
          = pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_left_comm]
        _ = pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) :=
            seg a (s + t.sum) _ (hS.mul hpX) (by omega)
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) := by
            congr 1
            ring
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) :=
            ih (s + a) _ (hS.mul (hU a)) (by omega)
        _ = pn (S * (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_assoc]

  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hSym N m G hGm hGsym)
  have hren : ∀ (φ : Fin N → Fin (N + N)), rename φ G =
      ∑ μ, c μ • (μ.parts.map fun b => rename φ (hsymm (Fin N) ℤ b)).prod := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_zsmul, hsymmPart, map_multiset_prod, Multiset.map_map]
    rfl
  have hLHS : pairNum (pointIdeal O y) x x' f g Gs Q = pn (rename (Fin.castAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.castAdd N) hGs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_left]
  have hRHS : pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q = pn (rename (Fin.natAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.natAdd N) hHs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_right]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hLHS, hRHS, hren, hren, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  have h := tele μ.parts 0 1 (isHomogeneous_one _ _) (by rw [μ.parts_sum, zero_add])
  simpa only [one_mul] using h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagBundleSectionForms

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ d k

theorem chartPow_add {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d d' : K → ℤ) :
    chartPow y c (d + d') = chartPow y c d * chartPow y c d' := by
  simp [chartPow, zpow_add₀ (hY _), Finset.prod_mul_distrib]

theorem chartPow_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hY : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℤ) :
    chartPow y c d ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k)

theorem chartPow_natCast (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (α : K → ℕ) :
    chartPow y c (fun k => (α k : ℤ)) = ∏ k, y ⟨k, c k⟩ ^ α k := by
  simp [chartPow]

theorem segreVec_pow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (n : ℕ) :
    segreVec y c ^ n = chartPow y c (fun _ => (n : ℤ)) := by
  simp [segreVec, chartPow, Finset.prod_pow]

section Dual

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_flag_dual (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hp : ∀ j, chartPow y c (b j) ≠ 0 := fun j => chartPow_ne_zero hY _
  have hgr : ∀ (j : Fin N) (s : Ω), (∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = s) ↔
      ∃ r ∈ chartRing F (segreVec y) c, s = r * chartPow y c (b j) := fun j s => by
    have h := hfl.graded c hc j
    rw [Set.ext_iff] at h
    exact h s
  have he : ∀ j : Fin N, ∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧
      w.repr v j = chartPow y c (b j) := fun j =>
    (hgr j _).2 ⟨1, one_mem _, (one_mul _).symm⟩
  choose e heL heT heD using he

  have hx : ∀ j : Fin N, e j - chartPow y c (b j) • w j ∈
      Submodule.span Ω (w '' {m | (m : ℕ) < j}) := by
    intro j
    rw [w.mem_span_image]
    intro m hm
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hm
    simp only [Set.mem_setOf_eq]
    by_contra hjm
    push_neg at hjm
    apply hm
    rcases hjm.lt_or_eq with h | h
    · have hne : j ≠ m := fun h' => (ne_of_lt h) (congrArg Fin.val h')
      simp [heT j m h, Finsupp.single_apply, hne]
    · have : m = j := Fin.ext h.symm
      subst this
      simp [heD]
  have hspan : ∀ m ≤ N, Submodule.span Ω (e '' {j | (j : ℕ) < m}) =
      Submodule.span Ω (w '' {j | (j : ℕ) < m}) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hS : {j : Fin N | (j : ℕ) < m + 1} = insert (⟨m, hm⟩ : Fin N) {j : Fin N | (j : ℕ) < m} := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hS, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert, Submodule.span_insert,
        ih (by omega)]
      have hxm := hx ⟨m, hm⟩
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.add_mem_sup
          (Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩)) (Submodule.mem_span_singleton_self (w ⟨m, hm⟩)))
          hxm
        simpa using this
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩))⁻¹ (Submodule.sub_mem_sup
          (Submodule.mem_span_singleton_self (e ⟨m, hm⟩)) hxm)
        simpa [smul_smul, inv_mul_cancel₀ (hp _)] using this
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    have h := hspan N le_rfl
    have hu : {j : Fin N | (j : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    rw [hu, Set.image_univ, Set.image_univ, w.span_eq] at h
    rw [h]
  have hli : LinearIndependent Ω e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by rw [Module.finrank_eq_card_basis w])
  let eb := Module.Basis.mk hli htop
  have heb : ⇑eb = e := funext (Module.Basis.mk_apply hli htop)
  have hvan : ∀ x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}), eb.repr x i = 0 := by
    intro x hx'
    rw [← hspan i i.isLt.le, ← heb, eb.mem_span_image] at hx'
    by_contra h
    exact lt_irrefl (i : ℕ) (hx' (Finsupp.mem_support_iff.2 h))
  have hself : ∀ j m, eb.repr (e j) m = Finsupp.single j 1 m := fun j m => by
    rw [← heb, eb.repr_self]
  have hint : ∀ m ≤ N, ∀ v ∈ B.lat c, (∀ j : Fin N, m ≤ (j : ℕ) → w.repr v j = 0) →
      ∀ j, eb.repr v j ∈ chartRing F (segreVec y) c := by
    intro m
    induction m with
    | zero =>
      intro _ v _ hv j
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ m ih =>
      intro hm v hvL hv j
      obtain ⟨r, hr, hrv⟩ := (hgr ⟨m, hm⟩ (w.repr v ⟨m, hm⟩)).1 ⟨v, hvL, fun j hj => hv j hj, rfl⟩
      have hv' : v - r • e ⟨m, hm⟩ ∈ B.lat c := sub_mem hvL (B.stable c r hr _ (heL _))
      have h' := ih (by omega) _ hv' (by
        intro j hj
        rcases hj.lt_or_eq with h | h
        · simp [hv j h, heT ⟨m, hm⟩ j h]
        · have : j = ⟨m, hm⟩ := Fin.ext h.symm
          subst this
          simp [heD, hrv])
      have hsplit : eb.repr v j = eb.repr (v - r • e ⟨m, hm⟩) j + r * eb.repr (e ⟨m, hm⟩) j := by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel]
      rw [hsplit, hself]
      refine add_mem (h' j) (mul_mem hr ?_)
      rw [Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine ⟨eb.coord i, fun v hv => ?_, fun j hj => ?_, ?_⟩
  · exact hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)) i
  · exact hvan _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · have hw : w i = (chartPow y c (b i))⁻¹ • (e i - (e i - chartPow y c (b i) • w i)) := by
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ (hp i), one_smul]
    rw [Module.Basis.coord_apply, hw, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
      hself, hvan _ (hx i)]
    simp

end Dual

section Forms

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def liftNat (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α

def chartMono (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k

theorem chartMono_homog (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMono (F := F) M c α) (liftNat α) := by
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k)
    (fun k => α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (α k))
  have hw : liftNat α = ∑ k, α k • blockWeight (bundleIdx ι M) ⟨some k, c k⟩ := by
    funext o
    cases o with
    | none => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
    | some k => simp [liftNat, blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [IsMultiHomog, chartMono, hw]
  exact h

theorem eval_chartMono (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (t : Fin N → Φ) (c : ∀ k, ι k) (α : K → ℕ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (chartMono M c α) =
      algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) := by
  simp [chartMono, eval₂_prod, eval₂_pow, eval₂_X, projCoord, map_prod]

theorem chartRing_forms (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {u : Ω}
    (hu : u ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx ι M) F), IsMultiHomog U (liftNat fun _ => n) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) U =
        algebraMap Ω Φ (u * segreVec y c ^ n) := by
  have hlift : ∀ n n' : ℕ, liftNat (K := K) (fun _ => n + n') = liftNat (fun _ => n) + liftNat (fun _ => n') := by
    intro n n'; funext o; cases o <;> simp [liftNat]
  have hQ : ∀ n : ℕ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t)
      (chartMono M c (fun _ => n)) = algebraMap Ω Φ (segreVec y c ^ n) := by
    intro n
    rw [eval_chartMono, segreVec, Finset.prod_pow]
  induction hu using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    refine ⟨1, chartMono M j (fun _ => 1), chartMono_homog M j _, ?_⟩
    rw [eval_chartMono, pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have h0 : liftNat (K := K) (fun _ => 0) = 0 := by funext o; cases o <;> rfl
      rw [h0]
      exact isWeightedHomogeneous_C _ _
    · simp
  | add z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * chartMono M c (fun _ => n') + U' * chartMono M c (fun _ => n), ?_, ?_⟩
    · rw [hlift]
      refine (hU.mul (chartMono_homog M c _)).add ?_
      rw [add_comm]
      exact hU'.mul (chartMono_homog M c _)
    · rw [eval₂_add, eval₂_mul, eval₂_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add (f := _)]
      congr 1
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * U', ?_, ?_⟩
    · rw [hlift]
      exact hU.mul hU'
    · rw [eval₂_mul, hUe, hUe', ← map_mul]
      congr 1
      ring

theorem eval_eq_zero_of_mem_projIdeal (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {f : MRing (bundleIdx ι M) F}
    (hf : f ∈ projIdeal F y w φ t) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) f = 0 := by
  have h : (MvPolynomial.eval (fun _ : Option K => (1 : Φ))).comp
      (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ t p) * X p.1)) =
      eval₂Hom ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp
  rw [projIdeal, RingHom.mem_ker] at hf
  rw [← coe_eval₂Hom, ← h, RingHom.comp_apply, hf, map_zero]

end Forms

end FlagBundleSectionForms

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleTrdegLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleTrdegLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω)
    (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ),
      Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤
        Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTruncSpecialize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TruncSpecialize.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ),
    AlgebraicIndependent Ω t → ∀ i : Fin N,
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ projIdeal F y w φ (truncCoord t i) ∧
      ∀ x z : MRing (bundleIdx ι M) F,
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) x =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) z →
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t i)) x = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleChartSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (i : Fin N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      ∃ (dl dm : Option K → ℕ) (l μ : MRing (bundleIdx ι M) F) (m : K → ℕ),
        μ = ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ m k ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaDeg + liftDeg (b i - a) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) l =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) μ ∧
        ∀ q ∈ projIdeal F y w φ (truncCoord t i), ∃ n : ℕ,
          (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n * q ∈
            projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpVerticalFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpVerticalFibre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ (a : Fin n → K → ℤ) (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * vNum W' (liftDegs a)
          else 0) =
        divCycle P x W * vNum W a

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleNeZeroFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem divCycle_ne_zero_facts {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h

theorem LeftTermSupport.proof : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : divCycle G s U ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualDisjoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ G'

def ResidualContraction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∀ x : MRing ι O, x ∉ P →
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm x) G' ≤
          divCycle P x (G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleCutProof

theorem intNumL_cons_eq_snoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type} [Field F] (P : Ideal (MRing ι F)) (x : K → ℤ)
    (L : List (K → ℤ)) :
    intNumL F P (x :: L) = intNum F P (Fin.snoc (α := fun _ => K → ℤ) L.get x) := by
  have hget : (x :: L).get = Fin.cons (α := fun _ => K → ℤ) x L.get := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have h := FieldNumbers.IntNumSymm.proof F K ι P (L.length + 1)
    (Fin.cons (α := fun _ => K → ℤ) x L.get) (finRotate _)
  rw [intNumL, hget, Fin.snoc_eq_cons_rotate, ← h]
  rfl

theorem cycEval_single {K : Type} {ι : K → Type} {F : Type} [Field F]
    (n : Ideal (MRing ι F) → ℤ) (Z : Ideal (MRing ι F)) :
    cycEval n (fun W => by classical exact if W = Z then 1 else 0) = n Z := by
  classical
  unfold cycEval
  rw [finsum_eq_single _ Z (fun W hW => by simp [hW])]
  simp

end FlagBundleCutProof


open FlagBundleCutProof in
theorem FlagBundleCut.proof (hDim : FlagBundleDim.Statement)
    (hForms : FlagBundleSectionForms.Statement) (hDiv : FlagBundleSectionDiv.Statement)
    (hCut : FieldNumbers.CutRational.Statement.{0}) : FlagBundleCut.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi L hL
  obtain ⟨bf, bg, f, g, hf, hg, hdeg, hfP, hgP, hval⟩ :=
    hForms F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i
  have hdiv := hDiv F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi bf bg f g hf hg hdeg hgP hval
  obtain ⟨hP, hrel⟩ :=
    hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) =
      ((L.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hrel]
    congr 2
    omega
  have h := hCut F (Option K) (bundleIdx ι M) _ hP L.length hrel' bf bg f g hf hg hfP hgP L.get
  rw [intNumL_cons_eq_snoc, ← hdeg, h, funext hdiv, intNumL]
  classical
  convert cycEval_single (fun W => intNum F W L.get) (projIdeal F y w φ (truncCoord t i))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelCommonModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E',
    ∃ (K'' : Type) (_ : Fintype K'') (ι'' : K'' → Type) (_ : ∀ k, Fintype (ι'' k))
      (z : (Σ k, ι'' k) → Ω)
      (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) N V)
      (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) =
                                IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O x ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E EB ∧ IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E' E'B ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B ∧
      (∀ (b : K → ℤ) (f g : MRing ι O),
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') b)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') f) (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') g)) ∧
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι'')) (I₁ : IFamily
          (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
        (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ → IsFieldIntersection I₂ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
        (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
          (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F₁.value O I₁ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₁.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₁.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₁.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₁.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) ∧
          F₂.value O I₂ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₂.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₂.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₂.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₂.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
