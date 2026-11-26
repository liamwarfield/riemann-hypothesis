module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory

theorem addGroupFG_sec_of_isArithVar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  intro k _ X _ p D h B hB
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.Hom.appTop p).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have hf : ∀ r : k, algebraMap k Γ(X, ⊤) r =
      (Scheme.Hom.appTop p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := fun _ => rfl
  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hfin : Module.Finite k (coh (twist (QCoh.structureModule X) B) 0) :=
    finite_coh_twist_of_isProjOver hf (QCoh.structureModule X) h.isProjOver hB 0
  haveI : Module.Finite ℤ (coh (twist (QCoh.structureModule X) B) 0) := Module.Finite.trans k _
  have hfg : AddGroup.FG (coh (twist (QCoh.structureModule X) B) 0) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := (cohZeroTwistEquiv B).toAddEquiv.toAddMonoidHom)
    (cohZeroTwistEquiv B).toAddEquiv.surjective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  first | exact @GlobalTheory.addGroupFG_sec_of_isArithVar | exact GlobalTheory.addGroupFG_sec_of_isArithVar | (intros; apply GlobalTheory.addGroupFG_sec_of_isArithVar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.mp this
  apply (AddSubgroup.fg_iff _).mpr
  refine ⟨(φ : M.B.Sec → X.functionField) '' S, ?_, hfin.image φ⟩
  rw [← AddMonoidHom.map_closure, hS]

end GlobalTheory.HSNef.PairFG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairSections_fg_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  first | exact @GlobalTheory.HSNef.PairFG.h_fg | exact GlobalTheory.HSNef.PairFG.h_fg | (intros; apply GlobalTheory.HSNef.PairFG.h_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem exists_coeff_le_of_linearIndependent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  intro k _ X _ p D hX P a b r f hf hli
  classical
  have h1 : genericPoint X ∈ ⨆ i, P.L.B.U i := by rw [P.L.isLB.cover]; trivial
  have h2 : genericPoint X ∈ ⨆ j, P.A.B.U j := by rw [P.A.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := finiteType_int_of_isAffineOpen hX hU
  have hg : ∀ l, ∃ g, fnOf U hgU g = P.loc a b (f l) i j := fun l =>
    exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  choose g hg using hg
  set c0 : X.functionField := (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b with hc0def
  have hloc : ∀ h, P.loc a b h i j = h * c0 := fun h => by simp only [Pair.loc, c0, mul_assoc]
  have hc0 : c0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hlig : LinearIndependent ℤ g := by
    have h3 : LinearIndependent ℤ ((LinearMap.mulRight ℤ c0) ∘ f) :=
      hli.map' _ (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hc0))
    refine LinearIndependent.of_comp (fnOf U hgU).toAddMonoidHom.toIntLinearMap ?_
    have e : (⇑(fnOf U hgU).toAddMonoidHom.toIntLinearMap ∘ g) = ⇑(LinearMap.mulRight ℤ c0) ∘ f := by
      funext l
      simp [hg, hloc]
    rw [e]
    exact h3
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) r g hlig
  obtain ⟨-, -, -, hsurj, -⟩ := GlobalTheory.ContRead.exists_continuous_read k X p D hX U hU (fun _ _ => 0)
    fun _ => continuousOn_const
  choose σ y hy hyx using hsurj
  let M : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun s l => x s (g l)
  let w : Fin r → ℝ := fun s => Real.exp ((a * (P.L.φ (σ (x s))).φ i (y (x s)) +
    b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2)
  let E : ℝ := ∑ s, w s
  let K : ℝ := ∑ l, ∑ s, ‖M⁻¹ l s‖
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => norm_nonneg _
  refine ⟨K * E, mul_nonneg hK hE, fun cc R hR l => ?_⟩
  set v : Fin r → ℂ := Matrix.mulVec M fun l => (cc l : ℂ) with hvdef
  have hsum : P.loc a b (∑ l, cc l • f l) i j = fnOf U hgU (∑ l, cc l • g l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hloc, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hg, hloc, smul_mul_assoc]
  have key : ∀ s, ‖v s‖ ≤ R * w s := by
    intro s
    have e := GlobalTheory.VolBr.nu_eq k X p P a b _ hR.1 (σ (x s)) (y (x s)) i j
      (ptsIn_mono hl (hy (x s))) (ptsIn_mono hr (hy (x s)))
    rw [hsum, ratVal_fnOf (hy (x s)), ev_eq (hy (x s)), hyx] at e
    have hv : v s = x s (∑ l, cc l • g l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [v, M, Matrix.mulVec, dotProduct, map_sum, map_zsmul, mul_comm]
    have hb := hR.2 (σ (x s)) (y (x s))
    rw [e] at hb
    rw [hv]
    have hw : ‖x s (∑ l, cc l • g l)‖ = ‖x s (∑ l, cc l • g l)‖ *
        Real.exp (-(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2) * w s := by
      rw [mul_assoc, ← Real.exp_add]
      have : -(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 +
          (a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    rw [hw]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hR0 : 0 ≤ R := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos _ : (0 : ℝ) < w l)
    linarith [key l, norm_nonneg (v l)]
  have hinv : (fun l => (cc l : ℂ)) = Matrix.mulVec M⁻¹ v := by
    rw [hvdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), Matrix.one_mulVec]
  have habs : |(cc l : ℝ)| = ‖(cc l : ℂ)‖ := by simp
  rw [habs, congrFun hinv l]
  calc ‖Matrix.mulVec M⁻¹ v l‖ = ‖∑ s, M⁻¹ l s * v s‖ := rfl
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * ‖v s‖ := (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * (R * E) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((key s).trans (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := w) (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ s)) hR0)) (norm_nonneg _)
    _ = (∑ s, ‖M⁻¹ l s‖) * E * R := by rw [← Finset.sum_mul]; ring
    _ ≤ K * E * R := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE) hR0
        exact Finset.single_le_sum (f := fun l => ∑ s, ‖M⁻¹ l s‖)
          (fun t _ => Finset.sum_nonneg fun s _ => norm_nonneg _) (Finset.mem_univ l)

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  first | exact @GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | exact GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent | (intros; apply GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fg_addSubgroup_field_finite_or_basis {K : Type} [Field K] (H : AddSubgroup K) (hH : H.FG) :
    (H : Set K).Finite ∨ ∃ (r : ℕ) (f : Fin r → K), (∀ j, f j ∈ H) ∧ LinearIndependent ℤ f ∧
      ∀ x ∈ H, ∃ c : Fin r → ℤ, x = ∑ j, c j • f j := by
  have hfin : Module.Finite ℤ H :=
    Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg H).2 hH)
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
  · left
    have htor : Module.IsTorsion ℤ H := by
      intro x
      refine ⟨⟨(ringChar K : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq.ne_zero)⟩, ?_⟩
      ext
      simp [ringChar.Nat.cast_ringChar]
    have : Finite H := Module.finite_of_fg_torsion H htor
    exact Set.toFinite _
  · right
    haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    haveI : NoZeroSMulDivisors ℤ H := inferInstance
    haveI : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
    let bs := Module.finBasis ℤ H
    refine ⟨_, fun j => (bs j : K), fun j => (bs j).2, ?_, ?_⟩
    · exact bs.linearIndependent.map' H.subtype.toIntLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    · intro x hx
      refine ⟨bs.repr ⟨x, hx⟩, ?_⟩
      have h := congrArg Subtype.val (bs.sum_repr ⟨x, hx⟩)
      calc x = ((⟨x, hx⟩ : H) : K) := rfl
        _ = ((∑ i, bs.repr ⟨x, hx⟩ i • bs i : H) : K) := h.symm
        _ = ∑ j, bs.repr ⟨x, hx⟩ j • (bs j : K) := by
          change H.subtype (∑ i, bs.repr ⟨x, hx⟩ i • bs i) = _
          rw [map_sum]
          rfl

theorem bl_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  intro k _ X _ p D hX P a b R
  rcases fg_addSubgroup_field_finite_or_basis (P.H a b) (GlobalTheory.T.pairSections_fg_of_projArithVariety k X p D hX P a b) with
    hfin | ⟨r, f, hf, hli, hspan⟩
  · exact hfin.subset (fun x hx => hx.1)
  · obtain ⟨C, -, hC⟩ := GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections k X p D hX P a b r f hf hli
    have hS : {c : Fin r → ℤ | ∀ j, |(c j : ℝ)| ≤ C * R}.Finite := by
      refine (Set.Finite.pi (t := fun _ : Fin r => Set.Icc (-⌈C * R⌉) ⌈C * R⌉)
        (fun _ => Set.finite_Icc _ _)).subset ?_
      intro c hc j _
      have h := abs_le.1 (hc j)
      have hc1 := Int.le_ceil (C * R)
      have h1 : (c j : ℝ) ≤ (⌈C * R⌉ : ℝ) := h.2.trans hc1
      have h2 : -((⌈C * R⌉ : ℤ) : ℝ) ≤ c j := by linarith
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    refine (hS.image (fun c => ∑ j, c j • f j)).subset ?_
    intro x hx
    obtain ⟨c, rfl⟩ := hspan x hx.1
    exact ⟨c, fun j => hC c R hx j, rfl⟩

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_sectionBall_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  first | exact @GlobalTheory.HSNef.bl_finite | exact GlobalTheory.HSNef.bl_finite | (intros; apply GlobalTheory.HSNef.bl_finite <;> assumption)
end
