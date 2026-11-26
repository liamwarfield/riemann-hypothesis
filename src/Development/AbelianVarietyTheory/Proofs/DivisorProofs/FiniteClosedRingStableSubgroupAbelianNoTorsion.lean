module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_nsmul_sub_eff : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  intro R _ Y f _ H m s M hH hM hs
  have hD : (dual M).IsLB := isLB_dual hM
  obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero R Y f H m s (dual M) hH hD hs
  refine ⟨(max t₀ 0).toNat, ?_⟩
  have hc : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  obtain ⟨σ, i, hσ⟩ := ht _ hc
  have key := eff_of_sec _ (isLB_tw hD hH _) σ i hσ
  have e : cls (tw (dual M) H ((max t₀ 0).toNat : ℤ)) (isLB_tw hD hH _) =
      cls (dual M) hD - cls (pw H (-((max t₀ 0).toNat : ℤ))) (isLB_pw hH _) :=
    cls_div hD (isLB_pw hH _) (isLB_tw hD hH _)
  rw [e, cls_pw hH, cls_dual hM hD, neg_zsmul, natCast_zsmul] at key
  convert key using 1
  abel
end GlobalTheory.EffBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_veryAmple_sub_isEffectivePicClass : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  first | exact @GlobalTheory.EffBound.exists_nsmul_sub_eff | exact GlobalTheory.EffBound.exists_nsmul_sub_eff | (intros; apply GlobalTheory.EffBound.exists_nsmul_sub_eff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem pull_one (M : GlobalTheory.UU.CP B) : pull (1 : B ⟶ B).left (cls M.L.L M.L.isLB) = 0 := by
  have e : (1 : B ⟶ B).left = (toUnit B).left ≫ eSec B := by
    rw [Hom.one_def]; rfl
  rw [e, pull_comp, ← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
    (cls_eq_zero_iff (pull_isLB M.L.isLB _)).2 ⟨M.L.rig, M.L.rigGen⟩, map_zero]

theorem pull_inv (M : GlobalTheory.UU.CP B) (f : B ⟶ B) :
    pull (f⁻¹).left (cls M.L.L M.L.isLB) = pull f.left (cls M.L.L M.L.isLB) := by
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb M.L.isLB _ _)).2 ⟨M.sym, M.sym_gen⟩
  rw [cls_linComb M.L.isLB, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_zsmul,
    neg_one_zsmul] at h0
  have hι : pull (ι[B]).left (cls M.L.L M.L.isLB) = cls M.L.L M.L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact h0
  rw [Hom.inv_def, Over.comp_left, pull_comp, hι]

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_pow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℕ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
  have e : pull (𝟙 B ^ n).left (cls M.L.L M.L.isLB) = ((n : ℤ) ^ 2) • cls M.L.L M.L.isLB := by
    rw [← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
      ← (cls_eq_iff (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)).2 h, cls_pw]
  have e2 : f ^ n = f ≫ 𝟙 B ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [e2, Over.comp_left, pull_comp, e, map_zsmul]
  norm_cast

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem act_zsmul {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B) (a : O) (n : ℤ) :
    act.act (n • a) = act.act a ^ n := by
  have h0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, zpow_zero, h0]
  | succ k ih => rw [add_zsmul, one_zsmul, act.add, ih, zpow_add_one]
  | pred k ih =>
    rw [sub_zsmul, one_zsmul, zpow_sub_one, ← ih]
    refine eq_mul_inv_of_mul_eq ?_
    rw [← act.add]; congr 1; abel

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_zpow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℤ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n.natAbs ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, pull_pow, Int.natAbs_natCast]
  | negSucc m => rw [zpow_negSucc, pull_inv, pull_pow, Int.natAbs_negSucc]

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] (hE0 : Eff (0 : Pic X)) {x : Pic X} (hx : Eff x) :
    ∀ n : ℕ, Eff (n • x)
  | 0 => by rw [zero_smul]; exact hE0
  | n + 1 => by rw [succ_nsmul]; exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 hx n) hx

theorem eff_sum {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B)
    {X : Scheme.{0}} [IsIntegral X] (F : (B ⟶ B) → Pic X) (c0 : Pic X) (hE0 : Eff (0 : Pic X))
    (hc0 : Eff c0) (h1 : F 1 = 0) (hpar : ∀ f g, Eff (2 • F f + 2 • F g - F (f * g))) :
    ∀ (l : ℕ) (b : Fin l → O) (t : Fin l → ℕ), (∀ i, Eff (t i • c0 - F (act.act (b i)))) →
      Eff ((2 ^ l * ∑ i, t i) • c0 - F (act.act (∑ i, b i))) := by
  have h0 : act.act 0 = 1 := by rw [← zero_smul ℤ (0 : O), act_zsmul, zpow_zero]
  intro l
  induction l with
  | zero =>
    intro b t _
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, h0, h1, mul_zero, zero_smul, sub_zero]
    exact hE0
  | succ l ih =>
    intro b t ht
    rw [Fin.sum_univ_castSucc (f := b), Fin.sum_univ_castSucc (f := t), act.add]
    have hP := ih (fun i => b i.castSucc) (fun i => t i.castSucc) fun i => ht _
    set P := act.act (∑ i : Fin l, b i.castSucc)
    set g := act.act (b (Fin.last l))
    set T := ∑ i : Fin l, t i.castSucc
    set u := t (Fin.last l)
    have h2 : 2 ≤ 2 ^ (l + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 ^ (l + 1) * (T + u)) • c0 - F (P * g) =
        (2 • F P + 2 • F g - F (P * g)) + 2 • ((2 ^ l * T) • c0 - F P) + 2 • (u • c0 - F g) +
          ((2 ^ (l + 1) - 2) * u) • c0 := by
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub h2]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (hpar P g) (eff_nsmul hE0 hP 2)) (eff_nsmul hE0 (ht _) 2))
      (eff_nsmul hE0 hc0 _)

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem exists_effective_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (c : ℕ), H.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ 1 ≤ c ∧ ∀ (n : Fin d → ℤ) (K : ℕ), 1 ≤ K → (∀ i, (n i).natAbs ≤ K) → ∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left))) (j : (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left)).ι), σ.f j ≠ 0 := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k A hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec A)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps GlobalTheory.globalFns_holds _ A hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds k A hB hproj H hH) hsym
  have hL : M.L.L = H := by rw [hM]
  subst hL
  obtain ⟨c0, hc0⟩ : ∃ c0, cls M.L.L M.L.isLB = c0 := ⟨_, rfl⟩
  have hEF : ∀ φ : A ⟶ A, Eff (pull φ.left c0) := fun φ =>
    hc0 ▸ GlobalTheory.EffBound.eff_pull_of_veryAmpleBy k A.hom M.L.L m s M.L.isLB hs φ.left inferInstance
  have h1 : pull (1 : A ⟶ A).left c0 = 0 := hc0 ▸ pull_one A M
  have hE0 : Eff (0 : Pic A.left) := h1 ▸ hEF 1
  have hEc : Eff c0 := by
    have := hEF (𝟙 A)
    rwa [Over.id_left, pull_id] at this
  have hpar : ∀ f g : A ⟶ A, Eff (2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0) := by
    intro f g
    have e := GlobalTheory.CubeThm.cube_pic A M f g g⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, pull_one, pull_inv A M g, hc0] at e
    have e' : 2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0 = pull (f * g⁻¹).left c0 := by
      rw [← sub_eq_zero, ← sub_eq_zero.2 e]
      abel
    rw [e']
    exact hEF _
  have hc : ∀ i, ∃ ci : ℕ, Eff (ci • c0 - pull (act.act (a i)).left c0) := fun i => by
    let N := M.L.L.pull (act.act (a i)).left
    have hN : N.IsLB := pull_isLB M.L.isLB _
    have hD : (dual N).IsLB := isLB_dual hN
    obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero k A.left A.hom M.L.L m s (dual N) M.L.isLB hD hs
    have hc' : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
    obtain ⟨σ, j, hσ⟩ := ht _ hc'
    have h := eff_of_sec _ (isLB_tw hD M.L.isLB _) σ j hσ
    have e : cls (tw (dual N) M.L.L ((max t₀ 0).toNat : ℤ)) (isLB_tw hD M.L.isLB _) =
        cls (dual N) hD - cls (pw M.L.L (-((max t₀ 0).toNat : ℤ))) (isLB_pw M.L.isLB _) :=
      cls_div hD (isLB_pw M.L.isLB _) (isLB_tw hD M.L.isLB _)
    rw [e, cls_pw M.L.isLB, cls_dual hN hD, neg_zsmul, natCast_zsmul] at h
    have h' : Eff ((max t₀ 0).toNat • cls M.L.L M.L.isLB - cls N hN) := by
      convert h using 1 <;> abel
    change Eff ((max t₀ 0).toNat • cls M.L.L M.L.isLB - cls (M.L.L.pull (act.act (a i)).left) _) at h'
    rw [cls_pull M.L.isLB, hc0] at h'
    exact ⟨_, h'⟩
  choose ci hci using hc
  refine ⟨M.L.L, m, s, 2 ^ d * ∑ i, ci i + 1, M.L.isLB, hs, by omega, fun n K _ hn => ?_⟩
  have hterm : ∀ i, Eff ((K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0) := by
    intro i
    have hle : (n i).natAbs ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left (hn i) 2
    have e : (K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0 =
        (n i).natAbs ^ 2 • (ci i • c0 - pull (act.act (a i)).left c0) +
          ((K ^ 2 - (n i).natAbs ^ 2) * ci i) • c0 := by
      rw [act_zsmul, ← hc0, pull_zpow, hc0]
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub hle]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 (hci i) _) (eff_nsmul hE0 hEc _)
  have hsum := eff_sum act (fun φ => pull φ.left c0) c0 hE0 hEc h1 hpar d (fun i => n i • a i)
    (fun i => K ^ 2 * ci i) hterm
  refine GlobalTheory.T.exists_section_nonzero_chart_of_effective_class _ (LB.isLB_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)) ?_
  rw [cls_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _), cls_pw M.L.isLB, cls_pull M.L.isLB, hc0]
  have e : (((2 ^ d * ∑ i, ci i + 1) * K ^ 2 : ℕ) : ℤ) • c0 - pull (act.act (∑ i, n i • a i)).left c0 =
      ((2 ^ d * ∑ i, K ^ 2 * ci i) • c0 - pull (act.act (∑ i, n i • a i)).left c0) + (K ^ 2) • c0 := by
    simp only [← Finset.mul_sum, ← natCast_zsmul]
    push_cast
    module
  rw [e]
  exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ hsum (eff_nsmul hE0 hEc _)

end GlobalTheory.OEndDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullbackStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (c : ℕ), H.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ 1 ≤ c ∧ ∀ (n : Fin d → ℤ) (K : ℕ), 1 ≤ K → (∀ i, (n i).natAbs ≤ K) → ∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left))) (j : (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left)).ι), σ.f j ≠ 0 := by
  first | exact @GlobalTheory.OEndDegree.exists_effective_bound | exact GlobalTheory.OEndDegree.exists_effective_bound | (intros; apply GlobalTheory.OEndDegree.exists_effective_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem pull_pw_g (H : LB X) (φ : X ⟶ X) (t : ℤ) (j j' : PUnit.{1} → H.ι) :
    ((GlobalTheory.AbLaw.pw H t).pull φ).g j j' = ((H.pull φ).g j j') ^ t := by
  simp only [LB.pull, LB.LinComb, GlobalTheory.AbLaw.pw, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

abbrev E (H : LB X) (φ : X ⟶ X) (q : ℕ) : LB X := ReciprocityTheory.ChartRestriction.G.Semi.LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)

def loc (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) : Γ(X, (E H φ q).U p) :=
  σ.f p ^ t *
    rs X (le_inf le_top inf_le_right : (E H φ q).U p ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2)

theorem units_id {U₁ U₂ W : X.Opens} (q t : ℕ) (u : Γ(X, U₁)ˣ) (v w : Γ(X, U₂)ˣ) (hw : w = v ^ (t : ℤ))
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) :
    (res h₁ (u ^ (q : ℤ)) * (res h₂ v)⁻¹) ^ t * res h₂ w = res h₁ (u ^ ((q * t : ℕ) : ℤ)) := by
  subst hw
  simp only [map_zpow, ← zpow_natCast, mul_zpow, inv_zpow, ← zpow_mul, Nat.cast_mul]
  group

theorem loc_compat (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p p' : H.ι × (PUnit.{1} → H.ι)) :
    rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (loc H φ q t σ a p) =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (loc H φ q t σ a p') := by
  have e1 : rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (σ.f p) =
      ((E H φ q).g p p').val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p') := by
    have := GlobalTheory.LB.sec_rel σ p p' (W := (E H φ q).U p ⊓ (E H φ q).U p') inf_le_left inf_le_right le_rfl
    rw [this]
    congr 1
    exact rs_self _ _
  have e2 : rs X (le_inf le_top (inf_le_left.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2) =
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val *
      rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) :=
    GlobalTheory.LB.coord_rel a p.2 p'.2 _ _ _
  have key : ((E H φ q).g p p') ^ t *
      res (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2) =
      res (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        (H.g p.1 p'.1 ^ ((q * t : ℕ) : ℤ)) :=
    units_id q t (H.g p.1 p'.1) ((H.pull φ).g p.2 p'.2) _ (pull_pw_g H φ t p.2 p'.2) _ _
  have kv : ((E H φ q).g p p').val ^ t *
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val := by
    have := congrArg Units.val key
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  unfold loc
  simp only [map_mul, map_pow, rs_rs]
  rw [e1, e2, mul_pow]
  linear_combination (rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p')) ^ t *
    rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) * kv
end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem top_le_iSup_E {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q : ℕ) : (⊤ : X.Opens) ≤ ⨆ p, (E H φ q).U p := by
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : x ∈ (⊤ : X.Opens)))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : φ x ∈ (⊤ : X.Opens)))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, fun _ => j), hi, Set.mem_iInter.2 fun _ => hj⟩

theorem existsUnique_img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) :
    ∃! b : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤, ∀ p : H.ι × (PUnit.{1} → H.ι),
      rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord b p.1) = loc H φ q t σ a p :=
  SecOn.existsUnique_of_local (M := GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) (isLB_pw hH ((q * t : ℕ) : ℤ)) (fun p : H.ι × (PUnit.{1} → H.ι) => (E H φ q).U p) (fun _ => le_top)
    (top_le_iSup_E hH φ q) (fun p => p.1) (fun _ => inf_le_left) (loc H φ q t σ a)
    (fun p p' => loc_compat H φ q t σ a p p')

def img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ :=
  (existsUnique_img hH φ q t σ a).exists.choose

theorem img_spec {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) :
    rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord (img hH φ q t σ a) p.1) =
      loc H φ q t σ a p :=
  (existsUnique_img hH φ q t σ a).exists.choose_spec p

def imgLin {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q)) :
    SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤ →ₗ[Γ(X, ⊤)] SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ where
  toFun := img hH φ q t σ
  map_add' a b := by
    refine (existsUnique_img hH φ q t σ (a + b)).unique (img_spec hH φ q t σ (a + b)) fun p => ?_
    erw [GlobalTheory.LB.coord_add, map_add, img_spec, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_add, map_add]
    ring
  map_smul' r a := by
    refine (existsUnique_img hH φ q t σ (r • a)).unique (img_spec hH φ q t σ (r • a)) fun p => ?_
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs]
    simp only [RingHom.id_apply]
    ring

theorem imgLin_injective [IsIntegral X] {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0) : Function.Injective (imgLin hH φ q t σ) := by
  obtain ⟨p₀, hp₀⟩ := hσ
  have hne : Nonempty ((E H φ q).U p₀) := by
    by_contra hc
    have hb : (E H φ q).U p₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hc ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, (E H φ q).U p₀) := by rw [hb]; infer_instance
    exact hp₀ (Subsingleton.elim _ _)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h0 : loc H φ q t σ a p₀ = 0 := by
    rw [← img_spec hH φ q t σ a p₀]
    change rs X _ (GlobalTheory.LB.coord (imgLin hH φ q t σ a) p₀.1) = 0
    rw [ha]
    erw [GlobalTheory.LB.coord_zero, map_zero]
  unfold loc at h0
  have h1 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp₀)
  have hz := GlobalTheory.SecGrowth.sec_eq_zero (M := (GlobalTheory.AbLaw.pw H t).pull φ) (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ) a) (k₀ := p₀.2)
    (W := (E H φ q).U p₀) inf_le_right (by erw [SecOn.topEquiv_f, rs_rs]; exact h1)
  apply (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ)).injective
  rw [map_zero]
  exact GlobalTheory.LB.f_injective (funext hz)

end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp

theorem finite_finrank_pull_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X) (hφf : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q t : ℕ)
    (σ : LB.Sec (E H φ q)) (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0)
    (hfin : Module.Finite K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤)) :
    Module.Finite K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := by
  rw [hφf]
  have hinj : Function.Injective (SecOnR.lin f (imgLin hH φ q t σ)) := imgLin_injective hH φ q t σ hσ
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end GlobalTheory.DegCmp

namespace GlobalTheory


open GlobalTheory.DegCmp in
theorem degree_le_of_pull_le_pow : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  intro k _ X _ f g hg H m s hH hs
  obtain ⟨hfin, -, c, C₀, -, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k X f g hg H m s hH hs
  refine ⟨c * C₀ * 2 ^ g, fun φ _ _ hφf D q hq hD hσ => ?_⟩
  obtain ⟨σ, j, hj⟩ := hσ
  have hW : ∀ t : ℕ, Module.Finite k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := fun t =>
    finite_finrank_pull_le f φ hφf hH q t σ ⟨j, hj⟩ (hfin (q * t))
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich k X X f φ H m s hH hs D hD hfin fun t => (hW t).1
  have h1 := (hgrow (a + 1) (by omega)).1
  have h2 := (ha (a + 1)).1
  have h3 := (hW (a + 1 + a)).2
  have h4 := (hgrow (q * (a + 1 + a)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2
  have hpos : 0 < (a + 1) ^ g := by positivity
  have key : D * (a + 1) ^ g ≤ (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g :=
    calc D * (a + 1) ^ g ≤ D * (c * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) :=
          Nat.mul_le_mul_left _ h1
      _ = c * (D * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) := by ring
      _ ≤ c * (C₀ * (q * (a + 1 + a)) ^ g) := Nat.mul_le_mul_left _ (h2.trans (h3.trans h4))
      _ ≤ c * (C₀ * (q * (2 * (a + 1))) ^ g) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) g))
      _ = (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g := by rw [mul_pow, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtaleStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  first | exact @GlobalTheory.degree_le_of_pull_le_pow | exact GlobalTheory.degree_le_of_pull_le_pow | (intros; apply GlobalTheory.degree_le_of_pull_le_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePow
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OEndDegree

theorem card_ker_le : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  obtain ⟨H, m, s, c, hH, hs, hc, hsec⟩ := GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback E k A act g hB hg d a
  obtain ⟨C, hC⟩ := GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale k A.left A.hom g hg H m s hH hs
  refine ⟨C * c ^ g, fun n K hn hb => ?_⟩
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · exfalso; apply hb
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hn i
      rw [Nat.le_zero, Int.natAbs_eq_zero] at this
      rw [this, zero_smul]
    · exact h
  obtain ⟨hfin, het, hker⟩ := GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero E k A act g hB hg _ hb
  refine ⟨hker, ?_⟩
  have hrank := GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))
  have hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom := Over.w _
  have hq : 1 ≤ c * K ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h := hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)
  calc _ ≤ C * (c * K ^ 2) ^ g := h
    _ = C * c ^ g * K ^ (2 * g) := by ring

end GlobalTheory.OEndDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKerIntegralCombinationEndoLePowStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ker_integralCombination_endo_le_pow : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  first | exact @GlobalTheory.OEndDegree.card_ker_le | exact GlobalTheory.OEndDegree.card_ker_le | (intros; apply GlobalTheory.OEndDegree.card_ker_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsion
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NoPiTorsion

theorem exists_small_mem {R : Type} [CommRing R] (I : Ideal R) [Finite (R ⧸ I)] {d : ℕ} (a : Fin d → R)
    (ha : LinearIndependent ℤ a) (K : ℕ) (hK : Nat.card (R ⧸ I) < (K + 1) ^ d) :
    ∃ n : Fin d → ℤ, (∀ i, (n i).natAbs ≤ K) ∧ ∑ i, n i • a i ≠ 0 ∧ ∑ i, n i • a i ∈ I := by
  classical
  letI := Fintype.ofFinite (R ⧸ I)
  let f : (Fin d → Fin (K + 1)) → R ⧸ I := fun v => Ideal.Quotient.mk I (∑ i, ((v i : ℕ) : ℤ) • a i)
  obtain ⟨v, w, hvw, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [← Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; exact hK)
  refine ⟨fun i => ((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ), fun i => ?_, ?_, ?_⟩
  · show (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)).natAbs ≤ K
    have := (v i).isLt; have := (w i).isLt; omega
  · intro h0
    apply hvw
    funext i
    have := (Fintype.linearIndependent_iff.1 ha) _ h0 i
    exact Fin.ext (by omega)
  · have : ∑ i, (((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) • a i =
        ∑ i, ((v i : ℕ) : ℤ) • a i - ∑ i, ((w i : ℕ) : ℤ) • a i := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    rw [this]
    exact Ideal.Quotient.eq.1 hf

variable {E : Type} [Field E] [NumberField E] {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A]

theorem act_natCast (act : OAct (𝓞 E) A) (n : ℕ) : act.act (n : 𝓞 E) = 𝟙 A ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    first | exact left_eq_mul.1 h | exact self_eq_mul_right.1 h
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem comp_act_natCast (act : OAct (𝓞 E) A) (x : 𝟙_ (Over (Sp k)) ⟶ A) (n : ℕ) :
    x ≫ act.act (n : 𝓞 E) = x ^ n := by
  rw [act_natCast, MonObj.comp_pow, Category.comp_id]

theorem eq_one_of_comp_act_pow (act : OAct (𝓞 E) A) (π : 𝓞 E)
    (htor : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) (m : ℕ) :
    ∀ y : 𝟙_ (Over (Sp k)) ⟶ A, y ≫ act.act (π ^ m) = 1 → y = 1 := by
  induction m with
  | zero => intro y hy; rwa [pow_zero, act.one, Category.comp_id] at hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, act.mul, ← Category.assoc] at hy
    exact ih y (htor _ hy)

theorem comp_act_eq_one_of_pow_eq_one (act : OAct (𝓞 E) A) (π π' : 𝓞 E) (N m : ℕ)
    (hN : (N : 𝓞 E) = π * π') (htor : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ (N ^ m) = 1) (b : 𝓞 E) (hb : b ∈ Ideal.span {π' ^ m}) :
    x ≫ act.act b = 1 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have hy : x ≫ act.act (π' ^ m) = 1 := by
    refine eq_one_of_comp_act_pow act π htor m _ ?_
    rw [Category.assoc, ← act.mul, ← mul_pow, mul_comm π', ← hN, ← Nat.cast_pow, comp_act_natCast, hx]
  have := act.hom c
  rw [mul_comm, act.mul, ← Category.assoc, hy, MonObj.one_comp]

end GlobalTheory.NoPiTorsion

namespace GlobalTheory.NoPiTorsion

theorem finite_points : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (π : 𝓞 E) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → π ≠ 0 → ¬ IsUnit π → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro E _ _ k _ _ _ A _ act π g hA hg hπ0 hπu htor
  classical
  set N := (Algebra.norm ℤ π).natAbs with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, ← Ideal.absNorm_span_singleton]; intro h
    exact hπ0 (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have hN1 : N ≠ 1 := by
    rw [hNdef, ← Ideal.absNorm_span_singleton]; intro h
    exact hπu (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h))
  obtain ⟨π', hπ'⟩ : π ∣ (N : 𝓞 E) := by
    have := Ideal.absNorm_mem (Ideal.span {π})
    rwa [Ideal.absNorm_span_singleton, ← hNdef, Ideal.mem_span_singleton] at this
  let ιB := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let d := Fintype.card ιB
  let a : Fin d → 𝓞 E := fun i => RingOfIntegers.basis E ((Fintype.equivFin ιB).symm i)
  have ha : LinearIndependent ℤ a :=
    (RingOfIntegers.basis E).linearIndependent.comp _ (Fintype.equivFin ιB).symm.injective
  have hd : Module.finrank ℤ (𝓞 E) = d := Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)
  have hd0 : 0 < d := hd ▸ Module.finrank_pos
  set N' := (Algebra.norm ℤ π').natAbs with hN'def
  have hNN : N * N' = N ^ d := by
    have h := congrArg (fun z => (Algebra.norm ℤ z).natAbs) hπ'
    simp only [map_mul, Int.natAbs_mul] at h
    rw [← h]
    have : ((N : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hd, Int.natAbs_pow, Int.natAbs_natCast]
  have hN'0 : N' ≠ 0 := by
    intro h; rw [h, mul_zero] at hNN; exact hN0 (pow_eq_zero_iff hd0.ne' |>.1 hNN.symm)
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_ker_integralCombination_endo_le_pow E k A act g hA hg d a
  have key : ∀ t : ℕ, (N ^ t) ^ (2 * g) ≤ C := by
    intro t
    have hI : Nat.card (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) = N' ^ (d * t) := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, map_pow,
        Int.natAbs_pow]
    haveI : Finite (𝓞 E ⧸ Ideal.span {π' ^ (d * t)}) :=
      Nat.finite_of_card_ne_zero (by rw [hI]; exact pow_ne_zero _ hN'0)
    obtain ⟨n, hnK, hn0, hnI⟩ := exists_small_mem (Ideal.span {π' ^ (d * t)}) a ha (N' ^ t) (by
      rw [hI, mul_comm d t, pow_mul]; exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) hd0.ne')
    obtain ⟨hfin, hcard⟩ := hC n (N' ^ t) hnK hn0
    have hMk : ((N ^ (d * t) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)
    have htors := GlobalTheory.abMulN_holds k A g (N ^ (d * t)) hA hg hMk
    have hle : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ (N ^ (d * t)) = 1} ≤
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} :=
      Nat.card_le_card_of_injective
        (fun x => ⟨x.1, comp_act_eq_one_of_pow_eq_one act π π' N (d * t) hπ' htor x.1 x.2 _ hnI⟩)
        (by intro x y h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
    rw [htors] at hle
    have h1 := hle.trans hcard
    have hsplit : N ^ (d * t) = N ^ t * N' ^ t := by rw [pow_mul, ← hNN, mul_pow]
    rw [hsplit, mul_pow] at h1
    have hpos : 0 < (N' ^ t) ^ (2 * g) := by positivity
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hg0 : g = 0 := by
    by_contra hg0
    have h := key C
    have h2 : 2 ≤ N := by omega
    have h3 : C < 2 ^ C := Nat.lt_two_pow_self
    have h4 : 2 ^ C ≤ N ^ C := Nat.pow_le_pow_left h2 C
    have h5 : N ^ C ≤ (N ^ C) ^ (2 * g) := Nat.le_self_pow (by omega) _
    omega
  subst hg0
  have h2k : ((2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 two_ne_zero
  refine GlobalTheory.AbelianNoTorsion.finite_points_of_no_torsion k A hA 2 le_rfl h2k fun x hx => ?_
  have h2 := GlobalTheory.abMulN_holds k A 0 2 hA hg h2k
  rw [mul_zero, pow_zero] at h2
  have : Subsingleton {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1} := (Nat.card_eq_one_iff_unique.1 h2).1
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨x, hx⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ 2 = 1}) ⟨1, one_pow 2⟩)

end GlobalTheory.NoPiTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (π : 𝓞 E) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → π ≠ 0 → ¬ IsUnit π → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.NoPiTorsion.finite_points | exact GlobalTheory.NoPiTorsion.finite_points | (intros; apply GlobalTheory.NoPiTorsion.finite_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsion
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableAbelian

theorem restrict : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (B N : Over (Sp k)) [GrpObj B] [GrpObj N] (act : OAct O B) (ν : N ⟶ B), IsMonHom ν → IsClosedImmersion ν.left → IsReduced N.left → (∀ a : O, Set.range (ν ≫ act.act a).left ⊆ Set.range ν.left) → ∃ act' : OAct O N, ∀ a, act'.act a ≫ ν = ν ≫ act.act a := by
  intro k _ O _ B N _ _ act ν hν hνc hred h
  have : Mono ν := Over.mono_of_mono_left _
  have hl : ∀ a : O, ∃ l : N ⟶ N, l ≫ ν = ν ≫ act.act a := fun a => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (ν ≫ act.act a).left ν.left (h a)
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, Over.comp_left, Category.assoc, (act.act a).w, ν.w]
  choose l hl using hl
  have hm : ∀ a, IsMonHom (l a) := fun a => by
    have := act.hom a
    constructor
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hl]
  refine ⟨⟨l, hm, ?_, ?_, ?_⟩, hl⟩
  · rw [← cancel_mono ν, hl, act.one, Category.id_comp, Category.comp_id]
  · intro a b
    rw [← cancel_mono ν, hl, act.mul, Category.assoc, hl, reassoc_of% (hl a)]
  · intro a b
    rw [← cancel_mono ν, hl, act.add, MonObj.comp_mul, MonObj.mul_comp, hl, hl]

theorem range_comp_subset : ∀ (k : Type) [Field k] (N₀ N : Over (Sp k)) [GrpObj N₀] [GrpObj N] (ν₀ : N₀ ⟶ N) (f : N ⟶ N), IsMonHom ν₀ → IsMonHom f → IsOpenImmersion ν₀.left → IsClosedImmersion ν₀.left → ConnectedSpace N₀.left → Set.range (ν₀ ≫ f).left ⊆ Set.range ν₀.left := by
  intro k _ N₀ N _ _ ν₀ f hν₀ hf ho hc hconn
  haveI := ho
  haveI := hc
  have hcl : IsClopen (Set.range ν₀.left) :=
    ⟨ν₀.left.isClosedEmbedding.isClosed_range, ν₀.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (Set.range (ν₀ ≫ f).left) :=
    isPreconnected_range (ν₀ ≫ f).left.continuous
  let t : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have e2 : η[N₀] ≫ ν₀ ≫ f = η[N₀] ≫ ν₀ := by
    rw [IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have he : (η[N₀] ≫ ν₀ ≫ f).left t ∈ Set.range (ν₀ ≫ f).left ∩ Set.range ν₀.left := by
    refine ⟨⟨η[N₀].left t, rfl⟩, ?_⟩
    rw [e2]
    exact ⟨η[N₀].left t, rfl⟩
  exact hpre.subset_isClopen hcl ⟨_, he⟩

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ B _ act π hB hπ0 hπu C Z hZ hC hstab htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have : Mono ν := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := GlobalTheory.AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have hlift : ∀ x ∈ C, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x := fun x hx => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
      (hr ▸ (hC x).1 hx)
    exact ⟨Over.homMk l (by rw [← ν.w, ← Category.assoc, hl, x.w]), Over.OverMorphism.ext hl⟩
  have hNred : IsReduced N.left := isReduced_of_smooth N.hom
  obtain ⟨actN, hactN⟩ := restrict k (𝓞 E) B N act ν hν hνc hNred fun a => by
    rw [hr]
    refine GlobalTheory.ReducedSubgroup.range_subset_of_points (ν ≫ act.act a) hZ fun x => ?_
    rw [← Category.assoc, ← hC]
    exact hstab a _ (hmem x)
  have : Smooth N₀.hom := SmoothOfRelativeDimension.smooth g N₀.hom
  have hN₀red : IsReduced N₀.left := isReduced_of_smooth N₀.hom
  have hconn : ConnectedSpace N₀.left := GeometricallyConnected.connectedSpace_of_subsingleton N₀.hom
  obtain ⟨act₀, hact₀⟩ := restrict k (𝓞 E) N N₀ actN ν₀ hν₀ hν₀c hN₀red fun a =>
    range_comp_subset k N₀ N ν₀ (actN.act a) hν₀ (actN.hom a) hν₀o hν₀c hconn
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion E k N₀ act₀ π g hA hg hπ0 hπu fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      have e : (x ≫ ν₀ ≫ ν) ≫ act.act π = (x ≫ act₀.act π) ≫ ν₀ ≫ ν := by
        simp only [Category.assoc, ← hactN, reassoc_of% (hact₀ π)]
      rw [e, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := GlobalTheory.TorsionDense.finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hlift x hx
  exact ⟨y, Subtype.ext hy⟩

end GlobalTheory.OStableAbelian
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsionStatement
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | exact GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | (intros; apply GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion <;> assumption)
end
