module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AHWeil

theorem eq_top_of_add_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ z : Fin g → ℂ, ∃ l : Λ, z - (l : Fin g → ℂ) ∈ W) : W = ⊤ := by
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hW : IsClosed (W : Set (Fin g → ℂ)) := W.closed_of_finiteDimensional
  obtain ⟨l, hl⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun l : Λ => (Homeomorph.subRight (l : Fin g → ℂ)) ⁻¹' (W : Set (Fin g → ℂ)))
    (fun l => hW.preimage (Homeomorph.continuous _))
    (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (h z))
  rw [← Homeomorph.preimage_interior] at hl
  obtain ⟨z, hz⟩ := hl
  exact W.eq_top_of_nonempty_interior' ⟨_, hz⟩

theorem dim_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g g' : ℕ} (u : HolUnif A L g) (u' : HolUnif A L g')
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem tangent_and_weil_of_isAH : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ g = P.g ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
  ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  intro hT P g u Hm χ hu
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  obtain rfl := dim_eq u u₀ F hF
  obtain ⟨⟨Ef, hEf, hB⟩, h1, h2⟩ := unimodular_and_tangent_of_isAH hT P rig hrig u Hm χ hu
  refine ⟨Ef, hEf, hB, rfl, h1, h2, fun k a b c hk hc => ?_⟩
  have ha := (UnifCompare.mem_iff u u₀ F hF a).2 a.2
  have hb := (UnifCompare.mem_iff u u₀ F hF b).2 b.2
  have e : Ef a b = E₀ ⟨F a, ha⟩ ⟨F b, hb⟩ := by
    have h := hE ⟨F a, ha⟩ ⟨F b, hb⟩
    rw [UnifCompare.hermForm_eq P.isLB u u₀ hu hu₀ F hF, ← hEf] at h
    exact_mod_cast h.symm
  have h := hW k ⟨F a, ha⟩ ⟨F b, hb⟩ c hk (e ▸ hc)
  rwa [← map_smul, ← map_smul, hF, hF] at h

end GlobalTheory.AHWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.appellHumbert_unif_tangent_weilPairing : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ g = P.g ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
  ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  first | exact @GlobalTheory.AHWeil.tangent_and_weil_of_isAH | exact GlobalTheory.AHWeil.tangent_and_weil_of_isAH | (intros; apply GlobalTheory.AHWeil.tangent_and_weil_of_isAH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

open GlobalTheory.PrimNorm

section Tensor

variable {X X' Y : Scheme.{0}}

theorem exists_gen_tensor {C A B : LB Y} (a : C.ι → A.ι) (b : C.ι → B.ι) (la : ∀ i, C.U i ≤ A.U (a i))
    (lb : ∀ i, C.U i ≤ B.U (b i))
    (hg : ∀ (y : Y) i j, y ∈ C.U i → y ∈ C.U j → gm (𝟙 Y) y (C.U i ⊓ C.U j) (C.g i j) =
      gm (𝟙 Y) y (A.U (a i) ⊓ A.U (a j)) (A.g (a i) (a j)) * gm (𝟙 Y) y (B.U (b i) ⊓ B.U (b j)) (B.g (b i) (b j)))
    (s : LB.Gen A) (hs : s.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ u : LB.Gen C, u.IsGen := by
  refine ⟨⟨fun i => res (la i) (s.s (a i)) * res (lb i) (t.s (b i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have ma : (𝟙 Y : Y ⟶ Y) y ∈ A.U (a i) ⊓ A.U (a j) := ⟨la i hy.1, la j hy.2⟩
  have mb : (𝟙 Y : Y ⟶ Y) y ∈ B.U (b i) ⊓ B.U (b j) := ⟨lb i hy.1, lb j hy.2⟩
  have ea := (gm_res _ y _ ma _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs (a i) (a j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ ma _))))
  have eb := (gm_res _ y _ mb _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht (b i) (b j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ mb _))))
  have v : ∀ i, y ∈ C.U i → gm (𝟙 Y) y (C.U i) (res (la i) (s.s (a i)) * res (lb i) (t.s (b i))) =
      gm (𝟙 Y) y (A.U (a i)) (s.s (a i)) * gm (𝟙 Y) y (B.U (b i)) (t.s (b i)) := fun i hi =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hi _) (gm_res _ y _ hi _))
  refine ((gm_res _ y _ hy _).trans ((v i hy.1).trans (congrArg₂ (· * ·) ea eb))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (v j hy.2)))).trans ?_
  exact mul_mul_mul_comm _ _ _ _

theorem lbIso_sum {L : LB X} {M : LB X'} {K K' J J' : Type} [Fintype K] [Fintype K'] [Fintype J] [Fintype J']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {ψ : J → (Y ⟶ X')} {δ : J → ℤ} {ψ' : J' → (Y ⟶ X')} {δ' : J' → ℤ}
    (h : LBIso (LB.LinComb L φ ε) (LB.LinComb M ψ δ)) (h' : LBIso (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ')) :
    LBIso (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ')) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  have l₁ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ (p.1 ∘ Sum.inl) ⊓ LB.wchart L φ (p.2 ∘ Sum.inl) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inl k)⟩
  have l₂ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ' (p.1 ∘ Sum.inr) ⊓ LB.wchart L φ' (p.2 ∘ Sum.inr) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inr k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inr k)⟩
  refine exists_gen_tensor (C := LB.div (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ'))
    (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε'))) (A := LB.div (LB.LinComb M ψ δ) (LB.LinComb L φ ε))
    (B := LB.div (LB.LinComb M ψ' δ') (LB.LinComb L φ' ε')) (fun p => (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
    (fun p => (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)) l₁ l₂ (fun y p q hp hq => ?_) w hw w' hw'
  refine ((gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
    (gm_linComb M _ _ (𝟙 Y) y p.1 q.1 hp.1 hq.1) (gm_linComb L _ _ (𝟙 Y) y p.2 q.2 hp.2 hq.2))).trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·)
    ((gm_div (LB.LinComb L φ ε) (LB.LinComb M ψ δ) (𝟙 Y) y (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl) (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl)
      ⟨l₁ p hp, l₁ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ δ (𝟙 Y) y _ _ (l₁ p hp).1 (l₁ q hq).1) (gm_linComb L φ ε (𝟙 Y) y _ _ (l₁ p hp).2 (l₁ q hq).2)))
    ((gm_div (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ') (𝟙 Y) y (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)
      (q.1 ∘ Sum.inr, q.2 ∘ Sum.inr) ⟨l₂ p hp, l₂ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ' δ' (𝟙 Y) y _ _ (l₂ p hp).1 (l₂ q hq).1)
      (gm_linComb L φ' ε' (𝟙 Y) y _ _ (l₂ p hp).2 (l₂ q hq).2)))).trans ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end Tensor

section Cube

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  {L : LB A.left} {M : LB B.left} {T : Over S}

omit [IsCommMonObj A] in
theorem cubeLB_isLB (hL : L.IsLB) {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB _ hL _ _

theorem class_cubeLB {U : Type*} [CommGroup U] (cl : LB T.left → U) (m : (T.left ⟶ A.left) → U)
    (h : ∀ (I : Type) [Fintype I] (φ : I → (T.left ⟶ A.left)) (ε : I → ℤ), cl (LB.LinComb L φ ε) = ∏ k, m (φ k) ^ ε k)
    (x y : T ⟶ A) :
    cl (cubeLB A ![x, y] L) = m (x * y).left * (m x.left)⁻¹ * (m y.left)⁻¹ * m (1 : T ⟶ A).left := by
  have e := congrArg (FreeGroup.lift m |> Abelianization.lift)
    (prod_square_id x y (fun q => Abelianization.of (FreeGroup.of q)))
  have hm (q : T.left ⟶ A.left) :
      (Abelianization.lift (FreeGroup.lift m)) (Abelianization.of (FreeGroup.of q)) = m q := by
    exact (Group.Abelianization.lift_apply_of _ _).trans FreeGroup.lift_apply_of
  simp only [diff₂, map_prod, map_zpow, map_mul, map_inv, hm] at e
  exact (h _ _ _).trans e

theorem lbIso_cubeLB_swap (hL : L.IsLB) (x y : T ⟶ A) : LBIso (cubeLB A ![x, y] L) (cubeLB A ![y, x] L) :=
  (lbIso_iff hL _ _ _ _).2 ((prod_square_id x y (cls L)).trans ((diff₂_comm _ _).trans
    (prod_square_id y x (cls L)).symm))

def cubeProd (L : LB A.left) (x y x' y' : T ⟶ A) : LB T.left :=
  LB.LinComb L (K := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)))
    (Sum.elim (fun I => (psum A ![x, y] I.down).left) (fun I => (psum A ![x', y'] I.down).left))
    (Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => (-1) ^ (2 - I.down.card)))

theorem lbIso_cubeLB_mul_left (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x x' y : T ⟶ A) :
    LBIso (cubeLB A ![x * x', y] L) (cubeProd L x y x' y) := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_left (diff₃_ptCls hL hT) x x' y).trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x' y (cls L)).symm)

theorem lbIso_cubeLB_mul_right (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x y y' : T ⟶ A) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeProd L x y x y') := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_right (diff₃_ptCls hL hT) x y y').trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x y' (cls L)).symm)

theorem lbIso_cubeLB_mul_left_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x x' y : T ⟶ A} {u u' v : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x', y] L) (cubeLB B ![u', v] M)) :
    LBIso (cubeLB A ![x * x', y] L) (cubeLB B ![u * u', v] M) :=
  have a : (cubeProd L x y x' y).IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u' v).IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_left hL hT x x' y)
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_left hM hT' u u' v).symm)

theorem lbIso_cubeLB_mul_right_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x y y' : T ⟶ A} {u v v' : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x, y'] L) (cubeLB B ![u, v'] M)) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeLB B ![u, v * v'] M) :=
  have a : (cubeProd L x y x y').IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u v').IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_right hL hT x y y')
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_right hM hT' u v v').symm)

theorem lbIso_cubeLB_hom (ψ : A ⟶ B) [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (x y : T ⟶ A) :
    LBIso (cubeLB A ![x, y] L) (cubeLB B ![x ≫ ψ, y ≫ ψ] M) := by
  obtain ⟨w, hw⟩ := h
  let ρ : (T ⟶ A) →* (T ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  refine (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullSame M _ _ _ (𝟙 _) fun I => ?_)
  have e : (fun i => ρ (![x, y] i)) = ![x ≫ ψ, y ≫ ψ] := funext fun i => by fin_cases i <;> rfl
  rw [Category.id_comp, ← e, ← psum_hom ρ]
  rfl

variable {X Y : Over S} {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}

theorem lbIso_of_lamEq (h : LamEq L f₁ f₂ M g₁ g₂) (x : T ⟶ X) (y : T ⟶ Y) :
    LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M) :=
  LBIso.chartPull (chartSquare L (lift x y) (by simp) (by simp)) (chartSquare M (lift x y) (by simp) (by simp)) h

end Cube

theorem lamEq_calculus : ∀ (S : Scheme.{0}) (X Y A B C : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C] (L : LB A.left) (M : LB B.left) (N : LB C.left), L.IsLB → M.IsLB → N.IsLB →
  ∀ (f₁ f₁' : X ⟶ A) (f₂ f₂' : Y ⟶ A) (g₁ g₁' : X ⟶ B) (g₂ g₂' : Y ⟶ B) (k₁ : X ⟶ C) (k₂ : Y ⟶ C),
  LamEq L f₁ f₂ L f₁ f₂ ∧ (LamEq L f₁ f₂ M g₁ g₂ → LamEq M g₁ g₂ L f₁ f₂ ∧ LamEq L f₂ f₁ M g₂ g₁ ∧ (LamEq M g₁ g₂ N k₁ k₂ → LamEq L f₁ f₂ N k₁ k₂) ∧
    (∀ (X' Y' : Over S) (a : X' ⟶ X) (b : Y' ⟶ Y), LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂)) ∧
    ∀ (T : Over S) (x : T ⟶ X) (y : T ⟶ Y), LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M)) ∧
  ((∃ t : LB.Gen (Theta A L), t.IsGen) → (∃ t : LB.Gen (Theta B M), t.IsGen) → LamEq L f₁ f₂ M g₁ g₂ → (LamEq L f₁' f₂ M g₁' g₂ → LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂) ∧ (LamEq L f₁ f₂' M g₁ g₂' → LamEq L f₁ (f₂ * f₂') M g₁ (g₂ * g₂'))) ∧
  ∀ ψ : A ⟶ B, IsMonHom ψ → LBIso L (M.pull ψ.left) → LamEq L f₁ f₂ M (f₁ ≫ ψ) (f₂ ≫ ψ) := by
  intro S X Y A B C _ _ _ _ _ _ L M N hL hM hN f₁ f₁' f₂ f₂' g₁ g₁' g₂ g₂' k₁ k₂
  refine ⟨(lbIso_iff hL _ _ _ _).2 rfl, fun h => ⟨LBIso.symm h, ?_, fun h' => ?_, fun X' Y' a b => ?_,
    fun T x y => lbIso_of_lamEq h x y⟩, fun hT hT' h => ⟨fun h' => ?_, fun h' => ?_⟩, fun ψ hψ h => ?_⟩
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hL _) (cubeLB_isLB hM _) (lbIso_cubeLB_swap hL _ _)
      (LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hM _)
        (lbIso_of_lamEq h (snd Y X) (fst Y X)) (lbIso_cubeLB_swap hM _ _))
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hN _) h h'
  · have e := lbIso_of_lamEq h (fst X' Y' ≫ a) (snd X' Y' ≫ b)
    simp only [Category.assoc] at e
    exact e
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_left_of hL hM hT hT' h h'
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_right_of hL hM hT hT' h h'
  · have e := lbIso_cubeLB_hom ψ h (fst X Y ≫ f₁) (snd X Y ≫ f₂)
    simp only [Category.assoc] at e
    exact e

end GlobalTheory.LamCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmGeneratorSqQuadraticEq
open NumberField

namespace GlobalTheory.CMGeneratorSquare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cm_generator_sq_quadratic_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  have hd : (H.d + 1) = 4 * ((H.d + 1) / 4) := by
    have := H.d_mod; omega
  have h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E)) := by
    have h2 := H.two_weight_eq_one_add_root
    have h3 := H.rt_sq
    have h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
      conv_lhs => rw [hd]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2 := by ring
    rw [h5, h2, mul_sub, ← h4]
    push_cast
    linear_combination h3 - 2 * h2
  have h4ne : (4 : 𝓞 E) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
  exact mul_left_cancel₀ h4ne h1

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E}, a ∈ GlobalTheory.CM.OK H →
    ∃ (u : ℤ) (v : ℤ), a = (↑u : NumberField.RingOfIntegers E) + (↑v : NumberField.RingOfIntegers E) *
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk
  have hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E) := by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination (v * v' : 𝓞 E) * hsq

end GlobalTheory.CMGeneratorSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CM

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem int_dvd_of_mul_eq_ringOfIntegers {N m : ℤ} {z : 𝓞 E} (h : (N : 𝓞 E) * z = m) : N ∣ m := by
  have h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m := ⟨z, by simpa using h.symm⟩
  have h2 := map_dvd (Algebra.norm ℤ) h1
  rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2

theorem int_dvd_of_sq_dvd_squarefree_mul_sq {d N v : ℤ} (hd : Squarefree d) (hN : N ≠ 0)
    (h : N ^ 2 ∣ d * v ^ 2) : N ∣ v := by
  obtain ⟨N', v', h1, h2, h3⟩ := extract_gcd N v
  generalize gcd N v = g at h1 h2
  subst h1 h2
  have hg : g ≠ 0 := left_ne_zero_of_mul hN
  have h4 : N' ^ 2 ∣ d * v' ^ 2 := by
    rw [mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h
  have hc : IsCoprime N' v' := (gcd_isUnit_iff _ _).1 h3
  have h5 : N' * N' ∣ d := by
    rw [← sq]
    exact (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4
  exact mul_dvd_mul_left g (hd _ h5).dvd

theorem cm_generator_sq_quadratic_eq (H : Host E) : H.w0 ^ 2 + (((1 + H.d) / 4 : ℕ) : 𝓞 E) = H.w0 := by
  have h4 : 4 * ((1 + H.d) / 4) = 1 + H.d := by have := H.d_mod; omega
  have h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4
  have h := H.rt_sq
  rw [rt_eq] at h
  apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
  linear_combination h + h5

theorem exists_coord (H : Host E) {a : 𝓞 E} (ha : a ∈ OK H) : ∃ u v : ℤ, a = u + v * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquare.main
  | exact _root_.GlobalTheory.CMGeneratorSquare.main
  | (apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquare.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquare.main ..)

theorem coord_eq_zero (H : Host E) {u v : ℤ} (h : (u : 𝓞 E) + v * H.w0 = 0) : u = 0 ∧ v = 0 := by
  have h1 := congrArg H.bar h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, map_zero] at h1
  have h2 : (v : 𝓞 E) * H.rt = 0 := by rw [rt_eq]; linear_combination h - h1
  have h3 : v = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)
  subst h3
  exact ⟨by simpa using h, rfl⟩

theorem coord_mem (H : Host E) (u v : ℤ) : (u : 𝓞 E) + v * H.w0 ∈ OK H :=
  add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

theorem coord_mul_bar (H : Host E) (u v : ℤ) : ((u : 𝓞 E) + v * H.w0) * H.bar (u + v * H.w0) =
    ((u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 : ℤ) : 𝓞 E) := by
  have h := cm_generator_sq_quadratic_eq H
  generalize (1 + H.d) / 4 = k at h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (-v ^ 2 : 𝓞 E) * h

theorem mem_OK_of_int_mul_mem (H : Host E) {N : ℤ} (hN : N ≠ 0) {y : 𝓞 E} (hy : (N : 𝓞 E) * y ∈ OK H) :
    y ∈ OK H := by
  obtain ⟨u, v, h⟩ := exists_coord H hy
  have hb := congrArg H.bar h
  have hn := coord_mul_bar H u v
  rw [← h, map_mul, map_intCast] at hn
  rw [map_mul, map_add (f := _), map_mul, map_intCast, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator] at hb
  have h1 : N ∣ 2 * u + v :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)
  have h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)
  have h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d := by have := H.d_mod; omega
  have h3 : N ^ 2 ∣ H.d * v ^ 2 := by
    have := dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)
    rwa [show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by
      linear_combination v ^ 2 * h4] at this
  obtain ⟨v', rfl⟩ := int_dvd_of_sq_dvd_squarefree_mul_sq
    (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3
  obtain ⟨u', rfl⟩ : N ∣ u :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)
  have : y = u' + v' * H.w0 :=
    mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)
  rw [this]
  exact coord_mem H u' v'

theorem finite_int_OK (H : Host E) : Module.Finite ℤ (OK H) :=
  Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective

theorem isIntegrallyClosed_OK (H : Host E) : IsIntegrallyClosed (OK H) := by
  have := finite_int_OK H
  rw [isIntegrallyClosed_iff (FractionRing (OK H))]
  intro x hx
  have hinj : Function.Injective (algebraMap (OK H) E) :=
    RingOfIntegers.coe_injective.comp Subtype.val_injective
  let φ : FractionRing (OK H) →ₐ[OK H] E :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj
  have hy : IsIntegral ℤ (φ x) := isIntegral_trans _ (hx.map φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OK H) x
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb
  have hb' : algebraMap (OK H) E b ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
  have hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H := by
    refine mem_OK_of_int_mul_mem H hn ?_
    convert (a * c).2 using 1
    apply RingOfIntegers.coe_injective
    have h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c := by
      rw [← map_mul, ← hc]; simp
    change (n : E) * φ _ = algebraMap (OK H) E (a * c)
    rw [map_div₀, φ.commutes, φ.commutes, h1, map_mul]
    field_simp
  refine ⟨⟨_, hm⟩, φ.injective ?_⟩
  exact φ.commutes _

theorem isDedekindDomain_OK (H : Host E) : IsDedekindDomain (OK H) :=
  have := finite_int_OK H
  { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)),
    Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }

theorem existsUnique_coord (H : Host E) (a : OK H) :
    ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  obtain ⟨u, v, h⟩ := exists_coord H a.2
  refine ⟨(u, v), Subtype.ext h, ?_⟩
  rintro ⟨u', v'⟩ h'
  have h2 : (a : 𝓞 E) = u' + v' * H.w0 := congrArg Subtype.val h'
  obtain ⟨h3, h4⟩ := coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)
  exact Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)

theorem finrank_int_OK (H : Host E) : Module.finrank ℤ (OK H) = 2 := by
  let f : (ℤ × ℤ) →ₗ[ℤ] OK H := LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
    (LinearMap.toSpanSingleton ℤ _ (wK H))
  have hf : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro a
    simpa [f, eq_comm (a := a)] using existsUnique_coord H a
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  simp

def barOK (H : Host E) : OK H ≃+* OK H where
  toFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  invFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  left_inv a := Subtype.ext (bar_bar H a)
  right_inv a := Subtype.ext (bar_bar H a)
  map_mul' a b := Subtype.ext (map_mul H.bar _ _)
  map_add' a b := Subtype.ext (map_add H.bar _ _)

theorem two_mul_finrank_OK (H : Host E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] :
    2 * Module.finrank (OK H) M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  have := finite_int_OK H
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  have : Module.Finite (OK H) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  rw [← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank,
    ← finrank_int_eq_mul_of_finite]

theorem OK_isDedekindDomain_and_projective :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  intro E _ _ _ H
  have h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E := by
    simpa using two_mul_finrank_OK H (𝓞 E)
  refine ⟨isDedekindDomain_OK H, existsUnique_coord H,
    ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩
  · change H.w0 + H.bar H.w0 = 1
    rw [cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  · intro M _ _ _ _
    have := finite_int_OK H
    have := isDedekindDomain_OK H
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
    have : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 E)
    refine ⟨Module.Finite.of_restrictScalars_finite ℤ _ _, Forms.projective_of_int _ _, ?_⟩
    have h3 := two_mul_finrank_OK H M
    rw [← h2, mul_assoc] at h3
    rw [← h2, Nat.mul_div_cancel_left _ two_pos]
    omega

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.integers_of_cm_field_conj_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  first | exact @GlobalTheory.CM.OK_isDedekindDomain_and_projective | exact GlobalTheory.CM.OK_isDedekindDomain_and_projective | (intros; apply GlobalTheory.CM.OK_isDedekindDomain_and_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_of_sabMap :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  intro E _ _ _ H S S' f T t' m
  have e : LBIso t'.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨h₁, h₂, h₃⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S' T.t.G t'.G f m.φ
    T.t.PP.L t'.PP.L T.t.PP.isLB t'.PP.isLB T.ab m.cart e
  have hs : Out.Sym t'.G t'.PP.L := by
    obtain ⟨-, w, hw, -⟩ := t'.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension T.g t'.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
  exact ⟨⟨⟨t', h₁, T.g, hd, hs, h₂ T.ample, h₃ T.ktriv⟩, rfl, rfl⟩, LBIso.symm e⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_of_cmTriple_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S) (t' : SAB H S') (m : SABMap t' T.t f), (∃ T' : PAT H S', T'.t = t' ∧ T'.g = T.g) ∧ LBIso (T.t.PP.L.pull m.φ) t'.PP.L := by
  first | exact @GlobalTheory.CM.PAT.exists_of_sabMap | exact GlobalTheory.CM.PAT.exists_of_sabMap | (intros; apply GlobalTheory.CM.PAT.exists_of_sabMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem polarised_of_grpObj (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) [GrpObj (schemeOver W)] (hc : IsCommMonObj (schemeOver W))
    (hη : η[schemeOver W].left = zero W) :
    IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
      (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
      Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
      Out.KTriv (schemeOver W) (originLB W) := by
  obtain ⟨hrig, hsym, hamp, hk⟩ := GlobalTheory.T.originLineBundle_polarisation R W hc hη
  exact ⟨isAbelianScheme_schemeOver R W hΔ hc, smoothOfRelativeDimension_toSpec_of_isUnit W hΔ,
    originLB_isLB W, hrig, hsym, hamp, hk⟩

theorem exists_grpObj_polarised (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
        (hT : IsUnimodularSol (W.map ρ) T),
        (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
          Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
        ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
          y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN) ∧
      (IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
        (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
        Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
        Out.KTriv (schemeOver W) (originLB W)) ∧
      ∃ v : epsR R ⟶ schemeOver W,
        (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
          v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
        IsLieBasis ![v] := by
  obtain ⟨inst, hc, hη, hadd, hneg⟩ := GlobalTheory.T.exists_commGrpObj_weierstrassScheme R W hΔ
  exact ⟨inst, hc, hη, hadd, hneg, polarised_of_grpObj R W hΔ hc hη,
    GlobalTheory.WeierstrassLie.isLieBasis_eps R W hη⟩

theorem exists_polAV : ∀ (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R), IsUnit W.Δ →
    ∃ (P : Out.PolAV (Sp R)) (ψ : P.A.left ⟶ scheme W) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsIso ψ ∧
      ψ ≫ toSpec W = P.A.hom ∧ eSec P.A ≫ ψ = zero W ∧
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W hΔ
  obtain ⟨inst, hc, hη, -, -, ⟨hab, hsm, hlb, hrig, hsym, hamp, hk⟩, v, ⟨h, hv⟩, hbasis⟩ :=
    exists_grpObj_polarised R W hΔ
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      grp := inst
      isAb := hab
      g := 1
      smoothDim := hsm
      L := originLB W
      isLB := hlb
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hk }
  refine ⟨P, 𝟙 _, v, rfl, inferInstance, ?_, ?_, ⟨h, ?_⟩, hbasis⟩
  · rw [Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact hη
  · rw [Category.comp_id]
    exact hv

end GlobalTheory.WeierstrassCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_of_obj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), ∃ T : PAT H S, T.t = o.t ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ o =>
    ⟨⟨o.t, ObjDim.isAbelianScheme o, _, ObjDim.smoothOfRelativeDimension o, ObjDim.sym, o.ample, o.ktriv⟩, rfl, rfl⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem lamBC_psum_hom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S}
    {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)

theorem lamBC_psum_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (I : Finset (Fin n)) :
    (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (lamBC_psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (lamBC_psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

theorem lamEq_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  intro S S' s X Y A B X' Y' A' B' _ _ _ _ x y a b hx hy hA hB L M L' M' hL hM hL' hM' iL iM
    f₁ f₂ g₁ g₂ f₁' f₂' g₁' g₂' e₁ e₂ e₃ e₄ H
  let p : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X := Over.homMk ((fst X' Y').left ≫ x) (by
    show ((fst X' Y').left ≫ x) ≫ X.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hx, ← Category.assoc, Over.w])
  let q : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ Y := Over.homMk ((snd X' Y').left ≫ y) (by
    show ((snd X' Y').left ≫ y) ≫ Y.hom = (X' ⊗ Y').hom ≫ s
    rw [Category.assoc, hy, ← Category.assoc, Over.w])
  let U : Over.mk ((X' ⊗ Y').hom ≫ s) ⟶ X ⊗ Y := lift p q
  have key : ∀ {C : Over S} {C' : Over S'} [GrpObj C] [GrpObj C'] {c : C'.left ⟶ C.left}
      (hC : IsGrpPullback C' C s c) (u : X ⟶ C) (v : Y ⟶ C) (u' : X' ⟶ C') (v' : Y' ⟶ C'),
      u'.left ≫ c = x ≫ u.left → v'.left ≫ c = y ≫ v.left → ∀ I : Finset (Fin 2),
      (psum C' ![fst X' Y' ≫ u', snd X' Y' ≫ v'] I).left ≫ c =
        U.left ≫ (psum C ![fst X Y ≫ u, snd X Y ≫ v] I).left := by
    intro C C' _ _ c hC u v u' v' hu hv I
    refine lamBC_psum_push hC _ _ U (fun i => ?_) I
    fin_cases i
    · show pushPt hC.1.w (fst X' Y' ≫ u') = lift p q ≫ fst X Y ≫ u
      rw [lift_fst_assoc]
      refine Over.OverMorphism.ext ?_
      show ((fst X' Y').left ≫ u'.left) ≫ c = ((fst X' Y').left ≫ x) ≫ u.left
      rw [Category.assoc, hu, Category.assoc]
    · show pushPt hC.1.w (snd X' Y' ≫ v') = lift p q ≫ snd X Y ≫ v
      rw [lift_snd_assoc]
      refine Over.OverMorphism.ext ?_
      show ((snd X' Y').left ≫ v'.left) ≫ c = ((snd X' Y').left ≫ y) ≫ v.left
      rw [Category.assoc, hv, Category.assoc]
  have H₁ : LBIso (cubeLB A' ![fst X' Y' ≫ f₁', snd X' Y' ≫ f₂'] (L.pull a))
      (cubeLB B' ![fst X' Y' ≫ g₁', snd X' Y' ≫ g₂'] (M.pull b)) :=
    LBIso.chartPull
      (chartPullLinComb L a _ _ _ U.left fun I => key hA f₁ f₂ f₁' f₂' e₁ e₂ I.down)
      (chartPullLinComb M b _ _ _ U.left fun I => key hB g₁ g₂ g₁' g₂' e₃ e₄ I.down) H
  have hLa : (L.pull a).IsLB := DVR.linComb_isLB _ hL _ _
  have hMb : (M.pull b).IsLB := DVR.linComb_isLB _ hM _ _
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hM' _ _)
    (PowPrimitive.lbIso_linComb iL.symm _ _)
    (LBIso.trans (DVR.linComb_isLB _ hLa _ _) (DVR.linComb_isLB _ hMb _ _) (DVR.linComb_isLB _ hM' _ _) H₁
      (PowPrimitive.lbIso_linComb iM _ _))

end GlobalTheory.CM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.isCubeLBPairingIso_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  first | exact @GlobalTheory.CM.lamEq_baseChange | exact GlobalTheory.CM.lamEq_baseChange | (intros; apply GlobalTheory.CM.lamEq_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem smoothOfRelativeDimension_of_fibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (β : R →+* K) (B : Over (Sp R)) [GrpObj B] (X' : Scheme.{0}) (π : X' ⟶ B.left) (p : X' ⟶ Sp K) (g : ℕ), IsAbelianScheme B → IsPullback π p B.hom (spMap β) → SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g B.hom := by
  intro R K _ _ _ β B _ X' π p g hB hP hg
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace (Sp R) := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected B.hom x
  have hn' : SmoothOfRelativeDimension n p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hP hn
  have hs : Surjective B.hom := inferInstance
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hP hs
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
  rw [← H1.dim_unique _ hn' hg y]
  exact hn

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem abelianScheme_hom_extends_dedekind_of_isGrpPullback :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (G₀ G₀' : Over (Sp K)) [GrpObj G₀] [GrpObj G₀'] (φ : G₀.left ⟶ G.left) (φ' : G₀'.left ⟶ G'.left), IsAbelianScheme G → IsAbelianScheme G' → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → IsGrpPullback G₀' G' (spMap (algebraMap R K)) φ' → ∀ f : G₀ ⟶ G₀', IsMonHom f → ∃ F : G ⟶ G', IsMonHom F ∧ f.left ≫ φ' = φ ≫ F.left ∧ ∀ F' : G ⟶ G', f.left ≫ φ' = φ ≫ F'.left → F' = F := by
  intro H R K _ _ _ _ _ G G' _ _ G₀ G₀' _ _ φ φ' hG hG' hφ hφ' f hf
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG'.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G _) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := abelianScheme_hom_extends_dedekind H R K G G' hG hG'
    (a.hom ≫ f ≫ b.hom) inferInstance
  have key : f.left ≫ φ' = φ ≫ F.left := by
    have h₁ := ExtUnique.pullback_map_left_fst (spMap (algebraMap R K)) F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  exact ⟨F, hF, key, fun F' h' => ExtUnique.over_hom_ext_of_isPullback (j := spMap (algebraMap R K)) hφ.1 (h'.symm.trans key)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAlStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.abelianScheme_hom_extends_dedekind_of_isGrpPullback_alt : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (G₀ G₀' : Over (Sp K)) [GrpObj G₀] [GrpObj G₀'] (φ : G₀.left ⟶ G.left) (φ' : G₀'.left ⟶ G'.left), IsAbelianScheme G → IsAbelianScheme G' → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → IsGrpPullback G₀' G' (spMap (algebraMap R K)) φ' → ∀ f : G₀ ⟶ G₀', IsMonHom f → ∃ F : G ⟶ G', IsMonHom F ∧ f.left ≫ φ' = φ ≫ F.left ∧ ∀ F' : G ⟶ G', f.left ≫ φ' = φ ≫ F'.left → F' = F := by
  first | exact @GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback | exact GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback | (intros; apply GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPicardGroup
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CechPicMul


open Classical in
def cl {X : Scheme.{0}} (L : LB X) : Multiplicative (CechPic.Pic X) :=
  if h : L.IsLB then Multiplicative.ofAdd (CechPic.cls L h) else 1

theorem cl_eq {X : Scheme.{0}} {L : LB X} (h : L.IsLB) : cl L = Multiplicative.ofAdd (CechPic.cls L h) := dif_pos h

theorem exists_picardGroup : ∃ (Pic : Scheme.{0} → Type 1) (_ : ∀ X, CommGroup (Pic X)) (cl : ∀ {X : Scheme.{0}}, LB X → Pic X) (pl : ∀ {X Y : Scheme.{0}}, (Y ⟶ X) → (Pic X →* Pic Y)),
  (∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (cl L = cl M ↔ LBIso L M)) ∧ (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → (cl L = 1 ↔ ∃ t : LB.Gen L, t.IsGen)) ∧
  (∀ (X : Scheme.{0}) (c : Pic X), pl (𝟙 X) c = c) ∧ (∀ (X Y Z : Scheme.{0}) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Pic X), pl (g ≫ f) c = pl g (pl f c)) ∧
  (∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ), (LB.LinComb L φ ε).IsLB ∧ cl (LB.LinComb L φ ε) = ∏ k, pl (φ k) (cl L) ^ ε k) ∧
  ∀ (X : Scheme.{0}) (L M : LB X), L.IsLB → M.IsLB → (LB.div M L).IsLB ∧ cl (LB.div M L) = cl M / cl L := by
  refine ⟨fun X => Multiplicative (CechPic.Pic X), fun X => inferInstance, cl,
    fun f => AddMonoidHom.toMultiplicative (CechPic.pull f), fun X L M hL hM => ?_, fun X L hL => ?_,
    fun X c => CechPic.pull_id c.toAdd, fun X Y Z f g c => CechPic.pull_comp g f c.toAdd,
    fun X Y L hL I _ φ ε => ⟨LB.isLB_linComb hL φ ε, ?_⟩, fun X L M hL hM => ⟨LB.isLB_div hM hL, ?_⟩⟩
  · beta_reduce
    rw [cl_eq hL, cl_eq hM]
    exact CechPic.cls_eq_iff hL hM
  · beta_reduce
    rw [cl_eq hL]
    exact CechPic.cls_eq_zero_iff hL
  · beta_reduce
    rw [cl_eq (LB.isLB_linComb hL φ ε), cl_eq hL, CechPic.cls_linComb hL, ofAdd_sum]
    rfl
  · beta_reduce
    rw [cl_eq (LB.isLB_div hM hL), cl_eq hL, cl_eq hM, CechPic.cls_div hM hL]
    rfl

end GlobalTheory.CechPicMul
end
end
