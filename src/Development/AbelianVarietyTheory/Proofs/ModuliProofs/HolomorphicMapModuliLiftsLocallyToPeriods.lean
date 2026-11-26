module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolLinearLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem exists_hol_linear_lift {B : Set (Fin m → ℂ)} (hB : IsOpen B) {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (f : G ⟶ G) [IsMonHom f] :
    ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ b ∈ B, ∀ z, e b (L b z) = e b z ≫ f) ∧
      ∀ z, DifferentiableOn ℂ (fun b => L b z) B := by
  have key : ∀ b₁ ∈ B, ∃ L : (Fin m → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ᶠ b in 𝓝 b₁, ∀ z, e b (L b z) = e b z ≫ f) ∧ ∀ z, DifferentiableAt ℂ (fun b => L b z) b₁ := by
    intro b₁ hb₁
    obtain ⟨ζ, -, h2, h3⟩ := hl.lift (W := B ×ˢ Set.univ) (β := Prod.fst)
      (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2 ≫ f) (w₀ := (b₁, 0)) (z₀ := 0)
      (hB.prod isOpen_univ) ⟨hb₁, trivial⟩ differentiableOn_fst (fun _ h => h.1) (isHolTo_comp_hom hol f.left)
      (by simp only [hom_zero (he b₁ hb₁).1.1, MonObj.one_comp])
    refine ⟨fun b => ((fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ _ _)).toLinearMap, ?_, fun z => ?_⟩
    · have ht : Tendsto (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (𝓝 b₁) (𝓝 (b₁, 0)) :=
        (Continuous.prodMk_left _).tendsto _
      filter_upwards [hB.mem_nhds hb₁, ht.eventually h2.eventually_analyticAt, ht.eventually h3.eventually_nhds]
        with b hb ha hz z
      have hd := ha.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right b (0 : Fin g → ℂ))
      have := fderiv_lift (x := fun z => e b z ≫ f) (fun z w => by simp only [(he b hb).1.1, MonObj.mul_comp])
        (he b hb).1.1 (he b hb).1.2.1 hr (he b hb).2 hd.differentiableAt
        (((Continuous.prodMk_right b).tendsto 0).eventually hz) z
      rwa [hd.fderiv] at this
    · have : DifferentiableAt ℂ (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0) ((0 : Fin m → ℂ), z)) b₁ :=
        (h2.fderiv.differentiableAt.comp b₁ (hasFDerivAt_prodMk_left b₁ (0 : Fin g → ℂ)).differentiableAt).clm_apply
          (differentiableAt_const ((0 : Fin m → ℂ), z))
      exact this
  choose! L h1 h2 using key
  refine ⟨fun b => L b b, fun b hb => (h1 b hb).self_of_nhds, fun z b₁ hb₁ => ?_⟩
  refine ((h2 b₁ hb₁ z).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hB.mem_nhds hb₁, h1 b₁ hb₁] with b hb h
  rw [linear_lift_unique (he b hb).1.1 hr (he b hb).2 (L := L b b) (L' := L b₁ b)
    fun z => ((h1 b hb).self_of_nhds z).trans (h z).symm]

theorem exists_hol_rep {O : Type} [CommRing O] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (act : OAct O G) :
    ∃ F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ),
      (∀ b ∈ B, ∀ a z, e b ((F b a).mulVec z) = e b z ≫ act.act a) ∧
      ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B := by
  classical
  choose L h1 h2 using fun a => haveI := act.hom a; exists_hol_linear_lift hB hr hol he hl (act.act a)
  have key : ∀ b ∈ B, ∃ F : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a, F a = LinearMap.toMatrix' (L a b) := by
    intro b hb
    have u := fun L L' => linear_lift_unique (he b hb).1.1 hr (he b hb).2 (V := Fin g → ℂ) (L := L) (L' := L')
    refine ⟨RingHom.mk' ⟨⟨fun a => LinearMap.toMatrix' (L a b), ?_⟩, fun a a' => ?_⟩ fun a a' => ?_, fun _ => rfl⟩
    · rw [u (L 1 b) LinearMap.id fun z => by rw [h1 1 b hb, act.one, Category.comp_id, LinearMap.id_apply],
        LinearMap.toMatrix'_id]
    · change LinearMap.toMatrix' (L (a * a') b) = _
      rw [u (L (a * a') b) (L a b ∘ₗ L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.comp_apply, h1 _ b hb, h1 _ b hb, mul_comm, act.mul, Category.assoc],
        LinearMap.toMatrix'_comp]
    · change LinearMap.toMatrix' (L (a + a') b) = LinearMap.toMatrix' (L a b) + LinearMap.toMatrix' (L a' b)
      rw [u (L (a + a') b) (L a b + L a' b) fun z => by
        rw [h1 _ b hb, LinearMap.add_apply, (he b hb).1.1, h1 _ b hb, h1 _ b hb, act.add, MonObj.comp_mul], map_add (f := _)]
  choose F hF using key
  refine ⟨fun b => if hb : b ∈ B then F b hb else F b₀ hb₀, fun b hb a z => ?_, fun a i j => ?_⟩
  · simp only [dif_pos hb, hF, LinearMap.toMatrix'_mulVec, h1 a b hb]
  · refine (differentiableOn_pi.1 (h2 a (Pi.single j 1)) i).congr fun b hb => ?_
    simp only [dif_pos hb, hF, LinearMap.toMatrix'_apply]

def HasForm {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) : Prop :=
  ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y

open Matrix in
theorem HasForm.of_comp {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {P : La → (Fin g → ℂ)} {g' : ℕ}
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hL : Function.Injective L) (h : HasForm EF (fun x => L (P x))) :
    HasForm EF P := by
  obtain ⟨Hm, h1, h2, h3⟩ := h
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h1, fun z hz => ?_, fun x y => ?_⟩
  · rw [key]
    exact h2 _ fun h0 => hz (hL (h0.trans (map_zero L).symm))
  · rw [key, h3]

theorem int_eq_of_exp {a b : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (a : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (b : ℂ) / k)) : a = b := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ b - a := fun k hk => by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp := Complex.two_pi_I_ne_zero
    refine ⟨n, ?_⟩
    have : ((b : ℂ) - a) = k * n := by
      refine mul_left_cancel₀ hp ?_
      field_simp at hn
      linear_combination (2 * Real.pi * Complex.I) * hn
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((b - a).natAbs + 1) (Nat.succ_pos _)) (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem hasForm_of_weil (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt)
    (A : Out.PolAV X) (y₀ y : Sp ℂ ⟶ X) (hy : y = (𝟙_ (Over (Sp ℂ))).hom ≫ y₀)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ A.A)} (he : IsExp y e) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0)
    (hl : ∀ (n : ℕ) (x : (Fin n → ℂ) → (Over.mk y ⟶ A.A)), IsHolTo Set.univ (fun w => (x w).left) → e 0 = x 0 →
      ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), AnalyticAt ℂ ζ 0 ∧ ∀ᶠ w in 𝓝 0, e (ζ w) = x w)
    {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (P : La → (Fin g → ℂ)) (hP : ∀ a, e (P a) = 1)
    (hw : ∀ (k : ℕ) (a a₂ : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a a₂ : ℂ) / k) →
      Out.WeilIs A.A A.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) : HasForm EF P := by
  subst hy
  obtain ⟨A', φ, hφ, -, hm, t, ht⟩ := hB _ _ y₀ A
  have hgp : IsGrpPullback A'.A A.A y₀ φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨rig, hrig⟩ := A'.rigid
  obtain ⟨u, Hm, χ, Ef, ⟨h1, h2, -⟩, -, -, -, -, -, h3, -, h4⟩ := hT A' rig hrig
  let x : (Fin A'.g → ℂ) → (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y₀) ⟶ A.A) := fun w => Out.toBase hφ.w (u.ex w)
  have hx : ∀ z w, x (z + w) = x z * x w := fun z w => by simp only [x, u.ex_add, hm]
  have hinj : Function.Injective (fun p : 𝟙_ (Over (Sp ℂ)) ⟶ A'.A => Out.toBase hφ.w p) := fun p q h =>
    Over.OverMorphism.ext (hφ.hom_ext (congrArg (fun s => s.left) h) ((Over.w p).trans (Over.w q).symm))
  have hker : ∀ z, x z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [← u.ker, ← hom_zero hx, ← hom_zero u.ex_add]
    exact hinj.eq_iff
  have hsx : Function.Surjective x := fun q => by
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk (hφ.lift q.left (𝟙_ (Over (Sp ℂ))).hom (Over.w q)) (hφ.lift_snd _ _ _))
    refine ⟨w, Over.OverMorphism.ext ?_⟩
    change (u.ex w).left ≫ φ = _
    rw [hw]
    exact hφ.lift_fst _ _ _
  have hhol : IsHolTo Set.univ (fun w => (u.ex w).left) := fun U f => by simpa using u.hol U f
  obtain ⟨ζ, hζ, hζ'⟩ := hl _ x (isHolTo_comp_hom hhol φ) (by rw [hom_zero hx, hom_zero he.1])
  obtain ⟨L, hL⟩ := exists_linearEquiv_lift hx he.1 hsx he.2.1 (by
    haveI := u.discrete
    rw [show {z | x z = 1} = (u.Λ : Set _) from Set.ext hker]
    exact DiscreteTopology.isDiscrete) hr hk hζ.differentiableAt hζ'
  have hmem : ∀ a, L.symm (P a) ∈ u.Λ := fun a => by rw [← hker, ← hL, L.apply_symm_apply, hP]
  refine HasForm.of_comp L.symm.toLinearEquiv.toLinearMap L.symm.injective ⟨Hm, h1, h2, fun a a₂ => ?_⟩
  refine (h3 ⟨_, hmem a⟩ ⟨_, hmem a₂⟩).symm.trans (congrArg _ (int_eq_of_exp fun k hk0 => ?_))
  have e1 := h4 k ⟨_, hmem a⟩ ⟨_, hmem a₂⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have e2 := hw k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have hp : ∀ a, (e ((k : ℂ)⁻¹ • P a)).left = (u.ex ((k : ℂ)⁻¹ • L.symm (P a))).left ≫ φ := fun a => by
    rw [← map_smul, ← L.apply_symm_apply ((k : ℂ)⁻¹ • P a), hL, L.symm_apply_apply]
    rfl
  haveI := A.isAb.comm
  have e3 := (weilIs_grpPullback_of_comm _ _ A.A A'.A y₀ φ A.L A'.L A.isLB A'.isLB hgp (LBIso.symm ⟨t, ht⟩) _ k _ _ _ _ _ (hp a) (hp a₂)).1 e1
  exact congrArg Units.val (weilIs_unique_fieldPoint _ A.A A.L A.isLB ℂ _ k _ _ _ _ e3 e2)

end

end GlobalTheory.LocLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem exists_periods
    (hLat : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range)
    [IsSeparated G.hom] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ}
    (hr : 0 < r) (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (P₀ : La →+ (Fin g → ℂ))
    (hi : Function.Injective P₀) (hs : Submodule.span ℝ (Set.range P₀) = ⊤) (hk : ∀ z, e b₀ z = 1 ↔ z ∈ P₀.range) :
    ∃ P : (Fin m → ℂ) → (La →+ (Fin g → ℂ)), P b₀ = P₀ ∧ ∀ᶠ b in 𝓝 b₀,
      (∀ x, DifferentiableAt ℂ (fun b => P b x) b) ∧ (∀ z, e b z = 1 ↔ z ∈ (P b).range) ∧
      Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by
  classical
  let bs := Module.Free.chooseBasis ℤ La
  choose ζ h1 h2 h3 using fun i => hl.lift (W := B) (β := id) (fun b => (1 : Over.mk (y b) ⟶ G)) (w₀ := b₀)
    (z₀ := P₀ (bs i)) hB hb₀ differentiableOn_id (fun _ h => h)
    (isHolTo_congr (isHolTo_comp_hom hy η[G].left) fun b _ => one_left _) ((hk _).2 ⟨_, rfl⟩)
  let P : (Fin m → ℂ) → (La →+ (Fin g → ℂ)) := fun b => (bs.constr ℤ fun i => ζ i b).toAddMonoidHom
  have hP : ∀ b x, P b x = ∑ i, bs.equivFun x i • ζ i b := fun b x => bs.constr_apply_fintype ℤ _ x
  have hP₀ : P b₀ = P₀ := by
    have : (bs.constr ℤ fun i => ζ i b₀) = P₀.toIntLinearMap := bs.ext fun i => by
      rw [bs.constr_basis, h1]; rfl
    ext1 x
    exact DFunLike.congr_fun this x
  have hd : ∀ᶠ b in 𝓝 b₀, ∀ x, DifferentiableAt ℂ (fun b => P b x) b := by
    filter_upwards [eventually_all.2 fun i => (h2 i).eventually_analyticAt] with b hb x
    simp only [hP]
    exact DifferentiableAt.fun_sum fun i _ => (hb i).differentiableAt.fun_const_smul _
  let K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ) := fun b => if hb : b ∈ B then homKer (he b hb).1.1 else ⊥
  have hK : ∀ b ∈ B, ∀ z, z ∈ K b ↔ e b z = 1 := fun b hb z => by simp only [K, dif_pos hb, mem_homKer]
  obtain ⟨C, hC, hCo, hC₀⟩ := eventually_nhds_iff.1 ((eventually_all.2 h3).and (hB.mem_nhds hb₀))
  have := hLat La g m C b₀ K P r hCo hC₀ hr
    (fun b hb z hz hn => (he b (hC b hb).2).2 z hn ((hK b (hC b hb).2 z).1 hz)) (fun b z z₀ hb hz hm => ?_)
    (fun x => (hd.self_of_nhds x).continuousAt) (fun b hb => ?_)
    (by rw [hP₀]; ext z; rw [hK b₀ hb₀, hk]) (hP₀ ▸ hi) (hP₀ ▸ hs)
  · refine ⟨P, hP₀, ?_⟩
    filter_upwards [this, hd, hB.mem_nhds hb₀] with b h h' hb
    exact ⟨h', fun z => by rw [h.1, hK b hb], h.2⟩
  · rw [hK b₀ hb₀]
    by_contra hne
    have ho := isOpen_ne_one (y := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => y bz.1) hol
    obtain ⟨i, hi1, hi2⟩ := ((hb.prodMk_nhds hz).eventually (ho.mem_nhds ⟨⟨hb₀, trivial⟩, hne⟩)).exists
    exact hi2 ((hK _ hi1.1 _).1 (hm i))
  · rintro _ ⟨x, rfl⟩
    rw [hP]
    exact sum_mem fun i _ => zsmul_mem ((hK b (hC b hb).2 _).2 ((hC b hb).1 i)) _

theorem isReduced_complex_tensor (E : Type) [Field E] [NumberField E] : IsReduced (ℂ ⊗[ℤ] 𝓞 E) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : Algebra.FormallyUnramified ℤ E := Algebra.FormallyUnramified.comp ℤ ℚ E
  haveI : Algebra.EssFiniteType ℤ E := Algebra.EssFiniteType.comp ℤ ℚ E
  haveI : IsReduced (ℂ ⊗[ℤ] E) := Algebra.FormallyUnramified.isReduced_of_field ℂ (ℂ ⊗[ℤ] E)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ ℂ) (IsScalarTower.toAlgHom ℤ (𝓞 E) E)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj

theorem lattice_comp {La : Type} [AddCommGroup La] {P : La →+ (Fin g → ℂ)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    {P' : La →+ (Fin g → ℂ)} (hP : ∀ x, h (P' x) = P x) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hd : DiscreteTopology P.range) : Submodule.span ℝ (Set.range P') = ⊤ ∧ DiscreteTopology P'.range := by
  constructor
  · have : Set.range P' = (h.symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]
      congr 1
      ext1 x
      exact h.eq_symm_apply.2 (hP x)
    rw [this, ← Submodule.map_span, hs, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · refine DiscreteTopology.of_continuous_injective (β := P.range)
      (f := fun z => ⟨h z, by obtain ⟨_, x, rfl⟩ := z; exact ⟨x, (hP x).symm⟩⟩) (by fun_prop) fun a b hab => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hab))

theorem exists_mulVec_comp {La T : Type} [AddCommGroup La] (M : T → Matrix (Fin g) (Fin g) ℂ)
    (P : T → (La →+ (Fin g → ℂ))) : ∃ P' : T → (La →+ (Fin g → ℂ)), ∀ b x, P' b x = (M b).mulVec (P b x) :=
  ⟨fun b => (Matrix.toLin' (M b)).toAddMonoidHom.comp (P b), fun b x => Matrix.toLin'_apply (M b) (P b x)⟩

theorem exists_equiv_mulVec {M : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit M.det) :
    ∃ j : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ), ∀ z, M.mulVec z = j z :=
  ⟨(Matrix.toLin'OfInv (Matrix.nonsing_inv_mul _ h) (Matrix.mul_nonsing_inv _ h)).toContinuousLinearEquiv,
    fun z => (Matrix.toLin'_apply M z).symm⟩

theorem natCast_mem_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (l.M : 𝓞 E) ∈ l.Mb := by
  refine Ideal.mul_le_left (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ?_
  rw [l.prod]
  exact Ideal.mem_span_singleton_self _

theorem dim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {p q : ℕ} {ty : Fin g → (E →+* ℂ)}
    (hty : IsTypeFn H p q ty) : Module.finrank ℚ E / 2 * (p + q) = g := by
  have h := PeriodDatum.two_mul_eq_of_isTypeFn H hty
  rw [IsTotallyComplex.finrank E] at h ⊢
  rw [Nat.mul_div_cancel_left _ two_pos]
  rw [_root_.mul_assoc] at h
  omega

theorem isUnit_natCast_of_over {K : Type} [Field K] [CharZero K] (s : X ⟶ Sp K) {k : ℕ} (hk : 0 < k) :
    IsUnit (k : Γ(X, ⊤)) := by
  have h : IsUnit (k : K) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')
  simpa only [map_natCast] using h.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appTop).hom

theorem section_pow {La : Type} [AddCommGroup La] {η' : La → (𝟙_ (Over X) ⟶ G)} (h : ∀ a c, η' (a + c) = η' a * η' c)
    {n : ℕ} {a : La} (hn : η' (n • a) = 1) (T : Over X) : (toUnit T ≫ η' a) ^ n = 1 := by
  rw [← hom_nsmul (e := fun a => toUnit T ≫ η' a) (fun a c => by rw [h, MonObj.comp_mul]), hn, MonObj.comp_one]

end

end GlobalTheory.LocLift

namespace GlobalTheory

open LocLift


set_option maxHeartbeats 400000 in
theorem LocLift.holomorphic_map_lifts_to_periods : ThetaUnifAV → Out.Laws → (∀ (k : Type) [Field
    k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G
    : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀
    : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z
    + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧
    (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e
    : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r
    : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin
    m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e
    b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧
    (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β
    : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀
    : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x
    w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g →
    ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w) → (∀ (La
    : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m →
    ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin
    g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b
    : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds
    b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b
    i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P
    b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P
    b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P
    b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) → (∀ (O
    : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+*
    Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ]
    O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B'
    : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin
    g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h
    b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a)) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y
    : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀
    : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X,
    ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x
    b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ =
    x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) →
    ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c)))) → ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) := by
  intro hT hL hsm hpol _ hrel hLat hdiag hweil E _ _ _ H D l Xo σ g ty _ _ hty D' t m B y b₀ P₀ e₀ hB hb₀ hyσ hy
    ⟨_, ⟨q1, q2, _, q4, _⟩, he₀, k₀, l₀, w₀, η₀, ηA₀⟩
  obtain ⟨hab, hdim, hrig, hsym⟩ := hpol E H D l _ _ _ _ Xo.univ
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  haveI := (hsm _ _ Xo.s inferInstance).2.2
  haveI := hab.proper
  let A : Out.PolAV Xo.X :=
    { A := Xo.univ.t.G, isAb := hab, g := _, smoothDim := hdim, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
      rigid := hrig, sym := hsym, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
  rw [dim_eq H hty] at hdim
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ := hrel _ σ _ Xo.s Xo.univ.t.G g m B y b₀ e₀ inferInstance hab hdim
    hB hb₀ hyσ hy he₀
  change HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, IsExp (y b) (e b) ∧ _ at he
  have hy₁ := isHolTo_mono hy hB₁ hB₁B
  obtain ⟨F, hF, hFd⟩ := exists_hol_rep hB₁ hb₁ hr hol he hl Xo.univ.t.act
  have hF₀ : ∀ a, F b₀ a = Matrix.diagonal (fun i => ((ty i).comp (algebraMap (𝓞 E) E)) a) := fun a =>
    Matrix.toLin'.injective (linear_lift_unique he₀.1 hr (he b₀ hb₁).2 fun z => by
      rw [Matrix.toLin'_apply, hF b₀ hb₁, ← l₀, Matrix.toLin'_apply]
      congr 1
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂₁, hh₀, hhd, hh⟩ := hdiag (𝓞 E) g m B₁ b₀ F _ inferInstance (isReduced_complex_tensor E)
    hB₁ hb₁ hFd hF₀
  haveI := D'.fin
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
  haveI := datum_free_int D'
  obtain ⟨P, hP₀, hP⟩ := exists_periods hLat hB₁ hb₁ hy₁ hr hol he hl P₀ q2 q4 k₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₂.mem_nhds hb₂))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₂ : C ⊆ B₂ := fun b hb => (hball b hb).2
  have hC₁ : C ⊆ B₁ := hC₂.trans hB₂₁
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)).mulVec (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : 𝓞 E) x, ∀ b ∈ C, P b (a • x) - (F b a).mulVec (P b x) = 0 := fun a x => by
    refine eq_zero_of_small hCc ((hPd _).sub (hmv (M := fun b => F b a) (β := id)
      (fun i j => (hFd a i j).mono hC₁) (hPd x))).continuousOn hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · haveI := Xo.univ.t.act.hom a
      exact (hom_sub_eq_one (he b (hC₁ hb)).1.1).2 (by rw [hF b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · ext i
      simp [hP₀, hF₀, q1, Matrix.mulVec_diagonal]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (hweil Xo.X A m k C y (fun b => e b ((k : ℂ)⁻¹ • P b a))
      (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk (isUnit_natCast_of_over Xo.s hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2 (by rw [hP₀]; exact w₀ k a a₂ c hk hc) b hb
  have hsec : ∀ (k : ℕ), 0 < k → ∀ (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) x, (∀ T, (toUnit T ≫ s) ^ k = 1) →
      toUnit _ ≫ s = e b₀ ((k : ℂ)⁻¹ • P₀ x) → ∀ b ∈ C, toUnit _ ≫ s = e b ((k : ℂ)⁻¹ • P b x) :=
    fun k hk s x hs h0 => (hweil Xo.X A m k C y (fun b => toUnit _ ≫ s)
      (fun b => e b ((k : ℂ)⁻¹ • P b x)) 1 b₀ hk (isUnit_natCast_of_over Xo.s hk) hCo hCc hC₀
      (isHolTo_congr (isHolTo_comp_hom (isHolTo_mono hy₁ hCo hC₁) s.left) fun b _ => by
        rw [Over.comp_left, Over.toUnit_left]; rfl) (htor k x)
      fun b hb => ⟨hs _, hpow k hk x b hb⟩).1 (by rw [hP₀]; exact h0)
  have hform : ∀ b ∈ C, HasForm D'.EF (P b) := fun b hb =>
    hasForm_of_weil hT hL.polBaseChange A (y b) (y b) (Category.id_comp _).symm (he b (hC₁ hb)).1 hr
      (he b (hC₁ hb)).2 (fun n x hx h0 => by
        obtain ⟨ζ, -, h2, h3⟩ := hl n Set.univ (fun _ => b) x 0 0 isOpen_univ trivial (differentiableOn_const _)
          (fun _ _ => hC₁ hb) hx h0
        exact ⟨ζ, h2, h3⟩) D'.EF (P b) (hk1 b hb) (hwe b hb)
  have hM := natCast_mem_level l
  obtain ⟨P', hP'd⟩ := exists_mulVec_comp (fun b => (h b)⁻¹) P
  have hdet : ∀ b ∈ C, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b (hC₂ hb)).1
  have hP' : ∀ b ∈ C, ∀ x, (h b).mulVec (P' b x) = P b x := fun b hb x => by
    rw [hP'd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have hj : ∀ b ∈ C, ∃ j : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ), ∀ z, (h b).mulVec z = j z := fun b hb =>
    exists_equiv_mulVec (hdet b hb)
  have hFh : ∀ b ∈ C, ∀ (a : 𝓞 E) z, (h b).mulVec (fun k => ty k (a : E) * z k) = (F b a).mulVec ((h b).mulVec z) :=
    fun b hb a z => by
      rw [Matrix.mulVec_mulVec, (hh b (hC₂ hb)).2, ← Matrix.mulVec_mulVec]
      congr 1
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl
  have hper : ∀ b ∈ C, IsPeriod D' ty (P' b) := fun b hb => by
    obtain ⟨j, hj⟩ := hj b hb
    have e1 : ∀ x, j (P' b x) = P b x := fun x => by rw [← hj, hP' b hb]
    obtain ⟨s1, s2⟩ := lattice_comp j e1 (hball b hb).1.2.2.2.1 (hball b hb).1.2.2.2.2
    refine ⟨fun a x i => congrFun (j.injective ?_ : P' b (a • x) = fun i => ty i (a : E) * P' b x i) i,
      fun x x' hx => (hball b hb).1.2.2.1 (by rw [← e1, hx, e1]), s2, s1,
      HasForm.of_comp j.toLinearEquiv.toLinearMap j.injective (by
        rw [show (fun x => j.toLinearEquiv.toLinearMap (P' b x)) = P b from funext e1]
        exact hform b hb)⟩
    rw [e1, ← hj, hFh b hb, hP' b hb]
    exact sub_eq_zero.1 (hlin a x b hb)
  refine ⟨C, P', fun b z => e b ((h b).mulVec z), hCo, hC₀, hC₁.trans hB₁B, ?_, ⟨hper, fun x => ?_⟩, ?_,
    fun b hb => ⟨hyσ b (hB₁B (hC₁ hb)), hper b hb, ?_, fun z => ?_, fun a z => ?_, ?_, fun a ha => ?_, fun a => ?_⟩⟩
  · ext1 x
    rw [← hP₀, ← hP' b₀ hC₀, hh₀, Matrix.one_mulVec]
  · simp only [hP'd]
    exact hmv (M := fun b => (h b)⁻¹) (β := id) (RiemannRel.differentiableOn_left_inverse h _
      (fun i j => (hhd i j).mono hC₂) fun b hb => Matrix.nonsing_inv_mul _ (hdet b hb)) (hPd x)
  · exact isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1).mulVec bz.2)) hol
      (hCo.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (β := Prod.fst)
        (fun i j => (hhd i j).comp differentiableOn_fst fun _ hw => hC₂ hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ hw.1, trivial⟩
  · obtain ⟨j, hj⟩ := hj b hb
    change IsExp (y b) (fun z => e b ((h b).mulVec z))
    simp only [hj]
    exact (he b (hC₁ hb)).1.comp j
  · obtain ⟨j, hj⟩ := hj b hb
    rw [(hball b hb).1.2.1]
    refine exists_congr fun x => ?_
    rw [← hP' b hb, hj, hj]
    exact j.injective.eq_iff
  · beta_reduce
    rw [hFh b hb, hF b (hC₁ hb)]
  · simpa only [Matrix.mulVec_smul, hP' b hb] using hwe b hb
  · simp only [Matrix.mulVec_smul, hP' b hb]
    refine hsec l.M (by have := l.three_le; omega) _ _ (section_pow Xo.univ.eta_add (Xo.univ.eta_ker _ ?_)) (η₀ a ha) b hb
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM trivial
  · simp only [Matrix.mulVec_smul, hP' b hb]
    exact hsec l.A l.A_pos _ _ (section_pow Xo.univ.etaA_add (Xo.univ.etaA_ker a)) (ηA₀ a) b hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_map_moduli_lifts_locally_to_periods : ThetaUnifAV → Out.Laws → (∀ (k
    : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S'
    : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G
    : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀
    : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z
    + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧
    (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e
    : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r
    : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin
    m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e
    b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧
    (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β
    : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀
    : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x
    w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g →
    ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w) → (∀ (La
    : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m →
    ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin
    g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b
    : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds
    b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b
    i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P
    b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P
    b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P
    b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) → (∀ (O
    : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+*
    Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ]
    O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B'
    : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin
    g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h
    b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a)) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y
    : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀
    : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X,
    ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x
    b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ =
    x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) →
    ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c)))) → ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) := by
  intro h1 h2 h3
  exact GlobalTheory.LocLift.holomorphic_map_lifts_to_periods h1 h2
    (fun k _ X s hs => let ⟨a, b, c⟩ := h3 k X s hs; ⟨a, ⟨fun x => (b x).1, fun x => (b x).2⟩, c⟩)
end
