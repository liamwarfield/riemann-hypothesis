module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipalSiegPreComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelInhabitant

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem sum_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    ∑ i, ∑ j, Out.stdSymp g (halves g i) (halves g j) * b j * a i = omegaStd a b := by
  have l : ∀ a, (halves g (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (halves g (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l]
    split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, r]
    split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg, _root_.mul_comm]

theorem exists_lev_of_rel {k g : ℕ} {G U : Type} [CommGroup G] [CommGroup U] {ze : U}
    (W : G → G → U → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹) (v : Fin (2 * g) → G) (hv : ∀ i, v i ^ k = 1)
    (hp : ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j)) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → G, (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ k = 1) ∧
      ∀ x y, W (lev x) (lev y) (ze ^ omegaStd x y) := by
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* U := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  let u : Fin g ⊕ Fin g → T := fun i => ⟨v (halves g i), hv _⟩
  have hu : ∀ i j, e (u i) (u j) = ze ^ Out.stdSymp g (halves g i) (halves g j) := fun i j =>
    (hw' (u i) (u j) _ (hp _ _)).symm
  let l : (Fin g ⊕ Fin g → ℤ) → T := fun a => ∏ i, u i ^ a i
  refine ⟨fun a => (l a).1, fun x y => ?_, fun x => (l x).2, fun x y => ?_⟩
  · rw [← Subgroup.coe_mul]
    congr 1
    simp only [l, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · have : w (l x) (l y) = ze ^ omegaStd x y := by
      show e (l x) (l y) = _
      have z : ∀ {I : Type} [Fintype I] (n : I → ℤ), ze ^ ∑ i, n i = ∏ i, ze ^ n i := fun n =>
        map_prod (zpowersHom U ze) (fun i => Multiplicative.ofAdd (n i)) _
      have s : ∀ i, e.flip (l y) (u i) = ze ^ ∑ j, Out.stdSymp g (halves g i) (halves g j) * y j := fun i => by
        rw [z, MonoidHom.flip_apply]
        simp only [l, map_prod, map_zpow, hu, ← zpow_mul]
      rw [← sum_stdSymp, ← MonoidHom.flip_apply, z]
      show e.flip (l y) (∏ i, u i ^ x i) = _
      simp only [map_prod, map_zpow, s, ← zpow_mul, Finset.sum_mul]
    exact this ▸ hw _ _

end GlobalTheory.SiegelInhabitant

namespace GlobalTheory


open SiegelInhabitant in
theorem exists_principal_siegPre_complex : ∀ (h k : ℕ), 0 < k → ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (ζ : o), IsPrimitiveRoot (em ζ) k → ∃ c : SiegPre h k ζ (spMap em), c.Principal ∧ SmoothOfRelativeDimension h c.A.hom := by
  intro h k hk o _ em ζ hζ
  have hL : Out.Laws := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1
  obtain ⟨P, -, -, hg, -⟩ := polarisedTorus_algebraic h (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)) 0 0
    (Matrix.isSymm_one.smul _)
    (by
      have : (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)).map Complex.im = 1 := by
        ext i j
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      rw [this]
      exact Matrix.PosDef.one)
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  subst hg
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let ze : ℂˣ := (hζ.isUnit hk.ne').unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 hζ
  have := P.isAb.comm
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk' ze hze
  obtain ⟨w₁, w₂, -⟩ := hL.weil _ P k (Out.baseOver _)
  obtain ⟨lev, add, tors, weil⟩ := exists_lev_of_rel (G := Out.baseOver _ ⟶ P.A)
    (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) pt hpt hw
  obtain ⟨c, φ, -, hc, -⟩ := exists_siegPre_of_polAV hL GlobalTheory.T.theorem_of_cube_polAbelianScheme o ℂ em P.g k ζ ze P lev rfl hk' rfl hze add tors
    (fun x y => by
      have e : unitOn (ze ^ omegaStd x y) = unitOn ze ^ omegaStd x y := map_zpow (Units.map _) _ _
      rw [e]
      exact weil x y)
  refine ⟨c, hc, ?_⟩
  have := P.smoothDim
  rw [← Over.w φ.hom]
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φ.hom))
  have H : SmoothOfRelativeDimension (0 + P.g) (φ.hom.left ≫ P.A.hom) := inferInstance
  rwa [Nat.zero_add] at H

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  first | exact @GlobalTheory.PolUnif.exists_unif_riemannForm | exact GlobalTheory.PolUnif.exists_unif_riemannForm | (intros; apply GlobalTheory.PolUnif.exists_unif_riemannForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandard
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SqRootPairing

theorem eq_of_sq_eq_of_odd {G : Type} [CommGroup G] {k : ℕ} (hk : Odd k) {a b : G} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (h : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul] at ha hb
  rw [h] at ha
  exact mul_left_cancel (ha.trans hb.symm)

theorem weilIs_down {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : Out.WeilIs G L k x₀ y₀ c) : Out.WeilIs G' L' k x y c := by
  subst hg
  exact (weilIs_grpPullback_of_comm _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem pow_eq_one (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {k n : ℕ} {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (H : Out.WeilIs P.A P.L k x y c) (hx : x ^ n = 1) : c ^ n = 1 := by
  have key : ∀ l : ℕ, Out.WeilIs P.A P.L k (x ^ (l + 1)) y (c ^ (l + 1)) := fun l => by
    induction l with
    | zero => rw [zero_add, pow_one, pow_one]; exact H
    | succ l ih => rw [pow_succ, pow_succ c]; exact (hL.weil S P k T).2.1 _ _ _ _ _ ih H
  have := key n
  rw [pow_succ, hx, _root_.one_mul] at this
  have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB this H
  rwa [pow_succ, mul_eq_right] at e

theorem weilIs_lev_of_sqOf : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  intro h k K _ ζ σ S s c p P φ lev hk3 hk hζ hp hsq hlev _ tors a b e he
  obtain ⟨hpb, -, φ₂, sq, iso⟩ := hsq
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let z : ℂˣ := Units.mk0 (σ ζ) (by rw [hζ]; exact Complex.exp_ne_zero _)
  have hz : (z : ℂ) = σ ζ := rfl
  have hzk : z ^ k = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hz, hζ, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, Units.val_one])
  have hez : e = z ^ omegaStd a b := Units.ext (by
    rw [Units.val_zpow_eq_zpow_val, hz, hζ, ← Complex.exp_int_mul, he]
    congr 1
    ring)
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have dc : (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left).IsLB := LB.isLB_linComb c.isLB _ _
  have w₀ := (c.geom ℂ p σ z hp hz).2.2 a b
  have pt : ∀ a, (toUnit (Over.mk p) ≫ c.lev a).left = (lev a).left ≫ φ := fun a => by
    rw [hlev, Over.comp_left, Over.toUnit_left]
    rfl
  have w₁ := weilIs_down dc dg hpb (SiegelPull.diag_iso sq iso) (𝟙_ (Over (Sp ℂ))) p (Category.id_comp p).symm k
    (lev a) (lev b) _ _ _ (pt a) (pt b) w₀
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P k (𝟙_ (Over (Sp ℂ)))).1 (lev a) (lev b) (tors a) (tors b)
  have w₂ := SiegelOfPolarised.weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg
    (SiegelOfPolarised.lbIso_diag hL P) hc₀
  have e₂ := CommutatorPairing.weilIs_unique hL.globalFns P.isAb dg w₂ w₁
  have up : ∀ (u : ℂˣ) (n : ℕ), unitOn (u ^ n) = unitOn u ^ n := fun u n => map_pow _ _ _
  have e₁ : c₀ = unitOn e := by
    refine eq_of_sq_eq_of_odd hk (pow_eq_one hL P hc₀ (tors a)) ?_ (e₂.trans ?_)
    · refine (up e k).symm.trans ?_
      rw [hez, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
      exact map_one _
    · refine Eq.trans ?_ (up e 2)
      rw [hez, mul_comm, zpow_mul, zpow_ofNat]
  exact e₁ ▸ hc₀

end GlobalTheory.SqRootPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandardStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_square_root_weil_pairing_standard : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  first | exact @GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | exact GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | (intros; apply GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix

namespace GlobalTheory.RiemannRel

theorem map_im_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.im = P.map Complex.re * Q.map Complex.im + P.map Complex.im * Q.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

theorem map_re_mul {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.re = P.map Complex.re * Q.map Complex.re - P.map Complex.im * Q.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

theorem hermForm_cols {h : ℕ} (Hm P Q : Matrix (Fin h) (Fin h) ℂ) (i j : Fin h) :
    (Pᵀ * Hm * Q.map star) i j = hermForm Hm (fun k => P k i) (fun k => Q k j) := by
  rw [Matrix.mul_assoc]
  simp [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec]

theorem matrix_form {h : ℕ} (Hm L M : Matrix (Fin h) (Fin h) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hG : (Mᵀ * Hm * M.map star).map Complex.im = 0)
    (hA : (Lᵀ * Hm * M.map star).map Complex.im = 1)
    (hB : (Lᵀ * Hm * L.map star).map Complex.im = 0) :
    IsUnit M.det ∧ (M⁻¹ * L).IsSymm ∧ ((M⁻¹ * L).map Complex.im).PosDef := by
  set G := Mᵀ * Hm * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have h1 : M.map star = (Mᵀ)ᴴ := by ext i j; simp
    rw [hGdef, h1]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hH
  set R := G.map Complex.re with hR
  have hRs : Rᵀ = R := by
    ext i j
    have := congrArg Complex.re (hGh.apply i j)
    simpa [hR] using this
  have hGR : G = R.map Complex.ofReal := by
    ext i j
    have := congrFun (congrFun hG i) j
    apply Complex.ext
    · simp [hR]
    · simpa [hR] using this
  have hRp : R.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hRs) fun x hx => ?_
    set xc : Fin h → ℂ := fun i => (x i : ℂ) with hxc
    have hst : star (M.mulVec xc) = (M.map star).mulVec xc := by
      funext i
      simp [Matrix.mulVec, dotProduct, hxc]
    have hne : M.mulVec xc ≠ 0 := by
      intro h0
      apply hx
      have h1 : (Lᵀ * Hm * M.map star).mulVec xc = 0 := by
        rw [← Matrix.mulVec_mulVec, ← hst, h0]; simp
      have h2 : ((Lᵀ * Hm * M.map star).map Complex.im).mulVec x = 0 := by
        funext i
        have := congrArg Complex.im (congrFun h1 i)
        simpa [Matrix.mulVec, dotProduct, hxc, Complex.im_sum] using this
      rwa [hA, Matrix.one_mulVec] at h2
    have h3 := hpos _ hne
    have h4 : M.mulVec xc ⬝ᵥ Hm.mulVec (star (M.mulVec xc)) = xc ⬝ᵥ G.mulVec xc := by
      rw [hst, hGdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec xc, Matrix.vecMul_transpose]
    rw [h4] at h3
    simpa [Matrix.mulVec, dotProduct, hxc, Complex.re_sum, hR] using h3
  have hRu : IsUnit R.det := hRp.det_pos.ne'.isUnit
  have hMu : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : G.det = 0 := by
      rw [hGdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp
    have h2 : G.det = (R.det : ℂ) := by
      rw [hGR]
      exact (Complex.ofRealHom.map_det R).symm
    rw [h1] at h2
    exact hRu.ne_zero (Complex.ofReal_eq_zero.1 h2.symm)
  set τ := M⁻¹ * L with hτ
  have hL : L = M * τ := by rw [hτ, Matrix.mul_nonsing_inv_cancel_left _ _ hMu]
  have hA' : Lᵀ * Hm * M.map star = τᵀ * G := by
    conv_lhs => rw [hL]
    rw [hGdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hB' : Lᵀ * Hm * L.map star = τᵀ * G * τ.map star := by
    have : L.map star = M.map star * τ.map star := by
      conv_lhs => rw [hL]
      exact Matrix.map_mul (f := starRingEnd ℂ)
    rw [this, ← Matrix.mul_assoc, hA']
  set X := τ.map Complex.re with hX
  set Y := τ.map Complex.im with hY
  have e1 : τᵀ.map Complex.re = Xᵀ := rfl
  have e2 : τᵀ.map Complex.im = Yᵀ := rfl
  have e3 : (τ.map star).map Complex.re = X := by ext i j; simp [hX]
  have e4 : (τ.map star).map Complex.im = -Y := by ext i j; simp [hY]
  rw [hB', map_im_mul, ← hA', hA, hA', map_re_mul, e1, e2, e3, e4, hG, ← hR] at hB
  rw [hA', map_im_mul, e1, e2, hG, ← hR, Matrix.mul_zero, zero_add] at hA
  have hRY : R * Y = 1 := by
    have := congrArg Matrix.transpose hA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.transpose_one] at this
  have hYi : R⁻¹ = Y := Matrix.inv_eq_right_inv hRY
  have hYi' : R⁻¹ = Yᵀ := Matrix.inv_eq_left_inv hA
  have hXs : Xᵀ = X := by
    rw [Matrix.mul_zero, sub_zero, Matrix.mul_neg, Matrix.mul_assoc, hRY, Matrix.mul_one, Matrix.one_mul] at hB
    exact (neg_add_eq_zero.1 hB)
  refine ⟨hMu, ?_, hYi ▸ hRp.inv⟩
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun hXs i) j
  · exact congrFun (congrFun (hYi'.symm.trans hYi) i) j

theorem exists_siegel_of_symplectic : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  intro h Hm v hH hpos hv
  let L : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inl i) k
  let M : Matrix (Fin h) (Fin h) ℂ := Matrix.of fun k i => v (.inr i) k
  obtain ⟨hM, hs, hp⟩ := matrix_form Hm L M hH hpos
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inr i) (.inr j)).trans ?_
      simp [omegaStd])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inr j)).trans ?_
      simp [omegaStd, Pi.single_apply, Matrix.one_apply, eq_comm])
    (by
      ext i j
      rw [Matrix.map_apply, hermForm_cols]
      refine (hv (.inl i) (.inl j)).trans ?_
      simp [omegaStd])
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hM
  refine ⟨M⁻¹ * L, M.toLinearEquiv' inferInstance, hs, hp, fun a => ?_⟩
  change M.mulVec (per (M⁻¹ * L) a) = _
  rw [per, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hM]
  funext k
  simp [L, M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]

end GlobalTheory.RiemannRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_period_of_symplectic_basis : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  first | exact @GlobalTheory.RiemannRel.exists_siegel_of_symplectic | exact GlobalTheory.RiemannRel.exists_siegel_of_symplectic | (intros; apply GlobalTheory.RiemannRel.exists_siegel_of_symplectic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.LevelLift

theorem exists_linear_lift {J G V : Type} [Fintype J] [DecidableEq J] [Group G] [AddCommGroup V] [Module ℂ V]
    (ex : V → G) (hadd : ∀ z w, ex (z + w) = ex z * ex w) (honto : Function.Surjective ex)
    (Λ : Submodule ℤ V) (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (k : ℕ) (hk : 0 < k) (lev : (J → ℤ) → G)
    (hl : ∀ a b, lev (a + b) = lev a * lev b) (hp : ∀ a, lev a ^ k = 1) :
    ∃ l : (J → ℤ) →ₗ[ℤ] Λ, ∀ a, lev a = ex ((k : ℂ)⁻¹ • (l a : V)) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let E : V →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) (fun z w => by
    rw [hadd]; rfl)
  let F : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (lev z)) (fun z w => by
    rw [hl]; rfl)
  choose z hz using fun j : J => honto (lev (Pi.single j 1))
  have hw : ∀ j, k • z j ∈ Λ := fun j => by
    rw [← hker]
    have h1 : E (k • z j) = k • E (z j) := map_nsmul E k (z j)
    have h2 : ex (k • z j) = ex (z j) ^ k := congrArg Additive.toMul h1
    rw [h2, hz, hp]
  let l : (J → ℤ) →ₗ[ℤ] Λ := (Pi.basisFun ℤ J).constr ℤ fun j => ⟨k • z j, hw j⟩
  have hlj : ∀ j, (l (Pi.single j 1) : V) = k • z j := fun j => by
    have := (Pi.basisFun ℤ J).constr_basis ℤ (fun j => (⟨k • z j, hw j⟩ : Λ)) j
    rw [Pi.basisFun_apply] at this
    exact congrArg Subtype.val this
  let F' : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => E ((k : ℂ)⁻¹ • (l a : V))) (fun a b => by
    rw [map_add (f := _), Submodule.coe_add, smul_add, map_add (f := _)])
  refine ⟨l, fun a => ?_⟩
  have hmem : a ∈ F.eqLocus F' := by
    have ha : a = ∑ j, a j • (Pi.single j 1 : J → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [ha]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
    show Additive.ofMul (lev (Pi.single j 1)) = Additive.ofMul (ex ((k : ℂ)⁻¹ • (l (Pi.single j 1) : V)))
    rw [hlj, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul, hz]
  exact congrArg Additive.toMul (show F a = F' a from hmem)

theorem dvd_sub_of_exp_eq (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  obtain ⟨c, hc⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨c, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    first
      | linear_combination (2 * Real.pi * Complex.I) * hc
      | linear_combination -(2 * Real.pi * Complex.I) * hc
      | linear_combination hc
      | linear_combination -hc
  exact_mod_cast this

theorem exists_lattice_lift : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  intro h k P lev u Ef hk hl hp hW hE
  obtain ⟨l, hlift⟩ := exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp
  refine ⟨l, hlift, fun a b => ?_⟩
  have h1 := hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  have h2 := hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  rw [← hlift a, ← hlift b] at h2
  have h3 := GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2
  exact dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)

end GlobalTheory.LevelLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_lift_of_level_section : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  first | exact @GlobalTheory.LevelLift.exists_lattice_lift | exact GlobalTheory.LevelLift.exists_lattice_lift | (intros; apply GlobalTheory.LevelLift.exists_lattice_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticZmodLift
namespace GlobalTheory

theorem symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelMod
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymplecticLevelLift

open Matrix Module

theorem omegaStd_single {h : ℕ} (i j : Fin h ⊕ Fin h) :
    omegaStd (Pi.single i 1) (Pi.single j 1) = (-Matrix.J (Fin h) ℤ) i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [omegaStd, Matrix.J, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem gram_eq {h : ℕ} {M : Type} [AddCommGroup M] {Ef : LinearMap.BilinForm ℤ M}
    {b : Basis (Fin h ⊕ Fin h) ℤ M} (hb : IsSymplecticBasis Ef b) (hE : Ef.IsAlt)
    (v : Fin h ⊕ Fin h → M) :
    (Matrix.of fun i j => Ef (v i) (v j)) =
      (b.toMatrix v)ᵀ * (-Matrix.J (Fin h) ℤ) * b.toMatrix v := by
  ext i j
  rw [of_apply, hb.apply_eq_sum hE]
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Basis.toMatrix_apply, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring

theorem exists_symplectic_equiv_congr : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  intro h k M _ _ _ Ef l _ hrk halt hbij hl
  have hE : Ef.IsAlt := halt
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hE hbij hrk
  set v : Fin h ⊕ Fin h → M := fun j => l (Pi.single j 1) with hv
  have hmem : (b.toMatrix v).map (Int.castRingHom (ZMod k)) ∈
      Matrix.symplecticGroup (Fin h) (ZMod k) := by
    rw [SymplecticGroup.mem_iff']
    have h1 : (Matrix.of fun i j => Ef (v i) (v j)).map (Int.castRingHom (ZMod k)) =
        (-Matrix.J (Fin h) ℤ).map (Int.castRingHom (ZMod k)) := by
      ext i j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).2 (hl (Pi.single i 1) (Pi.single j 1))
      rw [omegaStd_single, Int.cast_sub, sub_eq_zero] at this
      simpa [hv] using this
    rw [gram_eq hb hE, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg _), map_J,
      transpose_map] at h1
    simpa using h1
  obtain ⟨N, hN, hNT⟩ := symplectic_zmod_lift h k _ hmem
  have hw : b.toMatrix (fun j => ∑ i, N i j • b i) = N := by
    ext i j
    rw [Basis.toMatrix_apply, b.repr_sum_self]
  obtain ⟨c, hc, hcv⟩ := hb.exists_basis_of_toMatrix_mem hE (hw.symm ▸ hN)
  have hcong : ∀ j, ∃ m : M, v j - c j = (k : ℤ) • m := by
    intro j
    have hd : ∀ i, ∃ t : ℤ, b.toMatrix v i j - N i j = k * t := fun i => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1 ?_
      have := congrFun (congrFun hNT i) j
      simp only [Matrix.map_apply, eq_intCast] at this
      rw [Int.cast_sub, this, sub_self]
    choose t ht using hd
    refine ⟨∑ i, t i • b i, ?_⟩
    rw [← b.sum_toMatrix_smul_self v j, hcv, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← sub_smul, ht, mul_smul]
  choose m hm using hcong
  refine ⟨c.equivFun.symm, fun x y => ?_, fun a => ⟨∑ j, a j • m j, ?_⟩⟩
  · have hr : ∀ (z : Fin h ⊕ Fin h → ℤ) i, c.repr (c.equivFun.symm z) i = z i := fun z i => by
      rw [← c.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc.apply_eq_sum hE]
    simp only [hr, omegaStd]
  · have hla : l a = ∑ j, a j • v j := by
      conv_lhs => rw [← Finset.univ_sum_single a]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hla, c.equivFun_symm_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← smul_sub, hm, smul_comm]

end GlobalTheory.SymplecticLevelLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelModStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_basis_congr_level_mod : ∀ (h k : ℕ) (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (Ef : LinearMap.BilinForm ℤ M) (l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] M), 0 < k → Module.finrank ℤ M = 2 * h → (∀ x, Ef x x = 0) → Function.Bijective Ef → (∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b) → ∃ B : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] M, (∀ a b, Ef (B a) (B b) = omegaStd a b) ∧ ∀ a, ∃ m : M, l a - B a = (k : ℤ) • m := by
  first | exact @GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | exact GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr | (intros; apply GlobalTheory.SymplecticLevelLift.exists_symplectic_equiv_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.KeyFam

theorem holUnif_transport_linearEquiv : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add (f := _), u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩

end GlobalTheory.KeyFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holUnif_comp_linearEquiv_exists : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  exact @GlobalTheory.KeyFam.holUnif_transport_linearEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SiegelPtAt

theorem sqrt_at_point (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ) (hk : 3 ≤ k)
    (hζ : σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k)) (p : Sp ℂ ⟶ F.X) :
    ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ F.univ.A.left), SqOf P F.univ p φ := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hζ' : IsUnit ζ := IsUnit.mk0 _ fun e => Complex.exp_ne_zero _ (by rw [← hζ, e, map_zero])
  obtain ⟨R, _, π, p₁, Q₁, φ₁, -, rfl, hQ₁, -⟩ := GlobalTheory.SiegelNearby.exists_etale_sqrt hL σ F (by omega) hζ' p
  obtain ⟨P, ψ, hpb⟩ := GlobalTheory.SiegelNearby.exists_polPB hL.polBaseChange Q₁ p₁
  exact ⟨P, ψ ≫ φ₁, (sqOf_calculus h k K ζ _ _ _ F.s F.univ π).1 p₁ Q₁ P φ₁ ψ hQ₁ hpb⟩

theorem levels_pull {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (hsq : SqOf P c p φ) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A),
      (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) ∧ (∀ a b, lev (a + b) = lev a * lev b) ∧
        ∀ a, lev a ^ k = 1 := by
  choose l hl hl' using fun a => GlobalTheory.SiegelNearby.exists_section_pull hsq.1 (c.lev a) k (c.lev_tors a)
  refine ⟨l, hl', fun a b => ?_, hl⟩
  have key := hsq.1.2 (𝟙_ (Over (Sp ℂ))) (l a) (l b) (toUnit _ ≫ c.lev a) (toUnit _ ≫ c.lev b)
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
  rw [← MonObj.comp_mul, ← c.lev_add, Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left] at key
  apply Over.OverMorphism.ext
  apply hsq.1.1.hom_ext
  · rw [hl', ← key]; exact (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem perLev_of_level (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A))
    (hg : P.g = h) (hk : 0 < k) (add : ∀ a b, lev (a + b) = lev a * lev b) (tors : ∀ a, lev a ^ k = 1)
    (weil : ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) →
      Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) :
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, PerLev P τ k lev := by
  obtain ⟨u, Hm, χ, Ef, hAH, hEf, hbij, halt, hfree, hfin, hrank, hW⟩ := GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm h P hg
  obtain ⟨l, hl, hdvd⟩ := GlobalTheory.T.exists_lattice_lift_of_level_section h k P lev u Ef hk add tors weil (fun x y e he => hW k x y e hk he)
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.T.exists_symplectic_basis_congr_level_mod h k u.Λ Ef l hk hrank halt hbij hdvd
  let v : Fin h ⊕ Fin h → (Fin h → ℂ) := fun i => (B (Pi.single i 1) : Fin h → ℂ)
  have hv : ∀ i j, (hermForm Hm (v i) (v j)).im =
      (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ) := fun i j => by
    rw [← hEf, hB]
  obtain ⟨τ, T, hs, hp, hT⟩ := GlobalTheory.T.exists_siegel_period_of_symplectic_basis h Hm v hAH.1 hAH.2.1 hv
  obtain ⟨u', hex, hΛ⟩ := GlobalTheory.T.holUnif_comp_linearEquiv_exists h P.A P.L u T
  have hBa : ∀ a, (B a : Fin h → ℂ) = ∑ i, a i • v i := fun a => by
    conv_lhs => rw [show a = ∑ i, a i • (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨τ, hg, hs, hp, u', fun z => ?_, fun n a b e hn he => ?_, fun a => ?_⟩
  · rw [hΛ]
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := B.surjective ⟨T z, hz⟩
      refine ⟨a, T.injective ?_⟩
      rw [hT, ← hBa, ha]
    · rintro ⟨a, rfl⟩
      rw [hT, ← hBa]
      exact (B a).2
  · have := hW n (B a) (B b) e hn (by rw [hB]; exact he)
    rwa [hex, hex, map_smul, map_smul, hT, hT, ← hBa, ← hBa]
  · rw [hl, hex, map_smul, hT, ← hBa]
    obtain ⟨m, hm⟩ := hBl a
    have e : ((l a : u.Λ) : Fin h → ℂ) = (B a : Fin h → ℂ) + (k : ℂ) • (m : Fin h → ℂ) := by
      rw [← sub_eq_iff_eq_add', ← Submodule.coe_sub, hm, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ]
      norm_cast
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [e, smul_add, smul_smul, inv_mul_cancel₀ hk', one_smul, u.ex_add, (u.ker _).2 m.2, _root_.mul_one]

theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  intro h k K _ ζ σ F _ hk hodd hζ p hp
  obtain ⟨P, φ, hsq⟩ := sqrt_at_point h k K ζ σ F hk hζ p
  obtain ⟨lev, hlev, add, tors⟩ := levels_pull F.univ p P φ hsq
  have weil := GlobalTheory.T.siegel_square_root_weil_pairing_standard h k K ζ σ F.X F.s F.univ p P φ lev hk hodd hζ hp hsq hlev add tors
  obtain ⟨τ, hτ⟩ := perLev_of_level h k P lev hsq.2.1 (by omega) add tors weil
  exact ⟨τ, P, lev, φ, hτ, hsq, hlev⟩

end GlobalTheory.SiegelPtAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodTorusComplexPointSiegelFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  first | exact @GlobalTheory.SiegelPtAt.exists_ptAt | exact GlobalTheory.SiegelPtAt.exists_ptAt | (intros; apply GlobalTheory.SiegelPtAt.exists_ptAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelIntegral

theorem exists_complexPoint_mem : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] (U : X.Opens),
    (U : Set X).Nonempty → ∃ p : Sp ℂ ⟶ X, p ≫ s = spMap (RingHom.id ℂ) ∧ ∀ z : Sp ℂ, p z ∈ U := by
  intro X s _ U ⟨x, hx⟩
  obtain ⟨a, ha, haU⟩ := GlobalTheory.ConeOnto.exists_rat_pt s U.isOpen.isLocallyClosed hx
  refine ⟨a, ?_, haU⟩
  rw [ha]
  exact (Spec.map_id _).symm

theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k →
    Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ →
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, KeyFam.PtAt F.univ p τ := GlobalTheory.T.exists_periodTorus_complexPoint_siegelFamily

noncomputable def conjEmb (n : ℕ) : cycAway n →+* ℂ := (starRingEnd ℂ).comp (cycAway n).subtype

theorem conjEmb_injective (n : ℕ) : Function.Injective (conjEmb n) :=
  (RingHom.injective (starRingEnd ℂ)).comp Subtype.val_injective

theorem conjEmb_zeta (n : ℕ) :
    conjEmb n (zetaAway n) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := by
  simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, zetaAway, zeta]
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]

theorem preconnected_of_complex (g n : ℕ) (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n)
    (F : SFam g n (conjEmb n (zetaAway n))) : PreconnectedSpace F.X := by
  have hL := GlobalTheory.abelianSchemeLaws_all
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  rw [preconnectedSpace_iff_clopen]
  intro W hW
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hpW⟩ := exists_complexPoint_mem F.X F.s ⟨W, hW.isOpen⟩ hne.1
  obtain ⟨q, hq, hqW⟩ := exists_complexPoint_mem F.X F.s ⟨Wᶜ, hW.compl.isOpen⟩
    (by simpa [Set.nonempty_compl] using hne.2)
  have hζ : RingHom.id ℂ (conjEmb n (zetaAway n)) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := conjEmb_zeta n
  obtain ⟨τ, hτ⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ p hp
  obtain ⟨τ', hτ'⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ q hq
  obtain ⟨hp', hq', H⟩ := GlobalTheory.SiegelConnected.sameComp_of_ptAt hL.1 hL.2 GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds
    g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ τ τ' p q hp hq hτ hτ'
  obtain ⟨z⟩ : Nonempty (Sp ℂ) := inferInstance
  have h1 := (pullback.fst F.s (spMap (RingHom.id ℂ))).continuous.image_connectedComponent_subset
    (pullback.lift q (𝟙 _) hq' z) ⟨_, H z, rfl⟩
  have e : ∀ (r : Sp ℂ ⟶ F.X) (hr : r ≫ F.s = 𝟙 _ ≫ spMap (RingHom.id ℂ)),
      pullback.fst F.s (spMap (RingHom.id ℂ)) (pullback.lift r (𝟙 _) hr z) = r z := fun r hr => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [e, e] at h1
  exact hW.compl.connectedComponent_subset (hqW z) h1 (hpW z)

end GlobalTheory.SiegelIntegral


open GlobalTheory.SiegelIntegral in
theorem GlobalTheory.SiegelIntegral.integral_normal_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  intro g n hg hn hodd F
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have hB : Geo.Tor.IsNormalScheme (Sp (cycAway n)) := GlobalTheory.ZJ.isNormalScheme_sp _
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  have hN : Geo.Tor.IsNormalScheme F.X :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension _ _ F.s (g * (g + 1) / 2) hB
  haveI hLN : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  refine ⟨?_, hN, hLN⟩
  haveI : GlobalTheory.IsNormalScheme F.X := GlobalTheory.IsNormalScheme.of_pred hN
  obtain ⟨F', π, hpb, -⟩ := F.exists_baseChange (conjEmb n) (conjEmb_injective n) rfl
  haveI := preconnected_of_complex g n hg hn hodd F'
  have hgen : {x : F.X | (F.s x).asIdeal = ⊥} ⊆ Set.range π := by
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst F.s (spMap (conjEmb n))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      change (⊥ : Ideal ℂ).comap (conjEmb n) = (F.s x).asIdeal
      rw [hx]
      exact Ideal.comap_bot_of_injective _ (conjEmb_injective n)
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨hpb.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]⟩
  have hpre : _root_.IsPreconnected (Set.univ : Set F.X) :=
    (isPreconnected_range π.continuous).subset_closure (Set.subset_univ _) (by
      rw [← F.isReduced_and_dense.2.closure_eq]
      exact closure_mono hgen)
  obtain ⟨c, hc, -⟩ := GlobalTheory.exists_principal_siegPre_complex g n (Nat.pos_of_ne_zero hn0) (cycAway n)
    (cycAway n).subtype (zetaAway n) (Complex.isPrimitiveRoot_exp n hn0)
  haveI := F.nonempty _ Subtype.val_injective c hc
  haveI : ConnectedSpace F.X := { toPreconnectedSpace := ⟨hpre⟩, toNonempty := inferInstance }
  exact GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace F.X
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  first | exact @GlobalTheory.SiegelIntegral.integral_normal_noetherian | exact GlobalTheory.SiegelIntegral.integral_normal_noetherian | (intros; apply GlobalTheory.SiegelIntegral.integral_normal_noetherian <;> assumption)
end
