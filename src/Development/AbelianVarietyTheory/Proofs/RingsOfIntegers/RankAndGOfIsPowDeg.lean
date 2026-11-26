module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

private theorem relDim_eq_of_smoothOfRelativeDimension_grp {X Y : Scheme.{0}} (f : X ⟶ Y) (n m : ℕ) (x : X)
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hQ⟩ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  have hp := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra! H
    exact hp.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 H))
  have : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : algebraMap Γ(X, V) (Localization.Away t) 1 = 0 := Subsingleton.elim _ _
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at h0
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := h0
    have hc' : t ^ k = 0 := by simpa using hc
    exact htp (hp.mem_of_pow_mem k (by rw [hc']; exact Ideal.zero_mem _))
  have hn' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    (Localization.Away t) t _ h
  have hm' := hQ t ht
  let := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) (Localization.Away t) := hn'
  have a1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have : Algebra.IsStandardSmoothOfRelativeDimension m Γ(Y, U) (Localization.Away t) := hm'
  have a2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast a1.symm.trans a2

private theorem exists_limit_fan_smooth_relDim_mul {S : Scheme.{0}} (A : Over S) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom) :
    ∀ k : ℕ, ∃ c : Fan (fun _ : Fin k => A), Nonempty (IsLimit c) ∧
      SmoothOfRelativeDimension (k * g) c.pt.hom := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fan.mk (𝟙_ (Over S)) (fun i => Fin.elim0 i), ⟨Fan.IsLimit.mk _
      (fun s => CartesianMonoidalCategory.toUnit s.pt) (fun _ i => Fin.elim0 i)
      (fun _ _ _ => CartesianMonoidalCategory.toUnit_unique _ _)⟩, ?_⟩
    rw [zero_mul]
    show SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ k ih =>
    obtain ⟨c, ⟨hc⟩, hsm⟩ := ih
    refine ⟨extendFan (f := fun _ : Fin (k + 1) => A) c
      (BinaryFan.mk (CartesianMonoidalCategory.fst A c.pt) (CartesianMonoidalCategory.snd A c.pt)),
      ⟨extendFanIsLimit (fun _ : Fin (k + 1) => A) hc
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct A c.pt)⟩, ?_⟩
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (k * g)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (k * g)
    have h1 : SmoothOfRelativeDimension (k * g) (pullback.fst A.hom c.pt.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback A.hom c.pt.hom).flip hsm
    have h2 := smoothOfRelativeDimension_comp (n := k * g) (m := g) (pullback.fst A.hom c.pt.hom) A.hom
    rw [Nat.succ_mul]
    exact h2

theorem rank_and_g_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j), D'.rank = j * D.rank ∧ D'.P.g = j * D.P.g := by
  intro R _ _ j D D' pD
  rcases pD with ⟨pw, w, wg, wr, xe, cpr, wpsi⟩
  refine ⟨?_, ?_⟩
  · have e : D'.X ≃ₗ[ℤ] (Fin j → D.X) := xe.toIntLinearEquiv
    unfold DegPre.rank
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rcases pw with ⟨pr, hom, lim⟩
    obtain ⟨c, ⟨hc⟩, hsm⟩ := exists_limit_fan_smooth_relDim_mul D.P.A D.P.g D.P.5 j
    let e := IsLimit.conePointUniqueUpToIso lim hc
    have hw : e.hom.left ≫ c.pt.hom = D'.P.A.hom := Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := j * D.P.g) e.hom.left c.pt.hom
    rw [hw, zero_add] at h3
    let := D'.P.2
    have p : (𝟙_ (Over (Spec (CommRingCat.of R)))).left := (inferInstance : Nonempty (PrimeSpectrum R)).some
    exact relDim_eq_of_smoothOfRelativeDimension_grp D'.P.A.hom _ _ ((η[D'.P.A]).left p) D'.P.5 h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiWZeroProd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem four_comm {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (p : A' ⟶ A) [IsMonHom p] (f : A ⟶ A) (f' : A' ⟶ A') (h : f' ≫ p = p ≫ f) (k : Fin 4) :
    (![(padd A' (𝟙 _) f').left, 𝟙 A'.left, f'.left, (toUnit A' ≫ η[A']).left] : Fin 4 → _) k ≫ p.left =
      p.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) k := by
  fin_cases k
  · show (padd A' (𝟙 _) f').left ≫ p.left = p.left ≫ (padd A (𝟙 _) f).left
    rw [← Over.comp_left, ← Over.comp_left]
    unfold padd
    congr 1
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, Category.id_comp, h, ← Category.assoc, comp_lift,
      Category.comp_id]
  · show 𝟙 A'.left ≫ p.left = p.left ≫ 𝟙 A.left
    simp
  · show f'.left ≫ p.left = p.left ≫ f.left
    rw [← Over.comp_left, ← Over.comp_left, h]
  · show (toUnit A' ≫ η[A']).left ≫ p.left = p.left ≫ (toUnit A ≫ η[A]).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Category.assoc, IsMonHom.one_hom, ← Category.assoc, toUnit_unique (p ≫ toUnit A) (toUnit A')]

set_option maxHeartbeats 1000000 in
theorem psi_weight_zero_product (pD : IsPowDeg D' D j) {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (hx : ∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) (oa : D.OAct O) (oa' : D'.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (w0 : O) (h : TraceFormTwistIso D oa w0) :
    TraceFormTwistIso D' oa' w0 := by
  obtain ⟨u, hu, h0, hy⟩ := h
  have := oa'.onB.hom w0
  have : ∀ i, IsMonHom (pD.pw.pr i) := pD.pw.hom
  obtain ⟨u', hu', hval⟩ := exists_boxPull_gen pD.w pD.w_gen D.P.isLB D'.P.isLB
    (φ' := ![(padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left, 𝟙 D'.P.A.left, (oa'.onB.act w0).left, (toUnit D'.P.A ≫ η[D'.P.A]).left])
    (φ := fun _ => ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left])
    (ε := ![1, -2, -1, 2])
    (fun i => (pD.pw.pr i).left) (fun i k => four_comm (pD.pw.pr i) _ _ (hact w0 i) k) (fun _ => u) (fun _ => hu)
  have hη : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨u', hu', ?_, ?_⟩
  · apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    rw [val_pull hJ', val_one]
    have e1 := hval _ (𝟙 _ ≫ eSec D'.P.A) z J J' hJ hJ'
    have e2 : ∀ i, val u ((𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left) z J = 1 := by
      intro i
      have hc : (𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ eSec D.P.A := by
        simp only [Category.id_comp, eSec, ← Over.comp_left, IsMonHom.one_hom]
      rw [hc, ← val_pull hJ, val_corr hJ h0, val_one]
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (η[D'.P.A]) (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    simp only [← hη] at e3
    rw [Finset.prod_eq_one (fun i _ => e2 i)] at e1
    simp only [Category.assoc] at e1
    have e4 : ∀ m : D'.P.A.left ⟶ D'.P.A.left, eSec D'.P.A ≫ m = (η[D'.P.A]).left ≫ m := fun m => rfl
    have h1f : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ oa'.onB.act w0 = 1 := by
      rw [hη, IsMonHom.one_hom]
    simp only [e4, ← hη, e3, h1f] at e1
    have alg : ∀ {G : Type} [CommGroup G] (a v : G), a * (a ^ 2)⁻¹ * a⁻¹ * a ^ 2 * v = v := by
      intros
      group
    have h11 : ((1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) * 1) = 1 := mul_one _
    erw [h11] at e1
    rwa [alg] at e1
  · intro y
    apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    have hD : ∀ x : D.X, val (D.psi (x + w0 • x)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
        (val (D.psi (w0 • x)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (𝟙 _ ≫ D.xK x) z J =
        val (D.psi x) (𝟙 _) z J * val D.rigK (𝟙 _) z J := by
      intro x
      have hc := val_corr hJ (hy x) (𝟙 _)
      simp only [DegPre.tau, val_mul hJ, val_inv, val_pull hJ] at hc
      exact hc
    rw [val_mul hJ', val_mul hJ', val_pull hJ']
    simp only [DegPre.tau, val_mul hJ', val_inv]
    have P := fun x => psi_val pD hJ hJ' x (𝟙 _)
    have Rg := rig_val pD hJ hJ' (𝟙 _)
    have U := hval _ (𝟙 _ ≫ D'.xK y) z J J' hJ hJ'
    have hpr : ∀ i, (𝟙 _ ≫ D'.xK y) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ D.xK (pD.xe y i) := by
      intro i
      simp only [Category.id_comp, DegPre.xK, ptK, ← Over.comp_left, Category.assoc, pD.c_pr]
    simp only [hpr] at U
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (toUnit (TK R) ≫ D'.c y)
      (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    have e6 : (toUnit (TK R) ≫ D'.c y) ≫ oa'.onB.act w0 = toUnit (TK R) ≫ D'.c (w0 • y) := by
      rw [Category.assoc, ← oa'.c_lin]
    have e7 : (toUnit (TK R) ≫ D'.c y) * (toUnit (TK R) ≫ D'.c (w0 • y)) = toUnit (TK R) ≫ D'.c (y + w0 • y) := by
      rw [D'.c_add]
      unfold padd
      rw [← Category.assoc, comp_lift, Hom.mul_def]
    have e8 : ∀ x, (toUnit (TK R) ≫ D'.c x).left = D'.xK x := fun _ => rfl
    have e9 : (toUnit (TK R) ≫ η[D'.P.A]).left = (toUnit (TK R)).left ≫ eSec D'.P.A := rfl
    rw [e6, e7, Hom.one_def] at e3
    simp only [e8, e9] at e3
    simp only [Category.id_comp] at P Rg U e3 hD ⊢
    rw [e3] at U
    have hxe1 : ∀ i, pD.xe (y + w0 • y) i = pD.xe y i + w0 • pD.xe y i := by
      intro i
      rw [map_add (f := _), hx]
      rfl
    have hxe2 : ∀ i, pD.xe (w0 • y) i = w0 • pD.xe y i := by
      intro i
      rw [hx]
      rfl
    have Py := inv_mul_eq_iff_eq_mul.mp (P y)
    have Ps := inv_mul_eq_iff_eq_mul.mp (P (y + w0 • y))
    have Pw := inv_mul_eq_iff_eq_mul.mp (P (w0 • y))
    have key := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => (by rw [hxe1 i, hxe2 i]; exact hD (pD.xe y i) :
      val (D.psi (pD.xe (y + w0 • y) i)) (𝟙 _) z J * (val (D.psi (pD.xe y i)) (𝟙 _) z J)⁻¹ *
        (val (D.psi (pD.xe (w0 • y) i)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (D.xK (pD.xe y i)) z J =
        val (D.psi (pD.xe y i)) (𝟙 _) z J * val D.rigK (𝟙 _) z J))
    simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
    rw [Py, Ps, Pw, eq_inv_mul_of_mul_eq Rg, eq_inv_mul_of_mul_eq U, eq_inv_mul_of_mul_eq key]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ (oa : D.OAct O) (oa' : D'.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ w0 : O, Geo.Tor.TraceFormTwistIso D oa w0 → Geo.Tor.TraceFormTwistIso D' oa' w0 := by
  intro R _ _ j D D' pD O _ _ _ _ hx oa oa' hact w0 h
  exact psi_weight_zero_product pD hx oa oa' hact w0 h

end GlobalTheory.PsiWZeroProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowKernel

theorem pow_ext {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {X : Over S} {x y : X ⟶ G'} (h : ∀ l, x ≫ p.pr l = y ≫ p.pr l) : x = y :=
  Fan.IsLimit.hom_ext p.lim x y h

theorem one_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    (l : Fin j) : η[G'] ≫ p.pr l = η[G] := by
  haveI := p.hom l
  exact IsMonHom.one_hom (p.pr l)

theorem main : ∀ (S : Scheme.{0}) (T' T G' G B' B : Over S) [GrpObj T'] [GrpObj T] [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (pT : IsPowGrp T' T j) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (i : T ⟶ G) (q : G ⟶ B) (i' : T' ⟶ G') (q' : G' ⟶ B'), (∀ l, i' ≫ p.pr l = pT.pr l ≫ i) → (∀ l, q' ≫ pB.pr l = p.pr l ≫ q) → IsPullback i (toUnit T) q η[B] → IsPullback i' (toUnit T') q' η[B'] := by
  intro S T' T G' G B' B _ _ _ _ _ _ j pT p pB i q i' q' hi hq h

  have w : i' ≫ q' = toUnit T' ≫ η[B'] := by
    apply pow_ext pB
    intro l
    rw [Category.assoc, Category.assoc, hq l, one_pr pB l, ← Category.assoc, hi l,
      Category.assoc, h.w, ← Category.assoc, toUnit_unique (pT.pr l ≫ toUnit T) (toUnit T')]

  have key : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      (s.fst ≫ p.pr l) ≫ q = s.snd ≫ η[B] := by
    intro s l
    rw [Category.assoc, ← hq l, ← Category.assoc, s.condition, Category.assoc, one_pr pB l]
  have fac : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)) ≫ pT.pr l =
        h.lift (s.fst ≫ p.pr l) s.snd (key s l) :=
    fun s l => Fan.IsLimit.fac pT.lim _ l
  refine IsPullback.of_isLimit (c := PullbackCone.mk i' (toUnit T') w)
    (PullbackCone.IsLimit.mk w
      (fun s => Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)))
      ?_ ?_ ?_)
  · intro s
    apply pow_ext p
    intro l
    rw [Category.assoc, hi l, ← Category.assoc, fac s l, h.lift_fst]
  · intro s
    exact toUnit_unique _ _
  · intro s m hm _
    apply pow_ext pT
    intro l
    rw [fac s l]
    apply h.hom_ext
    · rw [h.lift_fst, Category.assoc, ← hi l, ← Category.assoc, hm]
    · rw [h.lift_snd]
      exact toUnit_unique _ _

end GlobalTheory.PowKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
namespace GlobalTheory.PowMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

variable {S : Scheme.{0}}

noncomputable def powHom {G B : Over S} (q : G ⟶ B) : ∀ n : ℕ, powObj G n ⟶ powObj B n
  | 0 => 𝟙 (𝟙_ (Over S))
  | n + 1 => (q ⊗ₘ powHom q n : G ⊗ powObj G n ⟶ B ⊗ powObj B n)

theorem powHom_pr {G B : Over S} (q : G ⟶ B) :
    ∀ (n : ℕ) (i : Fin n), powHom q n ≫ powPr B i = powPr G i ≫ q
  | 0, i => i.elim0
  | n + 1, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tensorHom_fst q (powHom q n)
    · show (q ⊗ₘ powHom q n) ≫ snd _ _ ≫ powPr B i = (snd _ _ ≫ powPr G i) ≫ q
      rw [tensorHom_snd_assoc, powHom_pr q n i, Category.assoc]

theorem prop_powHom (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G B : Over S} (q : G ⟶ B) (hq : P q.left) : ∀ n : ℕ, P (powHom q n).left
  | 0 => P.id_mem S
  | n + 1 => by
    have ih := prop_powHom P q hq n
    show P (q ⊗ₘ powHom q n).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := P) hq ih (Over.w q).symm (Over.w (powHom q n)).symm

theorem prop_of_comm (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ} (p : IsPowGrp G' G j)
    (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B') (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q)
    (hq : P q.left) : P q'.left := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  let f : B' ≅ powObj B j := pB.lim.conePointUniqueUpToIso (powIsLimit B j)
  have he : ∀ i, e.hom ≫ powPr G i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp (powIsLimit G j) ⟨i⟩
  have hf : ∀ i, f.inv ≫ pB.pr i = powPr B i := fun i =>
    pB.lim.conePointUniqueUpToIso_inv_comp (powIsLimit B j) ⟨i⟩
  have hq' : q' = e.hom ≫ powHom q j ≫ f.inv := by
    refine pB.lim.hom_ext fun ⟨i⟩ => ?_
    show q' ≫ pB.pr i = (e.hom ≫ powHom q j ≫ f.inv) ≫ pB.pr i
    rw [h, Category.assoc, Category.assoc, hf, powHom_pr, ← Category.assoc, he]
  have i1 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have i2 : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  rw [hq', Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact prop_powHom P q hq j

theorem isMonHom_of_comm {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ}
    (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B')
    (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q) (hq : IsMonHom q) : IsMonHom q' := by
  refine ⟨pB.lim.hom_ext fun ⟨i⟩ => ?_, pB.lim.hom_ext fun ⟨i⟩ => ?_⟩
  · have := p.hom i
    have := pB.hom i
    show (η ≫ q') ≫ pB.pr i = η ≫ pB.pr i
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i
    have := pB.hom i
    show (μ ≫ q') ≫ pB.pr i = ((q' ⊗ₘ q') ≫ μ) ≫ pB.pr i
    rw [Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h]

theorem main : ∀ (S : Scheme.{0}) (G' G B' B : Over S) [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B), ∃ q' : G' ⟶ B', (∀ i, q' ≫ pB.pr i = p.pr i ≫ q) ∧ (IsMonHom q → IsMonHom q') ∧ (Flat q.left → Flat q'.left) ∧ (Surjective q.left → Surjective q'.left) ∧ (QuasiCompact q.left → QuasiCompact q'.left) ∧ (IsAffineHom q.left → IsAffineHom q'.left) := by
  intro S G' G B' B _ _ _ _ j p pB q
  have h : ∀ i, pB.lim.lift (Fan.mk G' fun i => p.pr i ≫ q) ≫ pB.pr i = p.pr i ≫ q := fun i =>
    pB.lim.fac (Fan.mk G' fun i => p.pr i ≫ q) ⟨i⟩
  exact ⟨_, h, isMonHom_of_comm p pB q _ h, prop_of_comm @Flat p pB q _ h,
    prop_of_comm @Surjective p pB q _ h, prop_of_comm @QuasiCompact p pB q _ h,
    prop_of_comm @IsAffineHom p pB q _ h⟩

end GlobalTheory.PowMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem quasiCompact_geomConnected_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (QuasiCompact G.hom → QuasiCompact G'.hom) ∧ (Smooth G.hom → GeometricallyConnected G.hom → GeometricallyConnected G'.hom) := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @QuasiCompact p, fun hs hc => ?_⟩
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  have := geomConnected_powObj G j
  have := smooth_isMultiplicative
  have : Smooth (powObj G j).hom := prop_powObj @Smooth G hs j
  have := geomConnected_of_isIso e
  rw [hw]
  exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsBis
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpandsFracLinear

open GlobalTheory.ExpandsLinear

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → U.SecK k) (E : Fin n → Fam D.toPre (FractionRing R) k) (s₀ : U.SecK k), (∀ l, U.Expands k (s l) (E l)) → (∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G.hom (jK R)) (c l)) * (s l).f jj) → U.Expands k s₀ (∑ l, c l • E l) := by
  intro R _ _ I D A G _ _ U k n c s E s₀ hE hs
  simp only [UnifPre.Expands] at hE ⊢
  choose r hr σ f h1 h2 h3 using hE
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin n))
    (fun l => c l / algebraMap R (FractionRing R) (r l))
  choose a ha using fun l => hb l (Finset.mem_univ l)
  have hc : ∀ l, algebraMap R (FractionRing R) (a l) * algebraMap R (FractionRing R) (r l) =
      algebraMap R (FractionRing R) (b : R) * c l := by
    intro l
    have hrl : algebraMap R (FractionRing R) (r l) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
      exact fun h => hr l (IsFractionRing.injective R (FractionRing R) h)
    rw [ha l, Algebra.smul_def]
    field_simp
  refine ⟨b, nonZeroDivisors.ne_zero b.2, secComb (fun l => scal G.hom (a l)) σ,
    fun α => secComb (fun l => scal D.toPre.P.A.hom (a l)) (fun l => f l α), ?_, ?_, ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) U.LG.L _ _ _ _ (pullback.fst G.hom (jK R))
      (pullback.snd G.hom (jK R)) _ G.hom rfl pullback.condition s σ r a b c hc h1 s₀ hs
  · intro α
    refine secScal_comb (algebraMap R (FractionRing R)) D.toPre.P.L _ _ _ _ (D.toPre.prB (FractionRing R)).left
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_ ?_ (fun l => (E l).s α)
      (fun l => f l α) r a b c hc (fun l => h2 l α) _ ?_
    · have hh := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      unfold DegPre.BF TF at *
      rw [hh]
      congr 1
      show jFK (FractionRing R) ≫ jK R = _
      unfold jFK jK
      rw [← Spec.map_comp]
      rfl
    · exact Over.w (D.toPre.prB (FractionRing R))
    · intro j
      rw [fam_sum_f]
      simp only [smul_f]
      rfl
  · intro e
    exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun l => h3 l e) (fun j => rfl) (fun α j => rfl)

end GlobalTheory.ExpandsFracLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowAct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open GlobalTheory.Serre in
theorem exists_powAct : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), (∀ (O : Type) [Ring O] (r : RingAct G O), ∃ r' : RingAct G' O, ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a) ∧ ∀ (O : Type) [CommRing O] (r : Geo.Tor.OAct O G), ∃ r' : Geo.Tor.OAct O G', ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a := by
  intro S G' G _ _ _ _ j p
  obtain ⟨pr, hpr, hl⟩ := p
  have hprI : ∀ i, IsMonHom (pr i) := hpr
  have hext : ∀ {X : Over S} (f g : X ⟶ G'), (∀ i, f ≫ pr i = g ≫ pr i) → f = g :=
    fun f g h => Fan.IsLimit.hom_ext hl f g h

  let lf : (G ⟶ G) → (G' ⟶ G') := fun f => Fan.IsLimit.lift hl (fun i => pr i ≫ f)
  have hlf : ∀ (f : G ⟶ G) (i : Fin j), lf f ≫ pr i = pr i ≫ f :=
    fun f i => Fan.IsLimit.fac hl _ i
  have hlf' : ∀ (f : G ⟶ G) (i : Fin j) {Z : Over S} (h : G ⟶ Z),
      lf f ≫ pr i ≫ h = pr i ≫ f ≫ h := by
    intro f i Z h
    rw [← Category.assoc, hlf, Category.assoc]
  have hone : lf (𝟙 G) = 𝟙 G' := hext _ _ (fun i => by rw [hlf]; simp)
  have hcomp : ∀ f g : G ⟶ G, lf (f ≫ g) = lf f ≫ lf g := fun f g =>
    hext _ _ (fun i => by simp only [Category.assoc, hlf, hlf'])
  have hmon : ∀ f : G ⟶ G, IsMonHom f → IsMonHom (lf f) := by
    intro f hf
    constructor
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.one_hom]
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

  have hadd : ∀ f g : G ⟶ G, lf (lift f g ≫ μ) = lift (lf f) (lf g) ≫ μ := by
    intro f g
    refine hext _ _ (fun i => ?_)
    simp only [Category.assoc, hlf, IsMonHom.mul_hom, comp_lift_assoc, lift_map_assoc]
  refine ⟨fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.map_one, hone],
      fun a b => by
        try dsimp only
        rw [r.map_mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.map_add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩,
    fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.one, hone],
      fun a b => by
        try dsimp only
        rw [r.mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' T₁ T₁' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

def BoxSquare (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull f) (M.pull p))
    (we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')) (h : Fin j → (T' ⟶ T)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
    (∀ i, pr i (p' (r z)) ∈ M.U (jM i)) → p' (r z) ∈ M'.U jM' → (∀ i, prG i (f' (r z)) ∈ L.U (jL i)) →
    bw w (r ≫ p') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
      ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem compat_box (hM : M.IsLB) {p₁ : T₁ ⟶ B} {p₁' : T₁' ⟶ B'} {f₁ : T₁ ⟶ G} {f₁' : T₁' ⟶ G'}
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    {we₁ : LB.Iso (L.pull f₁) (M.pull p₁)}
    {we₁' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f₁') (M'.pull p₁')} {h₁ : Fin j → (T₁' ⟶ T₁)}
    {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (Q : BoxSquare w we we' h) (Q₁ : BoxSquare w we₁ we₁' h₁)
    (H : CompatAlong we₁ we m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) (hf' : m' ≫ f₁' = f') (hp' : m' ≫ p₁' = p')
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p) (hm : ∀ i, m' ≫ h₁ i = h i ≫ m) :
    CompatAlong we₁' we' m' := by
  intro q V h₁ h₂
  apply unit_ext
  intro x hx
  refine (gm_rp₁ m' x _ V h₁ hx _).trans (Eq.trans ?_ (gm_res (𝟙 T') x h₂ hx _).symm)
  change Geo.Tor.gw we₁' m' x (q.1 ⟨⟩) (fun _ => q.2 ⟨⟩) = Geo.Tor.gw we' (𝟙 T') x (q.1 ⟨⟩) (fun _ => q.2 ⟨⟩)
  obtain ⟨J, hJ⟩ := exists_good_at hM x
  have x₂ := h₂ hx
  have a₁ : ∀ i, pr i (p' x) ∈ M.U (J (p' ≫ pr i)) := fun i => by simpa using hJ (p' ≫ pr i)
  have b₁ : p' x ∈ M'.U (q.1 ⟨⟩) := mem_pull.mp x₂.1
  have c₀ : f' x ∈ LB.wchart L prG (q.2 ⟨⟩) := by
    have := mem_pull.mp x₂.2
    exact (Scheme.Hom.mem_preimage f').mp this
  have c₁ : ∀ i, prG i (f' x) ∈ L.U (q.2 ⟨⟩ i) := fun i => LB.wchart_le L prG (q.2 ⟨⟩) i c₀
  have ep : p₁' (m' x) = p' x := by rw [← hp']; rfl
  have ef : f₁' (m' x) = f' x := by rw [← hf']; rfl
  have e1 := Q T' (𝟙 T') x (fun i => J (p' ≫ pr i)) (q.1 ⟨⟩) (q.2 ⟨⟩) (fun i => a₁ i) b₁ (fun i => c₁ i)
  have e2 := Q₁ T' m' x (fun i => J (p' ≫ pr i)) (q.1 ⟨⟩) (q.2 ⟨⟩) (fun i => by rw [ep]; exact a₁ i)
    (by rw [ep]; exact b₁) (fun i => by rw [ef]; exact c₁ i)
  have e3 : ∏ i, Geo.Tor.gw we₁ (h i ≫ m) x (J (p' ≫ pr i)) (fun _ => q.2 ⟨⟩ i) =
      ∏ i, Geo.Tor.gw we (h i) x (J (p' ≫ pr i)) (fun _ => q.2 ⟨⟩ i) := by
    refine Finset.prod_congr rfl fun i _ => H.stalk hf hp (h i) x _ _ ?_ ?_
    · rw [← pt_of_eq (hE i) x]; exact a₁ i
    · rw [pt_of_eq (hF i) x]; exact c₁ i
  simp only [Category.id_comp] at e1
  simp only [hp', hm] at e2
  exact _root_.mul_left_cancel (e2.trans (e3.trans e1.symm))

private theorem gm_pull_transition_eq_gm_comp {X T Z : Scheme.{0}} (L : LB X) (f : T ⟶ X) (r : Z ⟶ T) (z : Z) (a b : L.ι)
    (h : r z ∈ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    gm r z _ ((L.pull f).g (fun _ => a) (fun _ => b)) = gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) :=
  (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b) h.1 h.2).trans (by simp)

private theorem gw_mul_gm_transition_eq_gw_of_isGen {B G T Z : Scheme.{0}} {M : LB B} {L : LB G} {p : T ⟶ B} {f : T ⟶ G}
    (hM : M.IsLB) {we : LB.Iso (L.pull f) (M.pull p)} (hwe : we.IsGen) (r : Z ⟶ T) (z : Z) (c : M.ι)
    (a b : L.ι) (h1 : p (r z) ∈ M.U c) (h2 : f (r z) ∈ L.U a) (h3 : f (r z) ∈ L.U b) :
    Geo.Tor.gw we r z c (fun _ => a) * gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) =
      Geo.Tor.gw we r z c (fun _ => b) := by
  have hz : r z ∈ ((M.pull p).div (L.pull f)).U (fun _ => c, fun _ => a) ⊓
      ((M.pull p).div (L.pull f)).U (fun _ => c, fun _ => b) :=
    ⟨⟨mem_pull.mpr h1, mem_pull.mpr h2⟩, ⟨mem_pull.mpr h1, mem_pull.mpr h3⟩⟩
  have hp : (r ≫ p) z ∈ M.U c := h1
  have gM : gm (r ≫ p) z (M.U c ⊓ M.U c) (M.g c c) = 1 := by
    have e0 := congrArg (gm (r ≫ p) z _) (hM.g_self c)
    rw [gm_res (r ≫ p) z _ hp, map_one] at e0
    exact e0
  have e := congrArg (gm r z _) (hwe (fun _ => c, fun _ => a) (fun _ => c, fun _ => b))
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz] at e
  have eg : gm r z _ (((M.pull p).div (L.pull f)).g (fun _ => c, fun _ => a) (fun _ => c, fun _ => b)) =
      (gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b))⁻¹ := by
    refine (map_mul (gm r z _) _ _).trans ?_
    refine (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv (gm r z _) _).trans (congrArg (·⁻¹) (gm_res r z _ hz _)))).trans ?_
    have hzM : r z ∈ (M.pull p).U (fun _ => c) ⊓ (M.pull p).U (fun _ => c) := ⟨mem_pull.mpr h1, mem_pull.mpr h1⟩
    have hzL : r z ∈ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b) := ⟨mem_pull.mpr h2, mem_pull.mpr h3⟩
    refine (congrArg₂ (· * ·) (gm_pull_transition_eq_gm_comp M p r z c c hzM)
      (congrArg (·⁻¹) (gm_pull_transition_eq_gm_comp L f r z a b hzL))).trans ?_
    exact (congrArg (· * _) gM).trans (one_mul _)
  rw [eg] at e
  change Geo.Tor.gw we r z c (fun _ => a) = _ * Geo.Tor.gw we r z c (fun _ => b) at e
  rw [e, mul_comm]
  exact mul_inv_cancel_left _ _

theorem change_chart (hM : M.IsLB) {we : LB.Iso (L.pull f) (M.pull p)} (hwe : we.IsGen) {K : Type} [Fintype K]
    {ε : K → ℤ} {Z Y : Scheme.{0}} (z : Z) (P : K → (Z ⟶ T)) {φ : K → (Y ⟶ G)} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (m : Z ⟶ Y) (c : ∀ k, P k ≫ f = m ≫ φ k) (jM : K → M.ι) (a b : K → L.ι)
    (hM' : ∀ k, p (P k z) ∈ M.U (jM k)) (ha : ∀ k, φ k (m z) ∈ L.U (a k)) (hb : ∀ k, φ k (m z) ∈ L.U (b k)) :
    (∏ k, Geo.Tor.gw we (P k) z (jM k) (fun _ => a k) ^ ε k) * gm m z (LB.wchart L φ a) (t.s a) =
      (∏ k, Geo.Tor.gw we (P k) z (jM k) (fun _ => b k) ^ ε k) * gm m z (LB.wchart L φ b) (t.s b) := by
  have hf : ∀ k, f (P k z) = φ k (m z) := fun k => pt_of_eq (c k) z
  have ma : m z ∈ LB.wchart L φ a := Set.mem_iInter.2 fun k => ha k
  have mb : m z ∈ LB.wchart L φ b := Set.mem_iInter.2 fun k => hb k
  rw [gen_trans ht m z ma mb]
  unfold trF
  rw [← _root_.mul_assoc, ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow]
  refine congrArg (· ^ ε k) ?_
  have e := gw_mul_gm_transition_eq_gw_of_isGen hM hwe (P k) z (jM k) (a k) (b k) (hM' k) (by rw [hf k]; exact ha k)
    (by rw [hf k]; exact hb k)
  rw [c k] at e
  exact e

theorem alg {U K I : Type} [CommGroup U] [Fintype K] [Fintype I] (ε : K → ℤ) (A W' : K → U) (W : K → I → U)
    (h : ∀ k, A k * W' k = ∏ i, W k i) {a' : U} {a b : I → U} (e₁ : (∏ k, A k ^ ε k) * a' = ∏ i, a i)
    (e₂ : ∀ i, a i = (∏ k, W k i ^ ε k) * b i) : a' = (∏ k, W' k ^ ε k) * ∏ i, b i := by
  apply mul_left_cancel (a := ∏ k, A k ^ ε k)
  rw [e₁, Finset.prod_congr rfl (fun i _ => e₂ i), Finset.prod_mul_distrib, Finset.prod_comm,
    ← _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← mul_zpow, h, Finset.prod_zpow]

theorem rel_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {K : Type} [Fintype K] {ε : K → ℤ} {Z YL YM YM' : Scheme.{0}} (z : Z) (P : K → (Z ⟶ T'))
    {φ : K → (YL ⟶ G)} {ψ : K → (YM ⟶ B)} {ψ' : K → (YM' ⟶ B')}
    {tL : LB.Gen (LB.LinComb L φ ε)} (htL : tL.IsGen) (tM : LB.Gen (LB.LinComb M ψ ε))
    (tM' : LB.Gen (LB.LinComb M' ψ' ε)) (mB : Z ⟶ YM') (nB : Fin j → (Z ⟶ YM)) (nG : Fin j → (Z ⟶ YL))
    (c₁ : ∀ i k, (P k ≫ h i) ≫ f = nG i ≫ φ k) (c₂ : ∀ k, P k ≫ p' = mB ≫ ψ' k)
    (c₃ : ∀ i k, (P k ≫ h i) ≫ p = nB i ≫ ψ k)
    (HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (mB ≫ ψ' k) ^ ε k) * val tM' mB z J' = ∏ i, val tM (nB i) z J)
    (HU : ∀ i J N, Good M z J → Good L z N → val tM (nB i) z J =
      (∏ k, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => N (nG i ≫ φ k)) ^ ε k) * val tL (nG i) z N)
    (jL : K → Fin j → L.ι) (jM' : K → M'.ι) (coh : LB.Coh M' (fun k => mB ≫ ψ' k) jM')
    (mM : ∀ k, ψ' k (mB z) ∈ M'.U (jM' k)) (mL : ∀ k i, φ k (nG i z) ∈ L.U (jL k i)) :
    gm mB z (LB.wchart M' ψ' jM') (tM'.s jM') =
      (∏ k, Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k) ^ ε k) *
        ∏ i, gm (nG i) z (LB.wchart L φ (fun k => jL k i)) (tL.s (fun k => jL k i)) := by
  obtain ⟨J', hJ', hJ'e⟩ := exists_good M' hM' z (fun k => mB ≫ ψ' k) jM' coh mM
  obtain ⟨J, hJ⟩ := exists_good_at hM z
  obtain ⟨N, hN⟩ := exists_good_at hL z
  have hQ : ∀ k, om w z J J' (mB ≫ ψ' k) * Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k) =
      ∏ i, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i) := by
    intro k
    have hk : ∀ i, (mB ≫ ψ' k) ≫ pr i = nB i ≫ ψ k := fun i => by
      rw [← c₂ k, Category.assoc, hE i, ← Category.assoc, c₃ i k]
    have e := Q Z (P k) z (fun i => J (nB i ≫ ψ k)) (jM' k) (jL k)
      (fun i => by
        have eq : pr i (p' (P k z)) = (nB i ≫ ψ k) z := by
          rw [← hk i, ← c₂ k]
          rfl
        rw [eq]
        exact hJ (nB i ≫ ψ k))
      (by rw [pt_of_eq (c₂ k) z]; exact mM k)
      (fun i => by
        have := mL k i
        rw [← pt_of_eq (c₁ i k) z] at this
        rw [← pt_of_eq (hF i) (P k z)]
        exact this)
    unfold om
    rw [hJ'e k]
    simp only [hk]
    rw [← c₂ k]
    exact e
  have he₂ : ∀ i, val tM (nB i) z J = (∏ k, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i) ^ ε k) *
      gm (nG i) z (LB.wchart L φ (fun k => jL k i)) (tL.s (fun k => jL k i)) := fun i =>
    (HU i J N hJ hN).trans (change_chart hM hwe z (fun k => P k ≫ h i) htL (nG i) (c₁ i)
      (fun k => J (nB i ≫ ψ k)) (fun k => N (nG i ≫ φ k)) (fun k => jL k i)
      (fun k => by rw [pt_of_eq (c₃ i k) z]; exact hJ _) (fun k => hN _) (fun k => mL k i))
  refine (val_of tM' mB z J' jM' hJ'e).symm.trans ?_
  exact alg ε (fun k => om w z J J' (mB ≫ ψ' k)) (fun k => Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k))
    (fun k i => Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i)) hQ (HM J J' hJ hJ') he₂

theorem gm_box_pull {X X' Y Y' Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (F : Fin j → (X' ⟶ X))
    {φ : Fin j → K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} (ρ : Fin j → (Y' ⟶ Y))
    (hψ : ∀ i k, φ' k ≫ F i = ρ i ≫ φ i k) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (r : Z ⟶ Y') (z : Z)
    (jj : K → Fin j → L.ι) (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ' jj) :
    gm r z (LB.wchart (LB.LinComb L F (fun _ => 1)) φ' jj)
      ((GeneratorPullback.boxGen L F φ' ε (fun i => GeneratorPullback.pullAlong L (F i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jj) =
      ∏ i, gm (r ≫ ρ i) z (LB.wchart L (φ i) (fun k => jj k i)) ((t i).s (fun k => jj k i)) := by
  refine (GlobalTheory.BoxSymmetry.gm_boxGen L F φ' ε _ r z jj h).trans (Finset.prod_congr rfl fun i _ => ?_)
  have hz : r z ∈ (L.pull (F i)).wchart φ' (fun k _ => jj k i) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (LB.wchart_le L F (jj k) i (Set.mem_iInter.1 h k))
  exact gm_res_pull r (ρ i) z _ hz _

theorem maps_box_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y Y₀ Z : Scheme.{0}}
    {φ' : K → (Y ⟶ B')} {φ : Fin j → K → (Y₀ ⟶ B)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, om w y J J' (r ≫ φ' a) ^ ε a) * val t' r y J' = ∏ i, val (t i) (r ≫ ρ i) y J := by
  have m1 : r y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i)
  have m2 : r y ∈ LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := hJ'.mem φ' r
  have e := congrArg (gm r y _) (H (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)))
  dsimp only at e
  have m12 : r y ∈ (((M.LinComb pr fun _ => 1).LinComb φ' ε).U fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
      (M'.LinComb φ' ε).U fun a => J' (r ≫ φ' a) := ⟨m1, m2⟩
  rw [map_mul, gm_res r y _ m12, gm_res r y _ m12] at e
  have e2 := (gm_box_pull M pr ρ hψ t r y _ m1).symm.trans
    (e.trans (congrArg (· * _) (gm_linCombIso w φ' ε r y _ _ m12)))
  rw [Finset.prod_congr rfl fun i _ => val_of (t i) (r ≫ ρ i) y J (fun k => J ((r ≫ φ' k) ≫ pr i))
    (fun k => congrArg J (by simp only [Category.assoc, hψ]))]
  exact e2.symm

theorem corr_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {ε : K → ℤ} {φ₀ : Fin j → K → (T ⟶ B)} {φ₁ : Fin j → K → (T₁ ⟶ B)} {φ₀' : K → (T' ⟶ B')} {φ₁' : K → (T₁' ⟶ B')}
    {t₀ : ∀ i, LB.Gen (LB.LinComb M (φ₀ i) ε)} {t₁ : ∀ i, LB.Gen (LB.LinComb M (φ₁ i) ε)}
    {t₀' : LB.Gen (LB.LinComb M' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb M' φ₁' ε)}
    {h₀ : Fin j → (T' ⟶ T)} {h₁ : Fin j → (T₁' ⟶ T₁)} {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (hm : ∀ i, m' ≫ h₁ i = h₀ i ≫ m)
    (c₀ : ∀ i k, φ₀' k ≫ pr i = h₀ i ≫ φ₀ i k) (c₁ : ∀ i k, φ₁' k ≫ pr i = h₁ i ≫ φ₁ i k)
    (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : LB.Gen.Maps (LB.linCombIso w φ₀' ε) t₀'
      (GeneratorPullback.boxGen M pr φ₀' ε (fun i => GeneratorPullback.pullAlong M (pr i) (h₀ i) (φ₀ i) ε φ₀' (c₀ i) (t₀ i))))
    (H₁ : LB.Gen.Maps (LB.linCombIso w φ₁' ε) t₁'
      (GeneratorPullback.boxGen M pr φ₁' ε (fun i => GeneratorPullback.pullAlong M (pr i) (h₁ i) (φ₁ i) ε φ₁' (c₁ i) (t₁ i))))
    (H : ∀ i, LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ (t₁ i) m) (t₀ i)) :
    LB.Gen.Corr M' _ _ _ _ (LB.pullGen M' _ _ t₁' m') t₀' := by
  refine corr_of_val hM' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at hM y
  have A₁ := maps_box_val w c₁ t₁' t₁ H₁ m' y hJ hJ'
  have A₀ := maps_box_val w c₀ t₀' t₀ H₀ (𝟙 _) y hJ hJ'
  simp only [Category.id_comp, c', hm] at A₁ A₀
  have A₂ : ∏ i, val (t₁ i) (h₀ i ≫ m) y J = ∏ i, val (t₀ i) (h₀ i) y J :=
    Finset.prod_congr rfl fun i _ => (val_pull hJ (t₁ i) m (h₀ i)).symm.trans (val_corr hJ (H i) (h₀ i))
  rw [val_pull hJ' t₁' m' (𝟙 _), Category.id_comp]
  exact _root_.mul_left_cancel (A₁.trans (A₂.trans A₀.symm))

end GlobalTheory.PowUnif
end
end
