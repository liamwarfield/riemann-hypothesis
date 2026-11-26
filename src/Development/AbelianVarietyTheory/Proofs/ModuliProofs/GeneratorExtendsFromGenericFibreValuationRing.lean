module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ValGenExtend

def genSec {X : Scheme.{0}} {L : LB X} (t : LB.Gen L) (ht : t.IsGen) : LB.Sec L :=
  ⟨fun i => (t.s i).val, fun i j => by
    have h := congrArg Units.val (ht i j)
    exact h⟩

theorem isGen_inv_of_eq {X : Scheme.{0}} {N : LB X} (t : LB.Gen N) (ht : t.IsGen)
    (g : ∀ a b, Γ(X, N.U a ⊓ N.U b)ˣ) (hg : ∀ a b, g a b = (N.g a b)⁻¹) :
    LB.Gen.IsGen (L := ⟨N.ι, N.U, g⟩) ⟨fun i => (t.s i)⁻¹⟩ := by
  intro a b
  have h : res (inf_le_left : N.U a ⊓ N.U b ≤ _) (t.s a)⁻¹ =
      g a b * res (inf_le_right : N.U a ⊓ N.U b ≤ _) (t.s b)⁻¹ := by
    rw [map_inv, map_inv, ht a b, _root_.mul_inv, hg]
  exact h

theorem exists_isGen_inv {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by
  refine ⟨⟨fun i => (t.s i)⁻¹⟩,
    isGen_inv_of_eq t ht ((⟨I, U, g'⟩ : LB X).pull j).g fun a b => ?_, fun i => ?_⟩
  · dsimp only [LB.pull, LB.LinComb]
    simp only [hg, map_inv, zpow_one, Finset.prod_inv_distrib]
    try rfl
  · exact (map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _))

theorem mem_basicOpen_of_mem {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have h := congrArg X.basicOpen (s.compat i k)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i k).isUnit] at h
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at h
  have hm : x ∈ L.U i ⊓ L.U k := ⟨hi, X.basicOpen_le _ hk⟩
  exact (h.ge (⟨hm, hm, hk⟩ : x ∈ _ ⊓ (_ ⊓ X.basicOpen (s.f k)))).2

theorem app_cst {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {X Y : Scheme.{0}}
    {f : X ⟶ Sp O} {j : Y ⟶ X} {g : Y ⟶ Sp K} (h : j ≫ f = g ≫ spMap φ) (U : X.Opens) (a : O) :
    (j.app U).hom (GlobalTheory.AbLaw.cst f U a) = GlobalTheory.AbLaw.cst g (j ⁻¹ᵁ U) (φ a) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 := congrArg (fun u => u.hom a) h1
  have h3 := congrArg (fun u => u.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)))
    (j.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  exact h3.trans (congrArg (rs Y le_top) h2)

theorem isUnit_of_mem_basicOpen {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}}
    (f : X ⟶ Sp O) {U : X.Opens} {a : O} {x : X} (hx : x ∈ X.basicOpen (GlobalTheory.AbLaw.cst f U a))
    (hf : f x = IsLocalRing.closedPoint O) : IsUnit a := by
  have h : X.basicOpen (GlobalTheory.AbLaw.cst f U a) =
      U ⊓ X.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) :=
    Scheme.basicOpen_res _ _ _
  have h1 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := (h.le hx).2
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  have h2 : a ∉ (f x).asIdeal := h1
  rw [hf] at h2
  exact not_not.1 h2

theorem triv_of_triv_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  intro O K _ _ _ _ _ _ _ _ X XK f j fK hp hsm hqc hgi M hM ⟨t, ht⟩
  have : IsDominant (spMap (algebraMap O K)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap O K))
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  have : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ hp
  obtain ⟨z⟩ : Nonempty XK := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (j z)
  have : Nonempty ((M.pull j).U fun _ => i₀) := ⟨⟨z, le_pull M j le_rfl hi₀⟩⟩
  obtain ⟨t', ht', htt⟩ := exists_isGen_inv M.g (GlobalTheory.AbLaw.pw M (-1)).g
    (fun a b => zpow_neg_one _) j t ht
  have hne : (t'.s fun _ => i₀).val ≠ 0 := fun h => by
    have h1 := htt i₀
    have : Nonempty (j ⁻¹ᵁ M.U i₀) := ⟨⟨z, hi₀⟩⟩
    rw [h, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, s, hc, hs, x, hx, hfx⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi M hM
    (genSec t ht) ⟨fun _ => i₀, (t.s fun _ => i₀).ne_zero⟩
  obtain ⟨c', s', hc', hs', x', hx', hfx'⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi _
    (isLB_pw hM (-1)) (genSec t' ht') ⟨fun _ => i₀, hne⟩
  have hprod : ∀ i : M.ι, (j.app (M.U i)).hom (s.f i * (show Γ(X, M.U i) from s'.f i)) =
      GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) (c * c') := fun i => by
    have h' : (j.app (M.U i)).hom (s'.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c' *
      rs XK (le_pull (GlobalTheory.AbLaw.pw M (-1)) j (W := M.U i) (i := i) le_rfl)
        (t'.s fun _ => i).val := hs' i
    have h : (j.app (M.U i)).hom (s.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c *
      rs XK (le_pull M j le_rfl) (t.s fun _ => i).val := hs i
    rw [map_mul, h, h', _root_.mul_mul_mul_comm, ← map_mul]
    exact (congrArg _ (htt i)).trans (_root_.mul_one _)
  have key : ∀ i, IsUnit (s.f i) := by
    rcases ValuationRing.isInteger_or_isInteger O (c * c') with ⟨a, ha⟩ | ⟨a, ha⟩
    · have e : ∀ i : M.ι, s.f i * (show Γ(X, M.U i) from s'.f i) = GlobalTheory.AbLaw.cst f (M.U i) a :=
        fun i => j.app_injective _ ((hprod i).trans (ha ▸ (app_cst _ hp.w _ a).symm))
      obtain ⟨y, hy, hy₁, hy₂⟩ := (f.isIrreducible_preimage f.isOpenMap
        (isIrreducible_singleton (x := IsLocalRing.closedPoint O))).isPreirreducible _ _
        (Out.nonzeroLocus s).isOpen (Out.nonzeroLocus s').isOpen ⟨x, hfx, hx⟩ ⟨x', hfx', hx'⟩
      obtain ⟨k, hk⟩ := exists_chart hM y
      have hu : IsUnit a := by
        refine isUnit_of_mem_basicOpen f (U := M.U k) (x := y) ?_ hy
        rw [← e k, Scheme.basicOpen_mul]
        exact ⟨mem_basicOpen_of_mem s hy₁ hk, mem_basicOpen_of_mem s' hy₂ (i := k) hk⟩
      exact fun i => isUnit_of_mul_isUnit_left ((e i).symm ▸ hu.map _)
    · intro i
      have e : s.f i * ((show Γ(X, M.U i) from s'.f i) * GlobalTheory.AbLaw.cst f (M.U i) a) = 1 := by
        refine j.app_injective _ ?_
        change (j.app (M.U i)).hom _ = (j.app (M.U i)).hom _
        rw [← _root_.mul_assoc, map_mul, hprod, app_cst _ hp.w, ← map_mul, ha,
          mul_inv_cancel₀ (mul_ne_zero hc hc'), map_one, map_one]
      exact IsUnit.of_mul_eq_one _ e
  exact ⟨⟨fun i => (key i).unit⟩, fun a b => Units.ext (s.compat a b)⟩

end GlobalTheory.ValGenExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_from_genericFibre_valuationRing : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  first | exact @GlobalTheory.ValGenExtend.triv_of_triv_generic | exact GlobalTheory.ValGenExtend.triv_of_triv_generic | (intros; apply GlobalTheory.ValGenExtend.triv_of_triv_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CubNondeg

theorem gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e

theorem descend_linComb {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (σ : LB.Gen (LB.LinComb M (fun k => m ≫ ψ k) ε)) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (LB.LinComb M ψ ε).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => m ≫ ψ k) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : K → M.ι, ∃ v : Γ(Y, LB.wchart M ψ j)ˣ, pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M ψ j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M ψ j) (hτ t)).mpr hx
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hM x
    have this := inv t x J hJ
    have e : ∀ k, τ t ≫ m ≫ ψ k = 𝟙 Y' ≫ m ≫ ψ k := fun k => by rw [Category.id_comp, ← Category.assoc, hτ]
    have g₁ := gen_trans hσ (τ t) x (le j hx') (hJ.mem (fun k => m ≫ ψ k) (τ t))
    have g₂ := gen_trans hσ (𝟙 Y') x (le j hx) (hJ.mem (fun k => m ≫ ψ k) (𝟙 Y'))
    refine (gm_res (τ t) x (le j) hx' _).trans ((g₁.trans (Eq.trans (congrArg₂ (· * ·) ?_ this) g₂.symm)).trans
      (gm_res (𝟙 Y') x (le j) hx _).symm)
    exact congrArg (fun q : K → (Y' ⟶ X) => ∏ k, gm (q k) x (M.U (j k) ⊓ M.U (J (q k))) (M.g (j k) (J (q k))) ^ ε k)
      (funext e)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : K → M.ι, m x ∈ LB.wchart M ψ j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun k => m ≫ ψ k) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M ψ ε (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem ratio_translate {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (n : ℕ)
    (x a y : A) (hx : x ^ n = 1) (hy : y ^ n = 1) (e : cubN θ n 1 x y = cubN θ n 1 y x) :
    cubN θ n 1 (a * y) x * (cubN θ n 1 x (a * y))⁻¹ = cubN θ n 1 a x * (cubN θ n 1 x a)⁻¹ := by
  have e₁ := GlobalTheory.UU.cubN_mul_left h n a y x
  have e₂ := h.N_add n 1 x a y
  rw [hy, h.face₂, _root_.one_mul] at e₁
  rw [hx, _root_.mul_one, h.face, _root_.one_mul, _root_.mul_one, h.s01 x, h.s12 a x] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ - a₂ - a₃

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem exists_sigma {T : Over S} (n : ℕ) (a x : T ⟶ A) (hx : x ^ n = 1) (φ : Fin 4 → (T.left ⟶ A.left))
    (hφ : φ = ![(a ^ n * x).left, (a ^ n).left, x.left, (1 : T ⟶ A).left]) :
    ∃ σ : LB.Gen (LB.LinComb L.L φ ![1, -1, -1, 1]), σ.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → val σ ρ.left z J =
        cubN (cubV c z J) n 1 (ρ ≫ a) (ρ ≫ x) * (cubN (cubV c z J) n 1 (ρ ≫ x) (ρ ≫ a))⁻¹ := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_cubN c (1 : T ⟶ A) a x n
  obtain ⟨t₂, g₂, v₂⟩ := GlobalTheory.WeilCube.exists_gen_torsion c n x a hx
  obtain ⟨σ, hσ, hv⟩ := exists_gen L.isLB (φ' := φ) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [hφ, mul_comm x a]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
    (LB.mulGen L.L _ _ _ _ t₁ (LB.invGen L.L _ _ t₂))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ (DVR.invGen_isGen _ _ _ _ g₂))
  refine ⟨σ, hσ, fun T' ρ z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, MonObj.comp_one]

theorem main : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : RigLB A) (c : CubicalStr A L) (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) (n : ℕ), (n : K) ≠ 0 → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Surjective ((𝟙 A) ^ n : A ⟶ A).left → ∀ x : Over.mk t ⟶ A, x ^ n = 1 → (∀ y : Over.mk t ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → Triv (Out.translDiff A L.L x) := by
  intro _ S A _ _ hA L c K _ _ t n hn h₁ h₂ h₃ x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => GlobalTheory.torsion_invariant_descends_fibre S A K t n hn hA.smooth h₁ h₂ h₃ V a
      (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.CubNondeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.exists_isPEL_of_tmap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S) (f : S' ⟶ S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g J a bas k o _ b ρ S S' s s' t t' τ f hs ht hP

  exact GlobalTheory.PELPull.isPEL_pull E H D g k J a bas o b ρ S S' s s' f t t' τ hs ht hP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCompare

private theorem pow_eq_one_of_three_pow_relations {G : Type*} [CommGroup G] (M : ℕ) (U0 Ax Ap A0 F R : G)
    (h1 : U0 ^ M * (Ax ^ M * Ap) = A0 ^ M * A0) (h2 : F ^ M * A0 = Ap * R ^ M) (h3 : A0 = R ^ M * R⁻¹) :
    (U0 * Ax * F * (R ^ M)⁻¹) ^ M = 1 := by
  rw [mul_pow, mul_pow, mul_pow, inv_pow, mul_inv_eq_one]
  apply mul_right_cancel (b := Ap * A0)
  calc U0 ^ M * Ax ^ M * F ^ M * (Ap * A0) = (U0 ^ M * (Ax ^ M * Ap)) * (F ^ M * A0) := by ac_rfl
    _ = (A0 ^ M * A0) * (Ap * R ^ M) := by rw [h1, h2]
    _ = (A0 ^ M * R ^ M) * (Ap * A0) := by ac_rfl
    _ = (R ^ M) ^ M * (Ap * A0) := by
      congr 1
      rw [h3, mul_pow, inv_pow, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]


open CommPairing in
theorem normalised_root_stalk {S : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {th : LB.Sec (LPow P.A P.L 1 T)} {x p : T ⟶ P.A} (hx : x ^ m = p)
    {fr : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => p.left) (fun _ => 1))}
    (hfr : IsTorsFrame P rig m p fr) {t v : Γ(T.left, ⊤)} (ht : IsValueAt P.A P.L 1 th p fr t)
    (a : ℤ) (ha : a = (m : ℤ) ^ 2) {s₁ s₂ : LB.Sec (LPow P.A P.L a T)}
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m a th s₁) {U : ThetaGrp P.A P.L a T}
    (hU : SymLift P.A P.L a (m ^ 2) x U) (hs₂ : IsActOf P.A P.L a U s₁ s₂)
    (h₃ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig a s₂ v) (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (m ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ t := by
  subst ha
  unfold IsActOf at hs₂
  obtain ⟨α, hα, hαn, htw⟩ := h₁
  obtain ⟨τ₀, -, hτ₀, hval⟩ := h₃
  obtain ⟨J, hJ, -⟩ := exists_good (L := P.L) P.isLB y (Empty.elim : Empty → (T.left ⟶ P.A.left)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hxM : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hx, hfr.1]
  have hR : ∀ k : ℕ, val rig T.hom y J ^ (k : ℤ) = val rig T.hom y J ^ k := fun k => zpow_natCast _ _
  have e1 := sval_valueAt hval hJ
  have e2 := sval_twist hs₂ (ptSecT P.A 1).left hJ
  have hpt : (ptSecT P.A (U.pt * 1)).left = (ptSecT P.A x).left := by rw [_root_.mul_one, hU.pt_eq]
  rw [pt_translT, hpt] at e2
  have e3 := sval_twist htw (ptSecT P.A x).left hJ
  rw [pt_mulT, hx] at e3
  have e4 := sval_valueAt ht hJ
  have e5 : val τ₀ (𝟙 _) y J = val rig T.hom y J ^ (m ^ 2) := by
    rw [val_corr hJ hτ₀, val_rigT rig _ hJ, ← Nat.cast_pow, hR]
  have F1 := frame_pow hG P hm hα hxM hU hJ
  rw [hx] at F1
  have F2 := torsFrame_pow hG P hα hfr hJ
  have F3 := val_corr hJ hαn (𝟙 _)
  rw [val_pull hJ, val_mul hJ, val_inv, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at F3
  have F3' : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (m ^ 2) * (val rig T.hom y J)⁻¹ := by
    rw [F3, zpow_one, ← hR, Nat.cast_pow]
  refine ⟨tval U (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val fr (𝟙 _) y J *
    (val rig T.hom y J ^ (m ^ 2))⁻¹, pow_eq_one_of_three_pow_relations _ _ _ _ _ _ _ F1 F2 F3', ?_⟩
  calc gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val τ₀ (𝟙 _) y J).val * (val τ₀ (𝟙 _) y J)⁻¹.val := by
        rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    _ = _ := by
        rw [← e1, e2, e3, e4, e5, show tval U (ptSecT P.A 1).left y J = val U.φ (ptSecT P.A 1).left y J from rfl]
        simp only [Units.val_mul]
        ring

end GlobalTheory.ThetaCompare

namespace GlobalTheory

end GlobalTheory
end
end
