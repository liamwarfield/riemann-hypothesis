module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

def wtZeroSubring {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Subring Γ(H.left, V) where
  carrier := {u | HasWt i V u 0}
  one_mem' := hasWt_one i V
  zero_mem' := fun Y t g h h' => by rw [map_zero, map_zero, mul_zero]
  mul_mem' := fun {a b} ha hb Y t g h h' => by
    have h₁ := ha Y t g h h'
    have h₂ := hb Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h₁ h₂ ⊢
    rw [map_mul, map_mul, h₁, h₂]
  add_mem' := fun {a b} ha hb Y t g h h' => by
    rw [map_add (f := _), map_add (f := _), ha Y t g h h', hb Y t g h h', mul_add]
  neg_mem' := fun {a} ha Y t g h h' => by
    rw [map_neg, map_neg, ha Y t g h h', mul_neg]

theorem hasWt_zero_appLE_base {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) (a : Γ(S, ⊤)) :
    HasWt i V ((H.hom.appLE ⊤ V le_top).hom a) 0 := by
  intro Y t g h h'
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  refine (appLE_appLE _ H.hom (U := ⊤) le_top h' a).trans (Eq.trans ?_ (appLE_appLE _ H.hom (U := ⊤) le_top h a).symm)
  exact congrArg (fun ψ : Γ(S, ⊤) ⟶ Γ(Y.left, ⊤) => ψ.hom a)
    (appLE_of_eq ((Over.w _).trans (Over.w _).symm) _ _ _ _)

theorem mem_range_appLE_chart_iff {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (W : Y.Opens) (a : Fin (N + 1)) (h : W ≤ φ ⁻¹ᵁ chart R N a) (u : Γ(Y, W)) :
    u ∈ Set.range (φ.appLE (chart R N a) W h).hom ↔
      u ∈ Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R N a v
    have e := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (hi := h))
    refine (show _ = _ from e) ▸ ?_
    clear e
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))
  · intro hu
    have : Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) ≤ (φ.appLE (chart R N a) W h).hom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨v, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨_, appLE_appLE φ (PSpace.str R N) (le_top : chart R N a ≤ _) h v⟩
      · exact ⟨_, rfl⟩
    exact this hu

theorem Charts.exists_proper_image {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) (C : Charts Y)
    [Nonempty Y] : ∃ (B : Scheme.{0}) (p : B ⟶ Sp R) (q : Y ⟶ B), q ≫ p = f ∧ IsProper p ∧ IsAffineHom q ∧
      ∃ V : {i // C.wt i = C.c₀} → B.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q ⁻¹ᵁ V a,
        Function.Injective (q.appLE (V a) (C.W a) h.le).hom ∧ ∀ u,
          u ∈ Set.range (q.appLE (V a) (C.W a) h.le).hom ↔
          u ∈ Subring.closure (Set.range (f.appLE ⊤ (C.W a) le_top).hom ∪
            {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j}) := by
  have hne : Nonempty {i // C.wt i = C.c₀} := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ y))
    exact ⟨a⟩
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin {i // C.wt i = C.c₀}
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := by
    cases n with
    | zero => exact (e₀ hne.some).elim0
    | succ N => exact ⟨N, rfl⟩
  let e := e₀.symm
  have hC : IsCoordFamily (fun i : Fin (N + 1) => C.W (e i)) (fun i j => C.r (e i) (e j).1) :=
    { cover := (e.iSup_comp (g := C.W)).trans C.cover
      self := fun i => C.r_self _
      mul := fun i j k => (C.trans _ _ _).symm
      basicOpen_le := fun i j => (C.inter _ _).ge.trans inf_le_right }
  obtain ⟨φ, hφ, hpre, hr⟩ : ∃ φ : Y ⟶ PSpace R N, φ ≫ PSpace.str R N = f ∧
      ∃ hpre : ∀ i, φ ⁻¹ᵁ chart R N i = C.W (e i), ∀ i j,
        pullRatio φ (C.W (e i)) i (hpre i).ge j = C.r (e i) (e j).1 :=
    ⟨hC.toHom f, hC.toHom_str f, hC.toHom_preimage f, hC.pullRatio_toHom f⟩
  have haff : IsAffineHom φ := isAffineHom_of_forall_exists_isAffineOpen φ fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))
    exact ⟨_, hi, isAffineOpen_chart R N i, (hpre i).symm ▸ C.aff _⟩
  have hq : ∀ i, C.W (e i) = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i := fun i => by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι, hpre]
  have hV : ∀ i, IsAffineOpen (φ.imageι ⁻¹ᵁ chart R N i) := fun i => (isAffineOpen_chart R N i).preimage _
  have hcov : ⨆ i, φ.imageι ⁻¹ᵁ chart R N i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]
  have := isProper_str R N
  refine ⟨φ.image, φ.imageι ≫ PSpace.str R N, φ.toImage, by rw [Scheme.Hom.toImage_imageι_assoc, hφ],
    inferInstance, ?_, fun a => φ.imageι ⁻¹ᵁ chart R N (e₀ a),
    (e₀.iSup_comp (g := fun i => φ.imageι ⁻¹ᵁ chart R N i)).trans hcov, fun a => ?_⟩
  · refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
    exact ⟨_, hi, hV i, hq i ▸ C.aff _⟩
  · obtain ⟨i, rfl⟩ := e.surjective a
    have hi : e₀ (e i) = i := e₀.apply_symm_apply i
    beta_reduce
    rw [hi]
    refine ⟨hV i, hq i, ?_, fun u => ?_⟩
    · have key : ∀ (W : Y.Opens) (h : W = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i),
          Function.Injective (φ.toImage.appLE _ W h.le).hom := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        exact φ.toImage_app_injective ⟨_, isAffineOpen_chart R N i⟩
      exact key _ (hq i)
    · have hs : {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r (e i) j} =
          Set.range (pullRatio φ (C.W (e i)) i (hpre i).ge) := by
        ext v
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨e₀ ⟨j, hj⟩, (hr i _).trans (by rw [show e (e₀ ⟨j, hj⟩) = ⟨j, hj⟩ from e₀.symm_apply_apply _])⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, (e j).2, hr i j⟩
      rw [hs, ← hφ, ← mem_range_appLE_chart_iff]
      have hc : ∀ v, (φ.toImage.appLE _ _ (hq i).le).hom ((φ.imageι.app (chart R N i)).hom v) =
          (φ.appLE (chart R N i) _ (hpre i).ge).hom v := fun v => by
        rw [Scheme.Hom.app_eq_appLE, appLE_appLE]
        exact congrArg (fun ψ : _ ⟶ Γ(Y, C.W (e i)) => ψ.hom v) (appLE_of_eq φ.toImage_imageι _ _ _ _)
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨v, rfl⟩ := φ.imageι.app_surjective _ (isAffineOpen_chart R N i) w
        exact ⟨v, (hc v).symm⟩
      · rintro ⟨v, rfl⟩
        exact ⟨_, hc v⟩

theorem Charts.Torus.exists_proper_quotient :
    ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∃ (B : Over (Sp K)) (q : H ⟶ B), IsProper B.hom ∧ IsAffineHom q.left ∧ ∃ V : {i // C.wt i = C.c₀} → B.left.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q.left ⁻¹ᵁ V a, Function.Injective (q.left.appLE (V a) (C.W a) h.le).hom ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE (V a) (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hT
  have : Nonempty H.left := ⟨(η : 𝟙_ (Over (Sp K)) ⟶ H).left (⊥ : PrimeSpectrum K)⟩
  obtain ⟨B, p, q, hq, hp, ha, V, hV, h⟩ := C.exists_proper_image H.hom
  refine ⟨Over.mk p, Over.homMk q hq, hp, ha, V, hV, fun a => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h a
  refine ⟨h₁, h₂, h₃, fun u => ⟨fun hu => (h₄ u).2 (hT.gen a u hu), fun hu => ?_⟩⟩
  refine (Subring.closure_le (t := wtZeroSubring i (C.W a))).2 ?_ ((h₄ u).1 hu)
  rintro _ (⟨v, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hasWt_zero_appLE_base i _ v
  · exact hT.inv a j hj

end GlobalTheory.ZJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.SymLift

theorem odd_root_iff {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by
  constructor
  · rintro rfl
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_pow] at h'
    constructor
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -h'
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -(j • h')
  · rintro ⟨rfl, rfl⟩
    rw [← pow_mul, pow_succ, mul_div_cancel_left]

variable {O : Type} [CommRing O] (N : NumD O)

theorem tk_pow {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by
  have a := NumD.Gt.pow_s p.1.2 k p'.1.1.toAdd
  rw [N.mem_QT.1 p.2, NumD.io_s, ← N.QT_pow_b p'] at a
  rw [NumD.tk, mul_pow, ← a, mul_assoc]

theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have a := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b p''] at a
  change p.1.2.s p''.1.1.toAdd * p'.1.2.s p''.1.1.toAdd / N.θ (N.c p''.1.1.toAdd) p.1.2.b p'.1.2.b *
    cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  replace a := congrArg Additive.ofMul a
  apply Additive.ofMul.injective
  simp only [NumD.tk, ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a

theorem tk_one_left {k : ℕ} (p : N.QT k) : N.tk 1 p = 1 := by
  change 1 * cubN N.θ k 1 p.1.2.b 1 = 1
  rw [N.cub.N_one, one_mul]

theorem wQ_iff {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by
  obtain ⟨j, rfl⟩ := hk
  have e : N.wQ p = N.ψ p.1.1.toAdd * mulq N.θ N.σ (2 * j + 1) p.1.2.b /
      (N.tk p p / dbl N.θ N.σ p.1.2.b ^ (2 * j + 1)) ^ j := by
    have : (2 * j + 1 - 1) / 2 = j := by omega
    simp only [NumD.wQ, NumB.wS, NumD.tk, this]
  rw [e, odd_root_iff, eq_div_iff_mul_eq']
  have a := tk_pow N p p
  have b := (GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N 0 p.1.1.toAdd).1
  have c := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB (2 * j + 1) 0 p.1.2.b 1).2.2.1
  rw [← N.QT_pow_b p] at b
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c ⊢
  linear_combination (norm := module) a + b + c

theorem dbl_mul (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB 2 0 x y).2.1
  have c := N.cub.coc x y y x
  rw [N.cub.s12 (x * y), N.cub.s12 x y x, N.cub.s12 x (y * y), N.cub.s12 y y x] at c
  simp only [mulq, cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul, mul_one,
    N.cub.face, div_one, sq] at a
  rw [N.cub.s12 y y x] at a
  replace a := congrArg Additive.ofMul a
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a c ⊢
  linear_combination (norm := abel) c - a

theorem wQ_mul {k : ℕ} (hk : Odd k) (p p' : N.QT k) :
    N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (wQ_iff N hk p' _).1 rfl
  rw [← div_eq_iff_eq_mul', wQ_iff N hk]
  have k₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).2.2.2.1
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  constructor
  · have t₁ := tk_mul_left N p p' (p * p')
    have t₂ := tk_mul_left N p p' p
    have t₃ := tk_mul_left N p p' p'
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).1
    have w₃ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p').1
    have d := dbl_mul N p.1.2.b p'.1.2.b
    have e : (p * p').1.2.b = p.1.2.b * p'.1.2.b := rfl
    rw [e] at t₁ ⊢
    obtain ⟨j, rfl⟩ := hk
    have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [this]
    have a₁ := E a₁; have b₁ := E b₁; have k₁ := E k₁; have t₁ := E t₁; have t₂ := E t₂; have t₃ := E t₃
    have w₂ := E w₂; have w₃ := E w₃; have d := E d
    apply Additive.ofMul.injective
    simp only [NumD.wp, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ b₁ k₁ t₁ t₂ t₃ w₂ w₃ d ⊢
    linear_combination (norm := module) a₁ + b₁ - k₁ - t₁ - t₂ - t₃ + w₂ + w₃ + (2 * j + 1) • d
  · have t := tk_pow N p p'
    have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b p'.1.2.b).2.1
    have s := N.ψ_add p.1.1.toAdd p'.1.1.toAdd
    change _ = N.ψ (p.1.1.toAdd + p'.1.1.toAdd) * mulq N.θ N.σ k (p.1.2.b * p'.1.2.b)
    have a₂ := E a₂; have b₂ := E b₂; have k₁ := E k₁; have t := E t; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₂ b₂ k₁ t m s ⊢
    linear_combination (norm := module) a₂ + b₂ - ((k + 1) / 2) • k₁ + t - m - s

theorem wQ_inv {k : ℕ} (hk : Odd k) (p : N.QT k) : N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  rw [← eq_div_iff_mul_eq', eq_comm, wQ_iff N hk]
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have e : (p⁻¹).1.2.b = p.1.2.b⁻¹ := rfl
  constructor
  · have t₁ := tk_mul_left N p p⁻¹ p⁻¹
    have t₂ := tk_mul_left N p p⁻¹ p
    have w₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p⁻¹ p).1
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k 1 1 p).1
    have s := N.σ_inv p.1.2.b
    rw [mul_inv_cancel] at t₁ t₂ w₁
    rw [mul_one, left_eq_mul] at w₂
    rw [w₂] at w₁
    rw [tk_one_left, e] at t₁ t₂
    rw [N.cub.s01 p.1.2.b p.1.2.b p.1.2.b⁻¹, N.cub.s12 p.1.2.b p.1.2.b p.1.2.b⁻¹] at t₂
    rw [e]
    have a₁ := E a₁; have t₁ := E t₁; have t₂ := E t₂; have w₁ := E w₁; have s := E s
    apply Additive.ofMul.injective
    simp only [NumD.wp, dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ t₁ t₂ w₁ s ⊢
    linear_combination (norm := module) a₁ + t₁ - t₂ + w₁ - k • s
  · have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b 1).2.2.2
    have s := N.even p.1.1.toAdd
    rw [← N.QT_pow_b p] at s
    change _ = N.ψ (-p.1.1.toAdd) * mulq N.θ N.σ k p.1.2.b⁻¹
    have a₂ := E a₂; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a₂ m s ⊢
    linear_combination (norm := module) a₂ - m - s

theorem normalising_factor : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p :=
  fun _ _ N _ hk p p' => ⟨wQ_iff N hk p, wQ_mul N hk p p', wQ_inv N hk p⟩

end GlobalTheory.Ex.SymLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactorStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wQ_characterization_and_mul_relation : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  first | exact @GlobalTheory.Ex.SymLift.normalising_factor | exact GlobalTheory.Ex.SymLift.normalising_factor | (intros; apply GlobalTheory.Ex.SymLift.normalising_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ConeClosed

theorem exists_homogenisation {k J : Type} [Field k] (i : J) (P : MvPolynomial J k) :
    ∃ (n : ℕ) (Q : MvPolynomial J k), ∀ w : J → k, w i ≠ 0 →
      MvPolynomial.eval w Q = w i ^ n * MvPolynomial.eval (fun j => w j / w i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun w _ => by simp⟩
  | add P P' h h' =>
    obtain ⟨n, Q, hQ⟩ := h
    obtain ⟨n', Q', hQ'⟩ := h'
    refine ⟨n + n', MvPolynomial.X i ^ n' * Q + MvPolynomial.X i ^ n * Q', fun w hw => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.eval_X, hQ w hw, hQ' w hw]
    ring
  | mul_X P j h =>
    obtain ⟨n, Q, hQ⟩ := h
    refine ⟨n + 1, Q * MvPolynomial.X j, fun w hw => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, hQ w hw]
    field_simp
    ring

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem exists_point {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (hU : IsAffineOpen U) (φ : Γ(X, U) →+* k) (hφ : ∀ a, φ (constFn p U a) = a) :
    ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ f, GlobalTheory.ZH.valR x U f = φ f := by
  let ψ : Γ(X, U) ⟶ CommRingCat.of k := CommRingCat.ofHom φ
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (Spec.map ψ ≫ hU.fromSpec) U f = φ f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map ψ ≫ hU.fromSpec, ?_, hx, hv⟩
  rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ p), ← Spec.map_id]
  congr 1
  ext a
  rw [← GlobalTheory.Points.valR_constFn p _ U hx, hv, hφ]
  rfl

theorem valR_eval₂ {k J : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (x : Sp k ⟶ X) (hp : x ≫ p = 𝟙 _) (hx : ⊤ ≤ x ⁻¹ᵁ U) (r : J → Γ(X, U)) (P : MvPolynomial J k) :
    GlobalTheory.ZH.valR x U (MvPolynomial.eval₂Hom (constHom p U) r P) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) P := by
  have e : (CrdCalc.valHom x U hx).comp (MvPolynomial.eval₂Hom (constHom p U) r) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, ← CrdCalc.valR_eq]
      exact GlobalTheory.Points.valR_constFn_of_section p x hp U hx a
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, ← CrdCalc.valR_eq]
  rw [CrdCalc.valR_eq x U hx, ← e]
  rfl

theorem mem_cone_of_vanishing : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ v : J → k, (∃ i ∈ J₀, v i ≠ 0) → (∀ Pf ∈ MvPolynomial.vanishingIdeal k (cone p H s), MvPolynomial.eval v Pf = 0) → v ∈ cone p H s) := by
  intro k _ _ X p H J _ s J₀ hH him v ⟨i, hi, hvi⟩ hv
  obtain ⟨hU, r, hr, hgen⟩ := him.2 i hi
  let Φ : MvPolynomial J k →+* Γ(X, (Out.nonzeroLocus (s i))) := MvPolynomial.eval₂Hom (constHom p (Out.nonzeroLocus (s i))) r
  have hsurj : Function.Surjective Φ := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval fun j => v j / v i) := by
    intro P hP
    obtain ⟨n, Q, hQ⟩ := exists_homogenisation i P
    have hmem : MvPolynomial.X i * Q ∈ MvPolynomial.vanishingIdeal k (cone p H s) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro w ⟨x, hp, hw⟩
      rw [MvPolynomial.aeval_eq_eval, map_mul, MvPolynomial.eval_X]
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.nonzeroLocus (s i)) := (CrdCalc.crd_isUnit_iff i hw).1 (Ne.isUnit hwi)
      have e : (fun j => w j / w i) = fun j => GlobalTheory.ZH.valR x (Out.nonzeroLocus (s i)) (r j) := funext fun j => by
        rw [CrdCalc.crd_ratio hw (hr j) hx, mul_div_cancel_right₀ _ hwi]
      rw [hQ w hwi, e, ← valR_eval₂ p x hp hx r P, RingHom.mem_ker.1 hP, CrdCalc.valR_eq x (Out.nonzeroLocus (s i)) hx, map_zero,
        mul_zero, mul_zero]
    have h := hv _ hmem
    rw [map_mul, MvPolynomial.eval_X, hQ v hvi] at h
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hvi)).resolve_left (pow_ne_zero _ hvi)
  let φ : Γ(X, (Out.nonzeroLocus (s i))) →+* k := Φ.liftOfSurjective hsurj ⟨_, hker⟩
  have hφ : ∀ P, φ (Φ P) = MvPolynomial.eval (fun j => v j / v i) P := fun P =>
    RingHom.liftOfSurjective_comp_apply Φ hsurj ⟨_, hker⟩ P
  obtain ⟨x, hp, hx, hval⟩ := exists_point p hU φ fun a => by
    have := hφ (MvPolynomial.C a)
    rwa [MvPolynomial.eval_C, show Φ (MvPolynomial.C a) = constFn p (Out.nonzeroLocus (s i)) a from
      MvPolynomial.eval₂Hom_C _ _ _] at this
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists hH s x
  have hwi : w i ≠ 0 := ((CrdCalc.crd_isUnit_iff i hw).2 hx).ne_zero
  refine ⟨x, hp, ?_⟩
  have h := CrdCalc.crd_smul (Units.mk0 (v i / w i) (div_ne_zero hvi hwi)) hw
  convert h using 2 with j
  have h₁ := hφ (MvPolynomial.X j)
  rw [MvPolynomial.eval_X, show Φ (MvPolynomial.X j) = r j from MvPolynomial.eval₂Hom_X' _ _ _] at h₁
  rw [CrdCalc.crd_ratio hw (hr j) hx, hval, h₁, Units.val_mk0]
  field_simp

end GlobalTheory.ZH.ConeClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamily
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SS.WeakNeronDef

theorem fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

theorem isDominant_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (N : Model R A) : IsPullback N.j A.hom N.Y.hom (spMap (algebraMap R K)) := by
  have h := Over.w N.e.inv
  have : IsIso N.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map N.e.inv))
  refine IsPullback.of_iso (IsPullback.of_hasPullback N.Y.hom (spMap (algebraMap R K)))
    (asIso N.e.inv.left).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j]
  · simp [← h]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_dvr_point (N : Model R A) [IsIntegral N.Y.left] (hN : N.Irr) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ y ∈ N.sp, IsDiscreteValuationRing (N.Y.left.presheaf.stalk y) ∧
      Irreducible (((Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫
        N.Y.left.presheaf.germ ⊤ y trivial).hom ϖ) := by
  have := N.smooth
  have hs := IsPullback.of_hasPullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  set i := pullback.fst N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hi
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have := GlobalTheory.isReduced_of_smooth_of_isReduced
    (pullback.snd N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  have hr : Set.range i = N.sp := Set.ext fun x => DvrModel.mem_range_special hs x
  have : IrreducibleSpace ↥(pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
    have h1 : IrreducibleSpace (Set.range i) := by
      rw [hr]; exact Subtype.irreducibleSpace hN
    exact i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.surjective.irreducibleSpace
      i.isClosedEmbedding.isEmbedding.toHomeomorph.symm.continuous
  have := isIntegral_of_irreducibleSpace_of_isReduced
    (pullback N.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨i (genericPoint _), hr.le ⟨_, rfl⟩, DvrModel.isDiscreteValuationRing_stalk_generic hϖ hs⟩

end GlobalTheory.SS.WeakNeronDef

namespace GlobalTheory.SS

open WeakNeronDef

theorem exists_defAt_of_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  intro R K _ _ _ _ _ _ A _ I M hM N hN
  have := N.smooth
  have hK := isPullback_j N
  have : IsIntegral N.Y.left := DvrModel.isIntegral hK
  have : IsOpenImmersion N.j := DvrModel.isOpenImmersion_generic hK
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨y, hy, hd, hi⟩ := exists_dvr_point N hN hϖ
  let ψ := (Scheme.ΓSpecIso (.of R)).inv ≫ N.Y.hom.appTop ≫ N.Y.left.presheaf.germ ⊤ y trivial
  let R' : Type := N.Y.left.presheaf.stalk y
  let K' : Type := FractionRing R'
  letI : Algebra R R' := ψ.hom.toAlgebra
  let s : Sp R' ⟶ N.Y.left := N.Y.left.fromSpecStalk y
  have hs : s ≫ N.Y.hom = spMap (algebraMap R R') := fromSpecStalk_comp N.Y.hom y
  have hi' : Irreducible (algebraMap R R' ϖ) := hi
  have := DvrModel.isLocalization_away (K := K) hϖ
  have hu : IsUnit (((algebraMap R' K').comp (algebraMap R R')) ϖ) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R' K')).2 hi'.ne_zero).isUnit
  let k : K →+* K' := IsLocalization.Away.lift ϖ hu
  have hk : spMap k ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) := by
    rw [← Spec.map_comp, ← IsLocalization.Away.lift_comp ϖ (S := K) hu]; rfl
  have hw : (spMap (algebraMap R' K') ≫ s) ≫ N.Y.hom = spMap k ≫ spMap (algebraMap R K) := by
    rw [hk, Category.assoc, hs, ← Spec.map_comp]; rfl
  let a := hK.lift _ _ hw
  have ha : a ≫ N.j = spMap (algebraMap R' K') ≫ s := hK.lift_fst _ _ _
  have ha' : a ≫ A.hom = spMap k := hK.lift_snd _ _ _
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' (by
    rw [hϖ.maximalIdeal_eq, hi'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]) a
    (by rw [← Category.assoc, ha', hk])
  have := (M i).smooth
  have := (M i).sep
  obtain ⟨U, hU, g, h₁, h₂⟩ := spread_out_of_isGermInjective' N.Y.hom (M i).Y.hom (x := y) b (hb.trans hs.symm)
  refine ⟨i, y, hy, U, g, hU, h₂, ?_⟩
  let t : Sp R' ⟶ U.toScheme := U.fromSpecStalkOfMem y hU
  have ht : t ≫ U.ι = s := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hP := isPullback_morphismRestrict N.j U
  have hc : a ≫ N.j = (spMap (algebraMap R' K') ≫ t) ≫ U.ι := by rw [ha, Category.assoc, ht]
  let c := hP.lift _ _ hc.symm
  have hc₁ : c ≫ (N.j ⁻¹ᵁ U).ι = a := hP.lift_snd _ _ _
  have hc₂ : c ≫ (N.j ∣_ U) = spMap (algebraMap R' K') ≫ t := hP.lift_fst _ _ _
  have : IsDominant s := isDominant_fromSpecStalk _ _
  have := GlobalTheory.isDominant_spMap_of_isFractionRing R' K'
  have : IsDominant (c ≫ (N.j ⁻¹ᵁ U).ι ≫ N.j) := by
    rw [← Category.assoc, hc₁, ha]; infer_instance
  have : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c ((N.j ⁻¹ᵁ U).ι ≫ N.j)
  refine ext_of_isDominant_of_isSeparated (M i).Y.hom ?_ c ?_
  · simp only [Category.assoc, h₂, Over.id_left, Category.id_comp, Model.j_hom]
    rw [morphismRestrict_ι_assoc, Model.j_hom]
  · simp only [Over.id_left, Category.id_comp]
    rw [← Category.assoc, hc₂, ← Category.assoc, hc₁, ← hb', Category.assoc]
    exact congrArg _ h₁.symm

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamilyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelMapDefined_weakNeronFamily : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [IsIntegral A.left] (I : Type) (M : I → Model R A), WeakNeron M → ∀ N : Model R A, N.Irr → ∃ i, ∃ y ∈ N.sp, DefAt N (M i) (𝟙 A) y := by
  first | exact @GlobalTheory.SS.exists_defAt_of_weakNeron | exact GlobalTheory.SS.exists_defAt_of_weakNeron | (intros; apply GlobalTheory.SS.exists_defAt_of_weakNeron <;> assumption)
end
end
