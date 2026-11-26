module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecCubeExactAtZeroAndOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secCube_exactAt_zero_and_one (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hD : ⨆ i, D i = ⊤) :
    (cubeComplex (secCube f M D)).ExactAt 0 ∧ (cubeComplex (secCube f M D)).ExactAt 1 := by
  let O : κ → Y.Opens := fun a => ⨅ i ∈ ({a} : Finset κ), D i
  have hOD (a : κ) : O a = D a := by simp [O]
  have hO (a : κ) : O a ≤ ⨅ i ∈ (∅ : Finset κ), D i :=
    iInf_le_iInf_of_subset D (Finset.empty_subset _)
  have hc : (⨅ i ∈ (∅ : Finset κ), D i) ≤ ⨆ a, O a := by
    simp only [hOD, hD, le_top]
  constructor
  · rw [cubeComplex_exactAt_zero_iff]
    intro s t h
    exact SecOnR.ext_of_cover f O hO hc fun a => congrFun h ⟨{a}, Finset.card_singleton a⟩
  · rw [cubeComplex_exactAt_one_iff]
    intro x
    constructor
    · intro hx
      have key (a b : κ) (hab : a < b) {W : Y.Opens} (ha : W ≤ O a) (hb : W ≤ O b) :
          SecOnR.restrict f M ha (x ⟨{a}, Finset.card_singleton a⟩) =
            SecOnR.restrict f M hb (x ⟨{b}, Finset.card_singleton b⟩) := by
        have e := Cube.d_one_apply_pair (secCube f M D) x hab
        rw [hx] at e
        have e' := (sub_eq_zero.1 e.symm).symm
        have hW : W ≤ ⨅ i ∈ ({a, b} : Finset κ), D i := by
          rw [hOD] at ha hb
          rw [Finset.iInf_insert, Finset.iInf_singleton]
          exact le_inf ha hb
        have e'' := congrArg (SecOnR.restrict f M hW) e'
        exact (SecOnR.restrict_restrict f _ _ _).symm.trans
          (e''.trans (SecOnR.restrict_restrict f _ _ _))
      obtain ⟨t, ht, -⟩ := SecOnR.existsUnique_glue f O hO hc
        (fun a => x ⟨{a}, Finset.card_singleton a⟩) fun a b => by
          rcases lt_trichotomy a b with h | rfl | h
          · exact key a b h _ _
          · rfl
          · exact (key b a h _ _).symm
      refine ⟨t, funext ?_⟩
      rintro ⟨s, hs⟩
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      exact ht a
    · rintro ⟨t, rfl⟩
      have := Cube.d_zero_apply (secCube f M D) ((Cube.termZeroEquiv _).symm t)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact Cube.d_d _ 0 _

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAt
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.KeyKa

theorem secCube_tw_exactAt_of_veryAmpleBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  intro R _ _ Y f H m s M hH hM hv
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hfin, hφ⟩ :=
    GlobalTheory.AbLaw.exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨n₀, hn⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hfin
  refine ⟨n₀, fun t ht p => ?_⟩
  have h01 := secCube_exactAt_zero_and_one R Y f (tw M H t) (Fin (m + 1))
    (fun i => Out.nonzeroLocus (s i)) hv.1
  match p with
  | 0 => exact h01.1
  | 1 => exact h01.2
  | p + 2 =>
    obtain ⟨φ, hb⟩ := hφ t
    have := isIso_cechComplexMap φ hb
    rw [← cechComplex_exactAt_succ_iff_cube]
    exact ((cechComplex_exactAt_succ_iff_cube _ p).2 (hn t ht (p + 2))).of_iso
      (asIso (cechComplexMap φ))

end GlobalTheory.KeyKa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_cubeTotalComplex_exactAt : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  first | exact @GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy | exact GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy | (intros; apply GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish

theorem exactAt_of_trace {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by
  have dφ : ∀ q (x : Cube.Term A q), Cube.d B q (fun s => φ s.1 (x s)) = fun t => φ t.1 (Cube.d A q x t) :=
    fun q x => funext fun t => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Cube.d_apply, map_sum, map_zsmul, hφ]
  have dT : ∀ q (x : Cube.Term B q), Cube.d B q (fun s => T s.1 (x s)) = fun t => T t.1 (Cube.d B q x t) :=
    fun q x => funext fun t => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Cube.d_apply, map_sum, map_zsmul, hT]
  rcases p with _ | p
  · rw [cubeComplex_exactAt_zero_iff'] at H ⊢
    intro x y hxy
    have : (fun s => φ s.1 (x s) : Cube.Term B 0) = fun s => φ s.1 (y s) := H (by rw [dφ, dφ, hxy])
    exact funext fun s => inj _ (congrFun this s)
  · rw [cubeComplex_exactAt_succ_iff] at H ⊢
    intro x
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ Cube.d_d A p y⟩
    obtain ⟨y, hy⟩ := (H (fun s => φ s.1 (x s))).1 (by
      rw [dφ, hx]; exact funext fun t => map_zero _)
    choose z hz using fun s : {s : Finset κ // s.card = p} => himg s.1 (y s)
    have key : Cube.d A p z = (n : R) • x := funext fun t => inj _ (by
      have e := congrFun (dφ p z) t
      have e' := congrFun (dT p y) t
      simp only [hz] at e
      rw [← e, e', hy, htr, Pi.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    obtain ⟨u, hu⟩ := hn.exists_left_inv
    exact ⟨u • z, by rw [map_smul, key, smul_smul, hu, one_smul]⟩

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)

theorem le_deck {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) (j : (M.pull f).ι) :
    W' ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U j) := fun y hy =>
  ⟨e hy.1, mem_pull.2 (by
    have := mem_pull.1 hy.2
    rwa [← hτ] at this)⟩

def act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) :
    SecOn (M.pull f) W →+ SecOn (M.pull f) W' where
  toFun s := GlobalTheory.LB.mkSec (fun j => pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j)) fun i j => by
    have e₀ : W' ⊓ (M.pull f).U i ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U i ⊓ (M.pull f).U j) :=
      le_deck f M hτ (le_deck f M hτ e i) j
    have h := congrArg (pb τ e₀) (GlobalTheory.LB.coord_mem s i j)
    have g₁ : ∀ (O : Y.Opens) (e : O ≤ (M.pull f).U i ⊓ (M.pull f).U j),
        rs Y e ((M.pull f).g i j).val = pb f (pre_pull M f (i PUnit.unit) (j PUnit.unit) e)
          (M.g (i PUnit.unit) (j PUnit.unit)).val :=
      fun O e => rs_pull_g M f (i PUnit.unit) (j PUnit.unit) (W := O) e
    exact (rs_pb τ _ _ _).trans ((pb_rs τ e₀ _ _).symm.trans (h.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ((congrArg (pb τ e₀) (g₁ _ _)).trans ((pb_pb τ f _ e₀ _).trans
        ((pb_congr hτ _ _).trans (g₁ _ _).symm))) ((pb_rs τ e₀ _ _).trans (rs_pb τ _ _ _).symm)))))
  map_zero' := GlobalTheory.LB.sec_ext fun j => map_zero (pb τ _)
  map_add' s t := GlobalTheory.LB.sec_ext fun j => map_add (pb τ _) _ _

theorem coord_act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W)
    (s : SecOn (M.pull f) W) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (act f M hτ e s) j = pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j) := rfl

theorem act_restrict {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W' ≤ τ ⁻¹ᵁ W')
    (h : W' ≤ W) (s : SecOn (M.pull f) W) :
    act f M hτ e' (SecOn.restrict _ h s) = SecOn.restrict _ h (act f M hτ e s) :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, SecOn.coord_restrict, SecOn.coord_restrict, coord_act, pb_rs, rs_pb]

theorem act_act {τ σ ρ : Y ⟶ Y} (hτ : τ ≫ f = f) (hσ : σ ≫ f = f) (hρ : ρ ≫ f = f) (H : τ ≫ σ = ρ)
    {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W ≤ σ ⁻¹ᵁ W) (e'' : W ≤ ρ ⁻¹ᵁ W) (s : SecOn (M.pull f) W) :
    act f M hτ e (act f M hσ e' s) = act f M hρ e'' s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_act, coord_act, pb_pb, pb_congr H]

theorem coord_pullLE {V : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (SecOn.pullLE M f V W e s) j =
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V j)) (GlobalTheory.LB.coord s (j PUnit.unit)) :=
  SecOn.coord_pullLE f e s j

theorem act_pullLE {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {V : X.Opens} {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W)
    (h : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) :
    act f M hτ e (SecOn.pullLE M f V W h s) = SecOn.pullLE M f V W h s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_pullLE, pb_pb, pb_congr hτ]

variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal


omit hτ in
theorem exists_fun (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) (s : Γ(Y, W))
    (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), pb (τ y) e s = s) : ∃! g : Γ(X, U), pb f e g = s := by
  obtain rfl := le_antisymm e e'
  simpa only [app_eq_pb] using hgal U s hs

theorem pb_injective (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) :
    Function.Injective (pb f e) := fun a _ hab =>
  (exists_fun f τ hgal U W e e' (pb f e a) (fun y _ => by rw [pb_pb, pb_congr (hτ y)])).unique rfl hab.symm

theorem pullLE_injective (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W) :
    Function.Injective (SecOn.pullLE M f V W e) := fun a b hab => GlobalTheory.LB.sec_ext fun i => by
  have h := (coord_pullLE f M e a (fun _ => i)).symm.trans
    ((congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) hab).trans (coord_pullLE f M e b (fun _ => i)))
  exact pb_injective f τ hτ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
    (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) h

theorem exists_pullLE (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W)
    (s : SecOn (M.pull f) W) (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), act f M (hτ y) e s = s) :
    ∃ x, SecOn.pullLE M f V W e x = s := by
  have inv : ∀ y, W ≤ τ y ⁻¹ᵁ W := fun y => by
    obtain rfl := le_antisymm e e'
    rw [← Scheme.Hom.comp_preimage, hτ]
  have H : ∀ i : M.ι, ∃ g : Γ(X, V ⊓ M.U i),
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V (fun _ => i))) g =
        GlobalTheory.LB.coord s (fun _ => i) := fun i =>
    (exists_fun f τ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
      (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) _ fun y _ =>
      congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) (hs y (inv y))).exists
  choose g hg using H
  refine ⟨GlobalTheory.LB.mkSec g fun i j => ?_, GlobalTheory.LB.sec_ext fun j => (coord_pullLE f M e _ j).trans (hg _)⟩
  have e₀ : W ⊓ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
    fun y hy => ⟨⟨e hy.1.1, mem_pull.1 hy.1.2⟩, mem_pull.1 hy.2⟩
  apply pb_injective f τ hτ hgal (V ⊓ M.U i ⊓ M.U j) _ e₀
    (fun y hy => ⟨⟨e' hy.1.1, mem_pull.2 hy.1.2⟩, mem_pull.2 hy.2⟩)
  have h := GlobalTheory.LB.coord_mem s (fun _ => i) (fun _ => j)
  rw [← hg, ← hg] at h
  exact (pb_rs f e₀ _ _).trans ((rs_pb f _ _ _).symm.trans (h.trans ((congrArg₂ (· * ·)
    ((rs_pull_g M f i j _).trans (pb_rs f e₀ _ _).symm)
    ((rs_pb f _ _ _).trans (pb_rs f e₀ _ _).symm)).trans (map_mul _ _ _).symm)))

theorem exactAt_of_pull [Group G] [Fintype G] (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    {R : Type} [CommRing R] (a : X ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ Spec (CommRingCat.of R))
    (hu : IsUnit ((Fintype.card G : ℕ) : R)) {I : Type} [LinearOrder I] (D : I → X.Opens) (p : ℕ)
    (H : (cubeComplex (secCube b (M.pull f) (fun i => f ⁻¹ᵁ D i))).ExactAt p) :
    (cubeComplex (secCube a M D)).ExactAt p := by
  have inv : ∀ y (s : Finset I), (⨅ i ∈ s, f ⁻¹ᵁ D i) ≤ τ y ⁻¹ᵁ (⨅ i ∈ s, f ⁻¹ᵁ D i) := fun y s => by
    rw [← preimage_biInf, ← Scheme.Hom.comp_preimage, hτ]
  let φ : ∀ s : Finset I, SecOn M (⨅ i ∈ s, D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => (SecOn.pullLE M f _ _ (preimage_biInf D f s).ge).toAddMonoidHom
  let T : ∀ s : Finset I, SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => ∑ y, act f M (hτ y) (inv y s)
  have hT : ∀ s x, T s x = ∑ y, act f M (hτ y) (inv y s) x := fun s x => AddMonoidHom.finsetSum_apply _ _ _
  refine exactAt_of_trace _ _ φ T (fun {s t} h x => ?_) (fun {s t} h x => ?_)
    (fun s => pullLE_injective f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le) _ hu (fun s y => ?_)
    (fun s x => ?_) p H
  · exact (SecOn.pullLE_restrict f (iInf_le_iInf_of_subset D h) (preimage_biInf D f t).ge _).trans
      (SecOn.restrict_pullLE f (preimage_biInf D f s).ge (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) _).symm
  · change T t (SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x) =
      SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) (T s x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT t, hT s x, map_sum]
    exact Finset.sum_congr rfl fun y _ => act_restrict f M (hτ y) (inv y s) (inv y t) _ x
  · refine exists_pullLE f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le (T s y)
      fun z e => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT s y, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w =>
      act_act f M (hτ z) (hτ w) (hτ (z * w)) (hmul z w) e (inv w s) (inv (z * w) s) y
  · refine (hT s _).trans ((Finset.sum_congr rfl fun y _ =>
      act_pullLE f M (hτ y) (inv y s) (preimage_biInf D f s).ge x).trans ?_)
    rw [Finset.sum_const, Finset.card_univ]
    rfl

end GlobalTheory.TraceDescent

theorem GlobalTheory.exactAt_secCube_of_mul_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  intro L K _ _ P m N I _ _ D p hm _ H
  classical
  haveI := P.isAb.comm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hm (by rw [h, Nat.cast_zero])
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom m).ker
  have hc : Nat.card G = m ^ (2 * P.g) := (L.mulN _ P m hm1).2.2.2.2 K (𝟙 _) hm
  haveI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega))
  haveI : Fintype G := Fintype.ofFinite G
  have hgal := GlobalTheory.torsion_invariant_descends (fun S _ P n hn =>
    have h := L.mulN S P n hn
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P m hm
  refine GlobalTheory.TraceDescent.exactAt_of_pull (Out.mulA P.A m).left N (G := G)
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
    (fun U f hf => hgal U f fun y hy e => hf ⟨y, hy⟩ e) (fun y z => ?_) _ _ ?_ D p H
  · have hy : y.1 ^ m = 1 := y.2
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hc, Nat.cast_pow]
    exact (IsUnit.mk0 _ hm).pow _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExactAtSectionCubeOfMulPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

theorem _root_.GlobalTheory.T.exactAt_sectionCube_of_mul_pullback : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  first | exact @GlobalTheory.exactAt_secCube_of_mul_pull | exact GlobalTheory.exactAt_secCube_of_mul_pull | (intros; apply GlobalTheory.exactAt_secCube_of_mul_pull <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.PolVanishing

variable {X : Scheme.{0}} {L : LB X}

theorem lbIso_pw_tw (hL : L.IsLB) (b N t : ℤ) :
    LBIso (AbLaw.pw L (b + N * t)) (tw (AbLaw.pw L b) (AbLaw.pw L N) t) := by
  refine lbIso_of_chartPull ⟨fun i => (i, i), fun i y hy => ⟨hy, hy⟩, fun y i j hi hj => ?_⟩
    (isLB_tw (isLB_pw hL b) (isLB_pw hL N) t)
  refine Eq.trans ?_ (gm_div (AbLaw.pw (AbLaw.pw L N) (-t)) (AbLaw.pw L b) (𝟙 X) y (i, i) (j, j)
    ⟨⟨hi, hi⟩, hj, hj⟩).symm
  change gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ (b + N * t)) =
    gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ b) * (gm (𝟙 X) y (L.U i ⊓ L.U j) ((L.g i j ^ N) ^ (-t)))⁻¹
  rw [← map_inv, ← map_mul, zpow_neg, inv_inv, ← zpow_mul, ← zpow_add]

theorem lbIso_pull_pw (μ' : X ⟶ X) (d l : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1])) (hα : α.IsGen) :
    LBIso ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) := by
  let A := LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1]
  have le : ∀ p : L.ι × (PUnit → L.ι), L.U p.1 ⊓ ((AbLaw.pw L l).pull μ').U p.2 ≤
      LB.wchart L (K := Fin 2) ![𝟙 X, μ'] ![p.1, p.2 PUnit.unit] := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hy.1, mem_pull.1 hy.2]
  refine gen_chartPull (A' := LB.div (AbLaw.pw L (d * l)) ((AbLaw.pw L l).pull μ')) (h := 𝟙 X)
    (A := AbLaw.pw A l) ⟨fun p => ![p.1, p.2 PUnit.unit], le, fun y p q hp hq => ?_⟩
    ⟨fun j => α.s j ^ l⟩ fun i j => ?_
  · refine (gm_div ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) (𝟙 X) y p q ⟨hp, hq⟩).trans ?_
    rw [gm_pull_g (AbLaw.pw L l) μ' (𝟙 X) y p.2 q.2 hp.2 hq.2]
    refine Eq.trans ?_ ((map_zpow _ _ l).trans (congrArg (· ^ l)
      (gm_linComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1] (𝟙 X) y _ _ (le p hp) (le q hq)))).symm
    rw [Fin.prod_univ_two]
    change gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1 ^ (d * l)) *
        (gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit) ^ l))⁻¹ =
      (gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ d *
        gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ (-1 : ℤ)) ^ l
    rw [map_zpow, map_zpow, mul_zpow, zpow_neg_one, inv_zpow, zpow_mul]
  · have h := congrArg (· ^ l) (hα i j)
    simp only [mul_zpow, ← map_zpow] at h
    exact h

variable {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)}

theorem exactAt_of_lbIso {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (h : LBIso M M')
    {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M' D)).ExactAt p := by
  obtain ⟨w, hw⟩ := h
  exact hp.of_iso ((cubeFunctor κ R).mapIso (secCubeCongr f D hM hM' w hw))

theorem exactAt_of_affine_covers [IsSeparated f] {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {κ' : Type} [LinearOrder κ'] [Fintype κ'] {D' : κ' → X.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hD' : ∀ i, IsAffineOpen (D' i)) (hc' : ⨆ i, D' i = ⊤) {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M D')).ExactAt p := by
  match p with
  | 0 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').1
  | 1 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').2
  | p + 2 =>
    rw [← cechComplex_exactAt_succ_iff_cube, HomologicalComplex.exactAt_iff_isZero_homology,
      ModuleCat.isZero_iff_subsingleton] at hp ⊢
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers R X f M κ D κ' D' hM inferInstance
      hD hc hD' hc' (p + 1)
    exact @Equiv.subsingleton _ _ e.symm.toEquiv hp

theorem exists_forall_le_exactAt [IsNoetherianRing R] (hL : L.IsLB) {N : ℤ} (hN : 0 < N) {m : ℕ}
    {s : Fin (m + 1) → LB.Sec (AbLaw.pw L N)} (hs : VeryAmpleBy f (AbLaw.pw L N) s) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p,
      (cubeComplex (secCube f (AbLaw.pw L n) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  choose t₀ ht₀ using fun b : ℤ =>
    GlobalTheory.T.serre_vanishing_cubeTotalComplex_exactAt R X f (AbLaw.pw L N) m s (AbLaw.pw L b) (isLB_pw hL N) (isLB_pw hL b) hs
  obtain ⟨T, hT⟩ := ((Set.finite_Ico (0 : ℤ) N).image t₀).bddAbove
  refine ⟨T * N, fun n hn p => ?_⟩
  have h₁ : t₀ (n % N) ≤ n / N :=
    (hT ⟨n % N, ⟨Int.emod_nonneg n hN.ne', Int.emod_lt_of_pos n hN⟩, rfl⟩).trans
      (Int.le_ediv_of_mul_le hN hn)
  have h₂ := exactAt_of_lbIso (isLB_tw (isLB_pw hL _) (isLB_pw hL N) _) (isLB_pw hL _)
    (lbIso_pw_tw hL (n % N) N (n / N)).symm (ht₀ (n % N) (n / N) h₁ p)
  rwa [Int.emod_add_mul_ediv] at h₂

theorem exists_le_natCast_ne_zero (K : Type) [Field K] (B : ℕ) : ∃ m : ℕ, B ≤ m ∧ (m : K) ≠ 0 := by
  by_cases h : (B : K) = 0
  · exact ⟨B + 1, Nat.le_succ B, by simp [h]⟩
  · exact ⟨B, le_rfl, h⟩

theorem exactAt_secCube_pw : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens), 1 ≤ l → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ p, (cubeComplex (secCube P.A.hom (pw P.L l) D)).ExactAt p := by
  intro hLaw K _ _ P l I _ _ D hl hD hc p
  have := P.isAb.proper
  obtain ⟨N, hN, r, s, -, hs⟩ := veryAmpleBy_of_relAmple P.isLB P.ample (𝟙 P.A.left)
    (Category.id_comp _) P.isLB (lbIso_pull_id P.isLB).symm
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_exactAt P.isLB (by exact_mod_cast hN) hs
  obtain ⟨m, hm, hmK⟩ := exists_le_natCast_ne_zero K n₀.toNat
  have hm₁ : 1 ≤ m := Nat.pos_of_ne_zero fun h => hmK (by simp [h])
  have hle : n₀ ≤ (m : ℤ) ^ 2 * l := by
    have h₁ : n₀ ≤ m := by omega
    have h₂ : (1 : ℤ) ≤ m := by exact_mod_cast hm₁
    nlinarith [mul_nonneg (sq_nonneg (m : ℤ)) (sub_nonneg.2 hl)]
  obtain ⟨α, hα⟩ := hLaw.mulPull _ P m
  have := (hLaw.mulN _ P m hm₁).1
  refine GlobalTheory.T.exactAt_sectionCube_of_mul_pullback hLaw K P m _ I D p hmK (isLB_pw P.isLB l) ?_
  refine exactAt_of_lbIso (isLB_pw P.isLB _) (LB.isLB_pull (isLB_pw P.isLB l) _)
    (lbIso_pull_pw _ _ l α hα).symm ?_
  refine exactAt_of_affine_covers (isLB_pw P.isLB _) (fun i => (hs.2 i).1) hs.1
    (fun i => (hD i).preimage _) ?_ (hn₀ _ hle p)
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

end GlobalTheory.PolVanishing
