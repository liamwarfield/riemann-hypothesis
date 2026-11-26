module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealEqCP

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Glue

open GlobalTheory.KS

variable {X Y : Scheme.{0}}

theorem map_eq_rsT {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    (Y.presheaf.map (homOfLE h).op).hom s = rsT s O := (rsT_of_le h s).symm

theorem rsT_pow' {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) (k : ℕ) : rsT (s ^ k) O = rsT s O ^ k := by
  rw [rsT_of_le h, rsT_of_le h, map_pow]

theorem le_wchart {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) {O : Y.Opens} (h : O ≤ m ⁻¹ᵁ L.U (c 0)) :
    O ≤ LB.wchart L (fun _ : Fin 1 => m) c := fun y hy =>
  Set.mem_iInter.2 fun x => by rw [Subsingleton.elim x 0]; exact h hy

theorem pullbackBundleChart_le_preimage {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => m) c ≤ m ⁻¹ᵁ L.U (c 0) := LB.wchart_le L _ c 0

theorem pbT_cocycle {L : LB X} (hL : L.IsLB) (m : Y ⟶ X) (a b c : L.ι) {O : Y.Opens}
    (h : O ≤ m ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    pbT m (L.g a b).val O * pbT m (L.g b c).val O = pbT m (L.g a c).val O := by
  have e := congrArg (fun u => pbT m u.val O) (hL.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, pbT_mul] at e
  rwa [pbT_rsT m inf_le_left h, pbT_rsT m (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    pbT_rsT m (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem linComb_g {L : LB X} (m : Y ⟶ X) (k : ℕ) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val O =
      pbT m (L.g (c 0) (c' 0)).val O ^ k := by
  have hle : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0)) :=
    fun y hy => ⟨pullbackBundleChart_le_preimage c hy.1, pullbackBundleChart_le_preimage c' hy.2⟩
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [rsT_pow' h]
  exact congrArg (· ^ k) ((congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res_pullU m hle (L.g (c 0) (c' 0)))).trans
    (rsT_pbT m hle h _))

theorem sec_rel {L : LB X} (m : Y ⟶ X) (k : ℕ) (τ : SecM m L k) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT (τ.f c) O = pbT m (L.g (c 0) (c' 0)).val O ^ k * rsT (τ.f c') O := by
  have e := congrArg (fun s => rsT s O) (τ.compat c c')
  simp only [map_eq_rsT] at e
  have h' : O ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := h
  rwa [rsT_rsT inf_le_left h', rsT_mul, linComb_g m k c c' h, rsT_rsT inf_le_right h'] at e

theorem exists_acts : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) →
    ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  intro R _ G _ _ n X m L hL dd hdd D h k τ

  have loc : ∀ i O (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)),
      rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
        op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
    intro i O hO f
    have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
      fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
      fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
    have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn G.hom hO r)
    have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]
  obtain ⟨F, hF⟩ : ∃ F : ∀ i, Γ(G.left, h.W i), ∀ i,
      F i = op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i)) :=
    ⟨_, fun _ => rfl⟩
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => le_wchart _ (h.le i)

  have Fc : ∀ i i', rsT (F i) (h.W i ⊓ h.W i') =
      pbT m (L.g (h.j i) (h.j i')).val (h.W i ⊓ h.W i') ^ k * rsT (F i') (h.W i ⊓ h.W i') := by
    intro i i'
    have hWc' : ∀ i, h.W i ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U (fun _ => h.j i) := hWc
    rw [hF, hF, loc i _ inf_le_left, loc i' _ inf_le_right, rsT_rsT (hWc' i) inf_le_left,
      rsT_rsT (hWc' i') inf_le_right,
      sec_rel m k τ (fun _ => h.j i) (fun _ => h.j i') (inf_le_inf (hWc i) (hWc i'))]
    exact h.glue k i i' _ le_rfl _
  have cov : ∀ V : G.left.Opens, V ≤ ⨆ i, V ⊓ h.W i := by
    intro V y hy
    have : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩

  have glue : ∀ c : Fin 1 → L.ι, ∃ t : Γ(G.left, LB.wchart L (fun _ : Fin 1 => m) c), ∀ i,
      rsT t (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) =
        pbT m (L.g (c 0) (h.j i)).val (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ^ k *
          rsT (F i) (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) := by
    intro c
    refine exists_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) (fun i => inf_le_left) (cov _) _
      fun i i' => ?_
    have hN1 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := inf_le_left
    have hN2 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i' := inf_le_right
    have hNW : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        h.W i ⊓ h.W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have hV : ∀ i, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun i y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i) ⊓ L.U (h.j i')) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, h.le i hy.1.2⟩, h.le i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_pow' hN1, rsT_pow' hN2, rsT_pbT m (hV i) hN1, rsT_pbT m (hV i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_pow' hNW, rsT_pbT m (show h.W i ⊓ h.W i' ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) from fun y hy => ⟨h.le i hy.1, h.le i' hy.2⟩) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  choose t ht using glue

  refine ⟨⟨t, fun c c' => ?_⟩, fun i => ?_⟩
  · have goal : rsT (t c) ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') =
        ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val *
          rsT (t c') ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
            (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') := ?_
    · exact (rsT_of_le inf_le_left (t c)).symm.trans (goal.trans (congrArg _ (rsT_of_le inf_le_right (t c'))))
    refine eq_of_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i)
      (fun i => inf_le_left) (cov _) _ _ fun i => ?_
    have a1 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have hV : ∀ c : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun c y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0) ⊓ L.U (h.j i)) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, pullbackBundleChart_le_preimage c' hy.1.2⟩, h.le i hy.2⟩
    have e' : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := inf_le_left
    have eL : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c := inf_le_left
    have eR : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c' := inf_le_right
    erw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', linComb_g m k c c' e',
      ← rsT_rsT inf_le_left a1 (t c), ← rsT_rsT inf_le_left a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_pow' a1, rsT_pow' a2, rsT_pbT m (hV c) a1, rsT_pbT m (hV c') a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  ·
    change rsT (t fun _ => h.j i) (h.W i) = _
    have a : h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i := le_inf (hWc i) le_rfl
    rw [← rsT_rsT inf_le_left a, ht, rsT_mul, rsT_pow' a,
      rsT_pbT m (show LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i))
        from fun y hy => ⟨pullbackBundleChart_le_preimage _ hy.1, h.le i hy.2⟩) a, rsT_rsT inf_le_right a, rsT_self,
      GlobalTheory.KS.AdjDlog.pbT_g_self hL m (h.j i) (h.le i), one_pow, _root_.one_mul, hF]

end GlobalTheory.Heat.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePowerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heatOperator_glued_pullbackBundlePower : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) → ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  first | exact @GlobalTheory.Heat.Glue.exists_acts | exact GlobalTheory.Heat.Glue.exists_acts | (intros; apply GlobalTheory.Heat.Glue.exists_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeries
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := (mul_right_cancel₀ hx ((mul_assoc _ _ _).trans e2)).symm
  exact ⟨k, hk, by rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]⟩

theorem root_mul {a b : ℂ} (ha : IsRoot1 a) (hb : IsRoot1 b) : IsRoot1 (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  exact ⟨n * m, Nat.mul_pos hn hm, by rw [mul_pow, pow_mul, ha, one_pow, mul_comm n, pow_mul, hb, one_pow, one_mul]⟩

theorem root_inv {a : ℂ} (ha : IsRoot1 a) : IsRoot1 a⁻¹ := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [inv_pow, ha, inv_one]⟩

theorem root_map (τ : ℂ ≃+* ℂ) {a : ℂ} (ha : IsRoot1 a) : IsRoot1 (τ a) := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [← map_pow, ha, map_one]⟩

theorem root_ne {a : ℂ} (ha : IsRoot1 a) : a ≠ 0 := by
  obtain ⟨n, hn, ha⟩ := ha
  rintro rfl
  rw [zero_pow hn.ne'] at ha
  exact zero_ne_one ha

theorem root_charOf {D : D7} (a : Recip D D.nd.Om) {R : Type} [CommRing R] (f : R →+* ℂ) {ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Rˣ}
    (h : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))) (x : (AE D)ˣ) :
    IsRoot1 ((GlobalTheory.SeriesTie.charOf a f ψ x : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := a.exists_sym x
  have hfin : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ψ σ ^ ψ.ker.index = 1 := by rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  refine ⟨_, Nat.pos_of_ne_zero hn, ?_⟩
  rw [charOf_eq a f h hσ hn h1, ← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]

theorem root_delta {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    IsRoot1 (((ρ.B i j b).de.chi x : Circle) : ℂ) := by
  rw [hρ.delta]
  refine root_charOf _ _ ?_ x
  have : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext σ
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [this]
  exact D.ntw.delta_open i

theorem conjFun_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
    {ph : Fin D.R.m → ℂ} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle}
    (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (H : HasTuples T R κ v₀ O ph j B ψ ψ') (hB : B.Good) {ω : PairRep (Vc D j) (Wc D j)}
    (hω : B.IsWeil 1 ω) (hψ : ψ.Good) (hψ' : ψ'.Good) (hQ : B.admitted ψ.Q) (hQ' : B.admitted ψ'.Q)
    (hδ : ∀ s, IsRoot1 ((B.de.chi s : Circle) : ℂ)) (hr : ∀ s, IsRoot1 ((ψ'.chi s : Circle) : ℂ))
    {c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W} {u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ} (hc : ExtC R j (inC (O j).c') (O j).c0' c)
    (hu : ∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) {τ : ℂ ≃+* ℂ} (h1 : FixBase T R j τ) (h2 : FixDat B τ)
    (h3 : ConjChar τ ψ ψ') {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {x x' : VsV D j ℂ} (hx : ConjVec j τ x x') :
    ∃ ζ : ℂ, IsRoot1 ζ ∧ ConjFun (O j) (κ j) τ ζ (ph j • B.gen ω ψ h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x)))
      (ph j • B.gen ω ψ' h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x'))) := by
  obtain ⟨T0', A', R', F', v₀', O', k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, t, t', ht, ht'⟩ := H
  obtain ⟨c', u', hc', hu', hio⟩ := k11 c u hc hu
  obtain ⟨ζ0, hζ0, K⟩ := GlobalTheory.ConjGen.conj_gen GlobalTheory.chartIndependence_unconditional D G Pl0 T0' A' T R' F' κ v₀' O' ph hn k1 k2 k3 k4 k5
    j k6 k7 c' hc' u' hu' B hB k8 ω hω τ (k9 τ h1) h2
  obtain ⟨s, hs, -⟩ := K ψ ψ' t t' hψ hψ' hQ hQ' ht ht' h3
  have hξ : IsRoot1 ((R'.xi t' s : Circle) : ℂ) := by
    rw [ht'.1, MonoidHom.mul_apply, Circle.coe_mul]
    exact root_mul (hδ s) (hr s)
  refine ⟨_, root_mul hζ0 hξ, k10 _ _ _ _ ?_⟩
  rw [← hio, ← hio]
  exact hs h hh x x' hx

theorem smul_apply_of {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (L : M →ₗ[ℂ] N) {ν a b : ℂ} {P Q : M}
    (h : ν • P = (a * b) • Q) : ν • L P = a • b • L Q := by
  rw [← map_smul, h, map_smul, mul_smul]

theorem rescale {X : Type} (τ : ℂ ≃+* ℂ) {ξ ζ : ℂ} (hξ : ξ ≠ 0) {Φ Φ' Ψ Ψ' : X → ℂ} (h : Ψ = ξ • Φ) (h' : Ψ' = ξ • Φ') {n : ℕ}
    {b : Fin n → ℂ} {f : Fin n → X → ℂ} (e1 : Φ = ∑ l, b l • f l) (e2 : ∑ l, τ (b l) • f l = fun x => ζ⁻¹ * Φ' x) :
    Ψ = ∑ l, (ξ * b l) • f l ∧ ∑ l, τ (ξ * b l) • f l = (τ ξ * ζ⁻¹ * ξ⁻¹) • Ψ' := by
  constructor
  · rw [h, e1, Finset.smul_sum]
    simp only [smul_smul]
  · have e3 : ∑ l, τ (ξ * b l) • f l = τ ξ • ∑ l, τ (b l) • f l := by
      simp only [map_mul, Finset.smul_sum, smul_smul]
    rw [e3, e2, h', smul_smul, inv_mul_cancel_right₀ hξ, mul_smul]
    rfl

end GlobalTheory.BigOn.Exp.TwConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayBasis

open GlobalTheory.InvFieldRing

theorem decompR {K : Type} [CommRing K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}
    (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  refine GlobalTheory.RelConstThickening.existsUnique_comb (W := ⊤) (fun U hU _ F => ?_) O le_top F
  refine GlobalTheory.RelConstThickening.existsUnique_of_isPushout (GlobalTheory.RelConstThickening.constHom q U) (ρ.app U)
    (GlobalTheory.RelConstThickening.constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [GlobalTheory.RelConstThickening.constHom]

section Field

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

def transl (u : epsR R ⟶ G) : epsR R ⊗ G ⟶ G := snd _ G * (fst _ G ≫ u)

def red (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (spMap_fst_comp R)

def fib (G : Over (Sp R)) : G ⟶ epsR R ⊗ G := lift (toUnit G ≫ red R) (𝟙 G)

theorem fib_snd : (fib G).left ≫ (snd (epsR R) G).left = 𝟙 _ := by
  rw [← Over.comp_left, fib, lift_snd]; rfl

theorem fib_fst : (fib G).left ≫ (fst (epsR R) G).left = G.hom ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  rw [← Over.comp_left, fib, lift_fst, Over.comp_left, Over.toUnit_left]; rfl

theorem fib_transl {u : epsR R ⟶ G} (hu : IsTangent u) : (fib G).left ≫ (transl u).left = 𝟙 _ := by
  have hs : red R ≫ u = η[G] := Over.OverMorphism.ext hu
  have hT : fib G ≫ transl u = 𝟙 G := by
    rw [transl, fib, MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.mul_one]
  rw [← Over.comp_left, hT]; rfl

theorem isPullback_thickR : IsPullback (snd (epsR R) G).left (fst (epsR R) G).left G.hom
    (spMap (algebraMap R (DualNumber R))) :=
  (IsPullback.of_hasPullback (epsR R).hom G.hom).flip

theorem surjective_fib : Surjective (fib G).left := by
  have hp : IsPullback (fib G).left G.hom (fst (epsR R) G).left (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    refine IsPullback.of_right ?_ fib_fst isPullback_thickR
    rw [fib_snd, spMap_fst_comp]
    exact IsPullback.id_horiz G.hom
  exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip (surjective_spMap_fst R)

theorem preimage_translR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) :
    (transl u).left ⁻¹ᵁ O = (snd (epsR R) G).left ⁻¹ᵁ O := by
  ext x
  obtain ⟨y, rfl⟩ := (surjective_fib (G := G)).surj x
  change ((fib G).left ≫ (transl u).left).base y ∈ O ↔ ((fib G).left ≫ (snd (epsR R) G).left).base y ∈ O
  rw [fib_transl hu, fib_snd]

theorem real_partR {u : epsR R ⟶ G} (hu : IsTangent u) (O : G.left.Opens) (f a b : Γ(G.left, O))
    (h : ((transl u).left.appLE O _ (preimage_translR hu O).ge).hom f =
      ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
        ((snd (epsR R) G).left.app O).hom b) : a = f := by
  have hjO : O ≤ (fib G).left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
    rw [← Scheme.Hom.comp_preimage, fib_snd, Scheme.Hom.id_preimage]
  have k := congrArg ((fib G).left.appLE _ _ hjO).hom h
  simp only [map_add (f := _), map_mul, Scheme.Hom.app_eq_appLE, appLE_appLE, appLE_constFn] at k
  rw [appLE_eq_of_eq (fib_transl hu) O O _ le_rfl, appLE_eq_of_eq fib_snd O O _ le_rfl, fib_fst] at k
  have h0 : (TrivSqZeroExt.fstHom R R R).toRingHom DualNumber.eps = 0 := by simp
  rw [constFn_spMap, h0] at k
  simp only [constFn, map_zero, zero_mul, add_zero] at k
  have hid : ∀ s : Γ(G.left, O), ((𝟙 G.left : G.left ⟶ G.left).appLE O O le_rfl).hom s = s := fun s =>
    (congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_eq_app (𝟙 G.left) (U := O))).trans rfl
  rw [hid, hid] at k
  exact k.symm

variable [IsCommMonObj G]

def pt (v : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G :=
  Over.homMk (tv v).left ((Over.w (tv v)).trans (Category.comp_id _))

theorem isTangent_pt (v : TanM (𝟙 (Sp R)) G) : IsTangent (pt v) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.scK_zero_iff]
  apply Over.OverMorphism.ext
  have h := congrArg (fun V => V.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  refine Eq.trans h ?_
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
  exact congrArg (· ≫ _) (Category.comp_id _)

theorem exists_isInv (v : TanM (𝟙 (Sp R)) G) : ∃ dd : Fld G.left, IsInv G v dd := by
  have hu := isTangent_pt v
  have hd := fun (O : G.left.Opens) (f : Γ(G.left, O)) =>
    decompR (isPullback_thickR (G := G)) O (((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f)
  choose ab hab huq using hd
  have huniq : ∀ O f (a b : Γ(G.left, O)),
      ((transl (pt v)).left.appLE O _ (preimage_translR hu O).ge).hom f =
        ((snd (epsR R) G).left.app O).hom a + constFn (fst (epsR R) G).left _ DualNumber.eps *
          ((snd (epsR R) G).left.app O).hom b → (ab O f).2 = b :=
    fun O f a b h => congrArg Prod.snd (huq O f (a, b) h).symm
  have hre : ∀ O f, (ab O f).1 = f := fun O f => real_partR hu O f _ _ (hab O f)
  have hee := fun O : G.left.Opens => constFn_eps_sq (fst (epsR R) G).left ((snd (epsR R) G).left ⁻¹ᵁ O)
  refine ⟨fun O f => (ab O f).2, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W _ f f'
    refine huniq W _ (f + f') _ ?_
    rw [map_add (f := _), hab W f, hab W f', hre, hre]
    simp only [map_add (f := _)]
    ring
  · intro W _ f f'
    refine huniq W _ (f * f') _ ?_
    rw [map_mul, hab W f, hab W f', hre, hre]
    simp only [map_add (f := _), map_mul]
    linear_combination (((snd (epsR R) G).left.app W).hom (ab W f).2 *
      ((snd (epsR R) G).left.app W).hom (ab W f').2) * hee W
  · intro W W' h _ f
    refine huniq W' _ (resG _ h f) _ ?_
    have h' : (snd (epsR R) G).left ⁻¹ᵁ W' ≤ (snd (epsR R) G).left ⁻¹ᵁ W := (snd (epsR R) G).left.preimage_mono h
    rw [appLE_res _ h h' (preimage_translR hu W).ge, hab W f, hre, map_add (f := _), map_mul, res_app _ h h',
      res_app _ h h', res_constFn]
  · intro S _ φ g₀ w O f hg hgO htr
    obtain ⟨g', v', hg', hv', rfl⟩ := htr
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let kA : tEpsG (g₀ ≫ G.hom) ⟶ epsR R := Over.homMk (spMap (dualMap φ)) (by
      change spMap (dualMap φ) ≫ spMap (algebraMap _ _) = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ G.hom
      rw [hg, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e])
    have hk : lift kA g' ≫ transl (pt v) = g' * v' := by
      unfold transl
      rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
      congr 1
      exact Over.OverMorphism.ext hv'.symm
    have hk2 : (lift kA g').left ≫ (snd (epsR R) G).left = spMap (algebraMap S (DualNumber S)) ≫ g₀ := by
      rw [← Over.comp_left, lift_snd, hg']
    have hk1 : (lift kA g').left ≫ (fst (epsR R) G).left = spMap (dualMap φ) := by
      rw [← Over.comp_left, lift_fst]
      rfl
    have hT : (g' * v').left = (lift kA g').left ≫ (transl (pt v)).left := by rw [← hk, Over.comp_left]
    have hx : ⊤ ≤ (lift kA g').left ⁻¹ᵁ ((snd (epsR R) G).left ⁻¹ᵁ O) := by
      intro y _
      show ((lift kA g').left ≫ (snd (epsR R) G).left).base y ∈ O
      rw [hk2]
      exact hgO (Set.mem_univ _)
    rw [hT, ← valR_appLE _ _ O _ (preimage_translR hu O).ge hx, hab O f, hre, valR_add _ _ hx, valR_mul _ _ hx,
      valR_constFn _ _ _ hk1 _ hx, Scheme.Hom.app_eq_appLE, valR_appLE _ _ _ _ _ hx, valR_appLE _ _ _ _ _ hx, hk2,
      valR_spMap_comp _ _ _ hgO, valR_spMap_comp _ _ _ hgO]
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add, ih]


open ReciprocityTheory.ChartRestriction.G.PullbackSections in
theorem exists_basis [IsLocalRing R] (hG : Smooth G.hom) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : Smooth ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show Smooth (pullback.snd _ _)
    infer_instance
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin n → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin n → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin n → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨n, ⟨Module.Basis.mk (v := b) ?_ ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Field

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ D O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have h2 : Smooth D.P.A.hom := D.P.isAb.smooth
  have hG : Smooth Y.H.hom := by
    rw [← Over.w Y.q]
    infer_instance
  obtain ⟨n, ⟨v⟩⟩ := exists_basis hG
  choose dd hdd using fun a => exists_isInv (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFieldsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_raynaudTangent_invariantFields : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayBasis.exists_basis_isInv | exact GlobalTheory.RayBasis.exists_basis_isInv | (intros; apply GlobalTheory.RayBasis.exists_basis_isInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

section General

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ}

def combF (dd : Fin n → Fld Z) (c : Fin n → R) : Fld Z :=
  fun W f => ∑ a, constFn s W (c a) * dd a W f

def quadF (dd : Fin n → Fld Z) (M : Matrix (Fin n) (Fin n) R) : Fld Z :=
  fun W f => ∑ a, ∑ b, constFn s W (M a b) * dd a W (dd b W f)

end General

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {Ω : Type} [CommRing Ω] [StarRing Ω] [Module Ω Q.X]
  {oa : Q.OAct Ω} (Y : Ray oa)

def IsTorField (F : Fld Y.H.left) (ℓ : Q.X → R) : Prop :=
  IsField ⊤ F ∧ (∀ W r, F W (constFn Y.H.hom W r) = 0) ∧
    (∀ (α : Q.X) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f →
      F W f = constFn Y.H.hom W (ℓ α) * f) ∧
    ∀ (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)),
      W ≤ Y.q.left ⁻¹ᵁ U → F W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * F W f

end Raynaud

end GlobalTheory.HeatMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
set_option autoImplicit false

noncomputable section

open Module TensorProduct GlobalTheory.DeRham

namespace GlobalTheory.PrincipalPolPairing

section Algebra

variable {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R' M'] {f : M →ₛₗ[algebraMap R R'] M'}

theorem exists_corr (hf : Function.Bijective (liftSemi f)) (h : Dual R M) :
    ∃ h' : Dual R' M', ∀ c, h' (f c) = algebraMap R R' (h c) := by
  let e := LinearEquiv.ofBijective _ hf
  let l : M →ₛₗ[algebraMap R R'] R' :=
    { toFun c := algebraMap R R' (h c), map_add' := by simp, map_smul' := by simp }
  refine ⟨liftSemi l ∘ₗ e.symm.toLinearMap, fun c ↦ ?_⟩
  have : f c = e (1 ⊗ₜ c) := (one_smul R' (f c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem ext_bc (hf : Function.Bijective (liftSemi f)) {N : Type*} [AddCommGroup N] [Module R' N]
    {u v : M' →ₗ[R'] N} (h : ∀ c, u (f c) = v (f c)) : u = v := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hf.2 c
  induction z with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

theorem ext_corr [Module.Finite R M] [Module.Projective R M] (hf : Function.Bijective (liftSemi f))
    {N : Type*} [AddCommGroup N] [Module R' N] {u v : Dual R' M' →ₗ[R'] N}
    (h : ∀ (y : Dual R M) (y' : Dual R' M'), (∀ c, y' (f c) = algebraMap R R' (y c)) → u y' = v y') :
    u = v := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  choose l hl using fun i : Fin n ↦ exists_corr hf (LinearMap.proj i ∘ₗ s)
  refine LinearMap.ext fun y' ↦ ?_
  have e : y' = ∑ i, y' (f (p (Pi.single i 1))) • l i := by
    refine ext_bc hf fun c ↦ ?_
    have hc : c = ∑ i, s c i • p (Pi.single i 1) := by
      conv_lhs => rw [← LinearMap.id_apply (R := R) c, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s c)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    conv_lhs => rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hl,
      LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]
    simp
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h _ _ (hl i)]

theorem subsingleton_of_fibres {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (AlgebraicClosure p.asIdeal.ResidueField ⊗[R] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have := h p
  have e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField p.asIdeal.ResidueField
    (AlgebraicClosure p.asIdeal.ResidueField) Q
  have h₁ := e.toEquiv.subsingleton
  have h₂ : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
    (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.rTensor_nontrivial _ _ _
  exact not_subsingleton _ h₁

end Algebra

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase GlobalTheory.DeRhamSheaf
open Limits (pullback)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Affine

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem isotropic (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg) P hP ψ hψ
  intro x hx y hy
  have := iso _ (push_mem_Fil (inl A A) hx) _ (push_mem_Fil (inr A A) hy)
  rwa [e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, sub_zero] at this

end Affine

end GlobalTheory.PrincipalPolPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_local {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (t : SAB H (Sp O)) (hprop : IsProper t.G.hom) (hpol : GlobalTheory.LN.PolAt t (Out.jK O)) :
    Out.RelAmple t.G t.PP.L := by
  by_cases hf : _root_.IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := GlobalTheory.PolLocal.exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := GlobalTheory.PolLocal.isIso_spMap _ (GlobalTheory.PolLocal.algebraMap_fractionRing_bijective O hf)
    exact (GlobalTheory.PolLocal.ample_kTriv_of_iso mu hA hK).1
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap V (FractionRing V))) tV
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.PolNormal.polAt_generic_pull ρ hρ mV hpol
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (GlobalTheory.PolLocal.isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := GlobalTheory.PolLocal.pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [GlobalTheory.PolLocal.spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, hA⟩ := GlobalTheory.PolNearAmple.relAmple_near_of_polAt E H O t hprop (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  obtain ⟨m₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  have e : spMap (RingHom.id O) = 𝟙 (Sp O) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact hA O (RingHom.id O) hu t (e ▸ m₀)

theorem relAmple_kTriv_of_generic {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => ?_
    have : q.asIdeal.IsPrime := q.isPrime
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨tO, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap S O)) t
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hA := relAmple_local tO (GlobalTheory.PolLocal.isProper_of_map m hp) (GlobalTheory.PolNormal.polAt_generic_pull _ hi m hg)
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at S q t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB
      ⟨w, hw⟩ hA
  exact ⟨hA, GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic E H S t hp hA hg⟩

theorem isProper_relAmple_kTriv_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab S x t' hx ⟨mx⟩
  have : CharZero R := algebraRat.charZero R
  have hf : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  generalize ∏ i, tt i = f at hf hab hx
  let Rf := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  obtain ⟨tf, ⟨mf⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap R Rf)) t
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 ((hab _).2 (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  obtain ⟨hA, hK⟩ := relAmple_kTriv_of_generic tf hpf hg
  have : IsOpenImmersion (spMap (algebraMap R Rf)) := by
    unfold spMap
    exact IsOpenImmersion.of_isLocalization f
  have hr : Set.range x ⊆ Set.range (spMap (algebraMap R Rf)) := by
    rintro _ ⟨s, rfl⟩
    exact hrange.ge (hx s)
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac mf mx (g := IsOpenImmersion.lift _ x hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  obtain ⟨w, hw, -⟩ := m'.lin
  exact ⟨GlobalTheory.PolLocal.isProper_of_map m' hpf,
    GlobalTheory.AmpleLocalBase.relAmple_baseChange m'.cart.1 tf.PP.isLB t'.PP.isLB ⟨w, hw⟩ hA,
    kTriv_pull m'.cart tf.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.AbLocusPol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmpleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedTriple_abelianLocus_proper_relAmple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus | exact GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus | (intros; apply GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X)
    (V : X.Opens) (h : f (closedPoint R) ∈ V) : ⊤ ≤ f ⁻¹ᵁ V := by
  intro p _
  have hp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.2.ne_top)
  exact hp.mem_open (f ⁻¹ᵁ V).2 h

end GlobalTheory.ChartDer
end
end
