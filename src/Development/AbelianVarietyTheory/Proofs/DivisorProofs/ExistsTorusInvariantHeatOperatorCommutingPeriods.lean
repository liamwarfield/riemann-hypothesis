module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerInvariantLifts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialDefectHeatOperatorMonomial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZeStatement
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
theorem _root_.GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  first | exact @GlobalTheory.InvCoefUniq.coef_eq_zero | exact GlobalTheory.InvCoefUniq.coef_eq_zero | (intros; apply GlobalTheory.InvCoefUniq.coef_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiffCoc

theorem rsT_rsT {Z : Scheme.{0}} {O₀ T : Z.Opens} (s : Γ(Z, O₀)) (hT : T ≤ O₀) (O : Z.Opens) (hO : O ≤ T) :
    rsT (rsT s T) O = rsT s O := by
  unfold rsT
  rw [dite_eq_left hT, dite_eq_left hO, dite_eq_left (hO.trans hT)]
  simp [resG]

theorem rsT_add {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_add (f := _)]

theorem rsT_sub {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_sub]

theorem isLift_mono {R : Type} [CommRing R] {G : Over (Sp R)} {D : R → R} {W W' : G.left.Opens} (h : W' ≤ W)
    {d : Fld G.left} (hd : IsLift G D W d) : IsLift G D W' d :=
  ⟨⟨fun O hO => hd.1.1 O (hO.trans h), fun O hO => hd.1.2.1 O (hO.trans h),
    fun O O' h' hO => hd.1.2.2 O O' h' (hO.trans h)⟩, fun O hO => hd.2 O (hO.trans h)⟩

theorem diff_isCoc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D J V d hlift hwt
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  have hl : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i := fun i i' =>
    (inf_le_left : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i)
  have hr : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i' := fun i i' =>
    (inf_le_right : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i')
  have hex : ∀ i i', ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i')), (∀ a, IsWt Y 0 _ (h a)) ∧
      ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V i') → ∀ f,
        d i O' f - d i' O' f = ∑ a, rsT (h a) O' * dd a O' f := fun i i' =>
    GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields R Dd.toPre O oa Y n v dd hdd (V i ⊓ V i') D (d i) (d i')
      (isLift_mono (hl i i') (hlift i)) (isLift_mono (hr i i') (hlift i'))
      (fun α V' hV' f hf => hwt i α V' (fun x hx => (hV' hx).1) f hf)
      (fun α V' hV' f hf => hwt i' α V' (fun x hx => (hV' hx).2) f hf)
  choose h hw hh using hex
  refine ⟨fun a i i' => h i i' a, fun a i j k => ?_, fun a i i' => hw i i' a, fun i i' W hW f => hh i i' W hW f⟩

  let U : J → Y.H.left.Opens := fun i => Y.q.left ⁻¹ᵁ V i
  let T := U i ⊓ U j ⊓ U k
  have hij : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V j) :=
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : T ≤ U i ⊓ U j)
  have hjk : T ≤ Y.q.left ⁻¹ᵁ (V j ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : T ≤ U j ⊓ U k)
  have hik : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : T ≤ U i ⊓ U k)
  let c : Fin n → Γ(Y.H.left, T) := fun b =>
    rsT (h i j b) T + rsT (h j k b) T - rsT (h i k b) T
  have hc : ∀ O, O ≤ T → ∀ f, ∑ b, rsT (c b) O * dd b O f = 0 := by
    intro O hO f
    have e : ∀ b, rsT (c b) O = rsT (h i j b) O + rsT (h j k b) O - rsT (h i k b) O := fun b => by
      simp only [c]
      rw [rsT_sub _ _ _ hO, rsT_add _ _ _ hO, rsT_rsT _ hij _ hO, rsT_rsT _ hjk _ hO, rsT_rsT _ hik _ hO]
    simp only [e, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← hh i j O (hO.trans hij) f, ← hh j k O (hO.trans hjk) f, ← hh i k O (hO.trans hik) f]
    ring
  have h0 := GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero R Y.H hsm n v dd hdd T c hc a
  simp only [c] at h0
  exact (sub_eq_zero.1 h0)

end GlobalTheory.DiffCoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycleStatement
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
theorem _root_.GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  first | exact @GlobalTheory.DiffCoc.diff_isCoc | exact GlobalTheory.DiffCoc.diff_isCoc | (intros; apply GlobalTheory.DiffCoc.diff_isCoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatInvLift

theorem rsT_of_le' {Z : Scheme.{0}} {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := dif_pos h

theorem rsT_rsT' {Z : Scheme.{0}} {O₀ O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Z, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le' h₁, rsT_of_le' h₂, rsT_of_le' (h₂.trans h₁), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT' {Z X : Scheme.{0}} (m : Z ⟶ X) {O₀ : X.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ m ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(X, O₀)) : rsT (pbT m s O₁) O₂ = pbT m s O₂ := by
  rw [rsT_of_le' h₂]
  unfold pbT
  rw [dif_pos h₁, dif_pos (h₂.trans h₁), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem rsT_constFn' {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) {O₀ O : Z.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn p O₀ a) O = constFn p O a := by
  rw [rsT_of_le' h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem rsT_field {Z : Scheme.{0}} {δ : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hδ : IsField ⊤ δ) {O₀ O : Z.Opens}
    (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT (δ O₀ s) O = δ O (rsT s O) := by
  rw [rsT_of_le' h, rsT_of_le' h, hδ.2.2 O₀ O h le_top s]

theorem rsT_add' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sum' {Z : Scheme.{0}} {O₀ : Z.Opens} {K : Type} (S : Finset K) (s : K → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ b ∈ S, s b) O = ∑ b ∈ S, rsT (s b) O := by
  unfold rsT; split_ifs <;> simp

end GlobalTheory.HeatInvLift

open GlobalTheory.HeatInvLift

namespace GlobalTheory.HeatInvLift

theorem exists_invLift_symmKS : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D
  obtain ⟨J, V, j, d₀, hc, hle, hl₀, hw₀⟩ := GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover R Dd O oa Y D
  obtain ⟨z, hzc, hzw, hz⟩ := GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle R Dd O oa Y n v dd hdd D J V d₀ hl₀ hw₀
  have H := fun a => GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary R Dd O oa Y n v dd hdd J V j hc hle (z a) (hzc a) (hzw a)
  choose c y hyw hy using H
  have hA := fun i => GlobalTheory.T.torusInvariantLift_add_invariantCombination R Dd O oa Y n v dd hdd D (V i) (d₀ i) (fun a => y a i) (hl₀ i) (hw₀ i) (fun a => hyw a i)
  have hrel : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f,
      (d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) - (d₀ i' W f + ∑ a, rsT (y a i') W * dd a W f) =
        ∑ a, ∑ b, constFn Y.H.hom W (Matrix.of c a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
    intro i i' W hW f
    rw [add_sub_add_comm, hz i i' W hW f]
    have hU : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
        Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i hx.1, hle i' hx.2⟩
    have key : ∀ a, rsT (z a i i') W = ∑ b, constFn Y.H.hom W (c a b) *
        dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W + (rsT (y a i') W - rsT (y a i) W) := by
      intro a
      rw [hy a i i', rsT_add', rsT_sub', rsT_rsT' inf_le_right hW, rsT_rsT' inf_le_left hW]
      congr 1
      rw [rsT_sum']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [rsT_mul', rsT_constFn' _ hW]
      congr 1
      unfold dlg
      rw [rsT_mul', rsT_field (hdd b).1 hW, rsT_pbT' _ hU hW, rsT_pbT' _ hU hW]
    simp only [key, Matrix.of_apply, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  obtain ⟨Θ, hs, hΘ⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_invariantLifts R Dd O oa Y n v dd hdd D J V j
    (fun i W f => d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) hc hle (fun i => (hA i).1) (fun i => (hA i).2)
    (Matrix.of c) hrel
  exact ⟨Θ, J, V, j, _, hs, hc, hle, fun i => (hA i).1, fun i => (hA i).2, hΘ⟩

end GlobalTheory.HeatInvLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasisStatement
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
theorem _root_.GlobalTheory.T.exists_connection_matrix_invariant_basis : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_symmKS | exact GlobalTheory.HeatInvLift.exists_invLift_symmKS | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_symmKS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefect
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatEx

theorem exists_basic_heat_polyDefect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h ∧ HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd m t gam hmon ht D hD
  obtain ⟨Θ, J, V, j, d, hs, hc, hle, hl, hw, hks⟩ := GlobalTheory.T.exists_connection_matrix_invariant_basis R Dd O oa Y n v dd hdd D
  obtain ⟨h, hb⟩ := GlobalTheory.T.exists_torus_invariant_heat_operator_of_symmetric_relation R Dd O oa Y n v dd hdd D Θ J V j d hs hc hle hl hw hks
    (GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary R Dd O oa Y n v dd hdd J V j hc hle)
  obtain ⟨w, π, π', hdef⟩ := GlobalTheory.T.exists_polynomial_defect_heatOperator_monomial R Dd O oa Y n v dd hdd m t gam hmon ht D hD h hb
  exact ⟨h, w, π, π', hb, hdef⟩

end GlobalTheory.HeatEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefectStatement
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
theorem _root_.GlobalTheory.T.exists_torusInvariant_heatOperator_polynomial_defect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h ∧ HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.HeatEx.exists_basic_heat_polyDefect | exact GlobalTheory.HeatEx.exists_basic_heat_polyDefect | (intros; apply GlobalTheory.HeatEx.exists_basic_heat_polyDefect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorPeriodDefectZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricSecondOrderOperatorOfCharacterFor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricSecondOrderOperatorOfCharacterFor
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

namespace GlobalTheory.HeatMod.TorTensor

theorem quad_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ : Type} [Fintype κ] {n : ℕ}
    (d : Fin n → S → S) (c : κ → Fin n → R) (w : κ → κ → R) (F : κ → S → S)
    (hF : ∀ s f, F s f = ∑ a, φ (c s a) * d a f) (hadd : ∀ s f g, F s (f + g) = F s f + F s g)
    (hmul : ∀ s r f, F s (φ r * f) = φ r * F s f) (f : S) :
    ∑ a, ∑ b, φ (∑ s, ∑ t, w s t * c s a * c t b) * d a (d b f) = ∑ s, ∑ t, φ (w s t) * F s (F t f) := by
  have h : ∀ s t, F s (F t f) = ∑ a, ∑ b, φ (c s a) * φ (c t b) * d a (d b f) := by
    intro s t
    have hs := map_sum (AddMonoidHom.mk' (F s) (hadd s)) (fun b => φ (c t b) * d b f) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hs
    rw [hF t f, hs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hmul, hF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ s, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ b, ∑ t, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) := Finset.sum_comm
    _ = ∑ s, ∑ a, ∑ t, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s, ∑ t, ∑ a, ∑ b, φ (w s t) * φ (c s a) * φ (c t b) * d a (d b f) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by simp only [_root_.mul_assoc]

theorem form_eq {R X : Type} [CommRing R] [AddCommGroup X] {κ : Type} [Fintype κ] (b : Module.Basis κ ℤ X)
    (w : X → X →+ R) (hw : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (α : X) :
    ∑ s, ∑ t, w (b s) (b t) * ((b.repr α t : ℤ) : R) * ((b.repr α s : ℤ) : R) = w α α := by
  have h1 : ∀ (g : X →+ R), g α = ∑ s, g (b s) * ((b.repr α s : ℤ) : R) := by
    intro g
    conv_lhs => rw [← b.sum_repr α]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  have h2 := h1 (AddMonoidHom.mk' (fun mu => w mu α) fun mu mu' => hw mu mu' α)
  simp only [AddMonoidHom.mk'_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h1 (w (b s)), Finset.sum_mul]

def twoPullConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) : R →+* Γ(Z, W) :=
  (s.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem base_constant_function_eq_torTensorConstantsRingHom {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) (W : Z.Opens) (r : R) :
    constFn s W r = twoPullConstantsRingHom s W r := rfl

theorem exists_quad : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd w hw hsymm
  let b := Module.Free.chooseBasis ℤ Dd.toPre.X
  let ℓ : Module.Free.ChooseBasisIndex ℤ Dd.toPre.X → Dd.toPre.X →+ R := fun s =>
    (Int.castAddHom R).comp (b.coord s).toAddMonoidHom
  have hℓ : ∀ s α, ℓ s α = ((b.repr α s : ℤ) : R) := fun s α => rfl
  have hex : ∀ s : Module.Free.ChooseBasisIndex ℤ Dd.toPre.X, ∃ c : Fin n → R,
      GlobalTheory.HeatMod.IsTorField Y (GlobalTheory.HeatMod.combF Y.H.hom dd c) (ℓ s) :=
    fun s => GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hdd (ℓ s)
  choose c hc using hex
  have hmul : ∀ s W r f, combF Y.H.hom dd (c s) W (twoPullConstantsRingHom Y.H.hom W r * f) =
      twoPullConstantsRingHom Y.H.hom W r * combF Y.H.hom dd (c s) W f := by
    intro s W r f
    rw [(hc s).1.2.1 W le_top, ← base_constant_function_eq_torTensorConstantsRingHom, (hc s).2.1 W r, mul_zero, add_zero]
  have key : ∀ W f, quadF Y.H.hom dd (Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a') W f =
      ∑ s, ∑ t, twoPullConstantsRingHom Y.H.hom W (w (b s) (b t)) * combF Y.H.hom dd (c s) W (combF Y.H.hom dd (c t) W f) :=
    fun W f => quad_eq (twoPullConstantsRingHom Y.H.hom W) (fun a => dd a W) c (fun s t => w (b s) (b t))
      (fun s => combF Y.H.hom dd (c s) W) (fun _ _ => rfl) (fun s => (hc s).1.1 W le_top) (fun s => hmul s W) f
  refine ⟨Matrix.of fun a a' => ∑ s, ∑ t, w (b s) (b t) * c s a * c t a', ?_, ?_, ?_⟩
  · ext a a'
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hsymm (b t) (b s)]
    ring
  · intro α W hW f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, base_constant_function_eq_torTensorConstantsRingHom, ← form_eq b w hw α, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hmul, (hc s).2.2.1 α W hW f hf, base_constant_function_eq_torTensorConstantsRingHom, hℓ, hℓ, map_mul,
      map_mul]
    ring
  · intro U g W k f hW
    rw [key, key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hc t).2.2.2 U g W k f hW, (hc s).2.2.2 U g W k _ hW]
    ring

end GlobalTheory.HeatMod.TorTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricSecondOrderOperatorOfCharacterForStatement
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
theorem _root_.GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ w : Dd.toPre.X → Dd.toPre.X →+ R, (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → ∃ M : Matrix (Fin n) (Fin n) R, Mᵀ = M ∧ (∀ (α : Dd.toPre.X) (W : Y.H.left.Opens), (∃ V : Dd.toPre.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f → GlobalTheory.HeatMod.quadF Y.H.hom dd M W f = constFn Y.H.hom W (w α α) * f) ∧ ∀ (U : Dd.toPre.P.A.left.Opens) (g : Γ(Dd.toPre.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)), W ≤ Y.q.left ⁻¹ᵁ U → GlobalTheory.HeatMod.quadF Y.H.hom dd M W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * GlobalTheory.HeatMod.quadF Y.H.hom dd M W f := by
  first | exact @GlobalTheory.HeatMod.TorTensor.exists_quad | exact GlobalTheory.HeatMod.TorTensor.exists_quad | (intros; apply GlobalTheory.HeatMod.TorTensor.exists_quad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeight
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

theorem isWt_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ τ hT j W _ hW
  exact GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hT (fun _ => j) W fun _ hx => Set.mem_iInter.2 fun _ => hW hx

end GlobalTheory.HeatMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeightStatement
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
theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  first | exact @GlobalTheory.HeatMod.isWt_fourierTerm | exact GlobalTheory.HeatMod.isWt_fourierTerm | (intros; apply GlobalTheory.HeatMod.isWt_fourierTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionSubConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionSubConstMul
set_option autoImplicit false

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

theorem valR_sub_const_mul {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp R) (φ : R →+* S)
    (x : Sp S ⟶ X) (hx : x ≫ p = spMap φ) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(X, W)) (r : R) :
    valR x W (f - constFn p W r * g) = valR x W f - φ r * valR x W g := by
  have hc : valR x W (constFn p W r) = φ r := GlobalTheory.Points.valR_constFn_of_over p φ x hx W h r
  rw [← hc]
  unfold valR
  simp only [dif_pos h, map_sub, map_mul]

theorem isWt_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  intro R _ _ Q Ω _ _ _ oa Y α W f g r hf hg S _ φ x x' c a a' ha ha' hW hW' hq hc
  have h1 := hf S φ x x' c a a' ha ha' hW hW' hq hc
  have h2 := hg S φ x x' c a a' ha ha' hW hW' hq hc
  have e : a ≫ Y.H.hom = spMap φ := by rw [ha]; exact Over.w x
  have e' : a' ≫ Y.H.hom = spMap φ := by rw [ha']; exact Over.w x'
  rw [valR_sub_const_mul _ φ a e W hW, valR_sub_const_mul _ φ a' e' W hW', h1, h2]
  ring

end GlobalTheory.HeatMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionSubConstMulStatement
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
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  first | exact @GlobalTheory.HeatMod.isWt_sub_const_mul | exact GlobalTheory.HeatMod.isWt_sub_const_mul | (intros; apply GlobalTheory.HeatMod.isWt_sub_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorPeriodDefectZero
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
open GlobalTheory.HeatMod

namespace GlobalTheory.HeatMod

theorem opMod {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (Θ M : Matrix (Fin n) (Fin n) R) (u c₁ c₂ : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W))
    (k : ℕ) (O : G.left.Opens) (f : Γ(G.left, O)) :
    op G dd (Θ + M) (u - c₁) (fun O f => d O f - combF G.hom dd c₂ O f) p p' k O f =
      op G dd Θ u d p p' k O f - 2 * (k : Γ(G.left, O)) * combF G.hom dd c₂ O f - quadF G.hom dd M O f -
        2 * combF G.hom dd c₁ O f := by
  have hc : ∀ a b : R, constFn G.hom O (a + b) = constFn G.hom O a + constFn G.hom O b := fun a b => by
    simp [constFn]
  have hs : ∀ a b : R, constFn G.hom O (a - b) = constFn G.hom O a - constFn G.hom O b := fun a b => by
    simp [constFn]
  simp only [op, combF, quadF, Matrix.add_apply, Pi.sub_apply, hc, hs, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem rsT_resG_constFn {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {U V : Z.Opens} (hV : V ≤ U)
    (x : R) : rsT (resG Z (le_top : U ≤ ⊤) (constFn s ⊤ x)) V = constFn s V x := by
  rw [← GlobalTheory.KS.rsT_of_le (le_top : U ≤ ⊤), GlobalTheory.KS.rsT_rsT le_top hV, GlobalTheory.KS.rsT_constFn _ le_top]

theorem defect_cancel {R X : Type} [CommRing R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R) (half : R)
    (h2 : 2 * half = 1) (hw1 : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (hw2 : ∀ mu mu', w mu mu' = w mu' mu)
    (hπ' : ∀ mu mu', π' (mu + mu') = π' mu + π' mu') (hπ : ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu)
    (k : ℕ) (mu α : X) :
    0 = 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu +
      (-(2 * (k : R) * (π (α + k • mu) - half * w (α + k • mu) (α + k • mu))) - w (α + k • mu) (α + k • mu) -
        2 * π' (α + k • mu)) -
      (-(2 * (k : R) * (π α - half * w α α)) - w α α - 2 * π' α) := by
  have wsm : ∀ (m : ℕ) (x y : X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hw1 0 0 y
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  have psm : ∀ (m : ℕ) (x : X), π' (m • x) = (m : R) * π' x := by
    intro m x
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hπ' 0 0
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hπ', ih]; push_cast; ring
  have qsm : ∀ (m : ℕ) (x : X), π (m • x) = (m : R) * π x + half * ((m : R) ^ 2 - m) * w x x := by
    intro m x
    induction m with
    | zero =>
      have := hπ 0 0
      simp only [add_zero, map_zero, AddMonoidHom.zero_apply] at this
      simp only [zero_smul, Nat.cast_zero]
      linear_combination -this
    | succ m ih =>
      rw [succ_nsmul, hπ, ih, map_nsmul, nsmul_eq_mul]
      push_cast
      linear_combination (-(m : R) * w x x) * h2
  simp only [hπ, hπ', hw1, map_add (f := _), wsm, map_nsmul, psm, qsm, nsmul_eq_mul, hw2 α mu]
  linear_combination (-((k : R) ^ 2 * w mu mu + 2 * (k : R) ^ 2 * w mu α)) * h2

theorem exists_heat_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h w π π' hB hD hw1 hw2 hπ' hπ
  let ℓ₁ : Dd.toPre.X →+ R := AddMonoidHom.mk' π' hπ'
  let half : R := algebraMap ℚ R (1 / 2)
  have h2 : (2 : R) * half = 1 := by
    simp only [half]
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  let ℓ₂ : Dd.toPre.X →+ R := AddMonoidHom.mk' (fun x => π x - half * w x x) (fun a b => by
    simp only [hπ, hw1, map_add (f := _)]
    rw [hw2 b a]
    linear_combination (-(w a b)) * h2)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₂
  obtain ⟨M, hMs, hMa, hMg⟩ := GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form R Dd O oa Y n v dd hv w hw1 hw2
  obtain ⟨⟨a1, a2, a3⟩, kc, wt₂, pb₂⟩ := hc₂
  let h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D :=
    { Θ := h.Θ + M
      symm := by rw [Matrix.transpose_add, h.symm, hMs]
      u := h.u - c₁
      J := h.J
      W := h.W
      j := h.j
      d := fun i O f => h.d i O f - combF Y.H.hom dd c₂ O f
      p := h.p
      p' := h.p'
      cover := h.cover
      le := h.le
      lift := fun i => by
        obtain ⟨⟨f1, f2, f3⟩, fc⟩ := h.lift i
        refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hh hW f => ?_⟩, fun W hW r => ?_⟩
        · dsimp only; rw [f1 W hW, a1 W le_top]; ring
        · dsimp only; rw [f2 W hW, a2 W le_top]; ring
        · dsimp only; rw [f3 W W' hh hW, a3 W W' hh le_top, map_sub]
        · dsimp only; rw [fc W hW, kc, sub_zero]
      glue := fun k i i' O hO f => by
        have hle : O ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (h.j i) ⊓ Dd.toPre.P.L.U (h.j i')) := fun x hx =>
          ⟨h.le i (hO hx).1, h.le i' (hO hx).2⟩
        rw [opMod, opMod, h.glue k i i' O hO f, pb₂ _ _ O k f hle, hMg _ _ O k f hle, hc₁.2.2.2 _ _ O k f hle]
        ring }

  have wsm : ∀ (m : ℕ) (x y : Dd.toPre.X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero => simp only [zero_smul, Nat.cast_zero, zero_mul]; have := hw1 0 0 y; simp only [add_zero] at this; linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  let e : ℕ → Dd.toPre.X → R := fun k α => -(2 * (k : R) * ℓ₂ α) - w α α - 2 * ℓ₁ α
  have key : ∀ k α σ σ', TActs Y h' k α σ σ' →
      TActs Y h k α σ (σ' - constFn Dd.toPre.P.A.hom ⊤ (e k α) • σ) := by
    rintro k α σ σ' ⟨τ, τ', hτ, hτ', hA⟩
    refine ⟨τ, τ' - constFn Y.H.hom ⊤ (e k α) • τ, hτ, GlobalTheory.T.isRaynaudFourierTerm_sub_smul R Dd.toPre O oa Y k α σ σ' τ τ' (e k α) hτ hτ',
      fun i => ?_⟩
    have hA' := hA i
    obtain ⟨V, hV⟩ := (hB i).1
    have hwt := GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight R Dd.toPre O oa Y k α σ τ hτ (h.j i) (h.W i) ⟨V, hV⟩ (h.le i)
    change rsT (τ'.f fun _ => h.j i) (h.W i) = op Y.H dd (h.Θ + M) (h.u - c₁)
      (fun O f => h.d i O f - combF Y.H.hom dd c₂ O f) (h.p i) (h.p' i) k (h.W i)
      (rsT (τ.f fun _ => h.j i) (h.W i)) at hA'
    rw [opMod, wt₂ α _ ⟨V, hV⟩ _ hwt, hMa α _ ⟨V, hV⟩ _ hwt, hc₁.2.2.1 α _ ⟨V, hV⟩ _ hwt] at hA'
    have hle' : h.W i ≤ LB.wchart Dd.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun x hx =>
      Set.mem_iInter.2 fun _ => h.le i hx
    have hce : constFn Y.H.hom (h.W i) (e k α) = -(2 * (k : Γ(Y.H.left, h.W i)) * constFn Y.H.hom (h.W i) (ℓ₂ α)) -
        constFn Y.H.hom (h.W i) (w α α) - 2 * constFn Y.H.hom (h.W i) (ℓ₁ α) := by
      have hcf : ∀ a, constFn Y.H.hom (h.W i) a = ((Y.H.hom.appLE ⊤ (h.W i) (fun _ _ => trivial)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) a := fun _ => rfl
      simp only [hcf, e, map_sub, map_neg, map_mul, map_natCast, map_ofNat]
    change rsT ((τ'.f fun _ => h.j i) - resG Y.H.left le_top (constFn Y.H.hom ⊤ (e k α)) * τ.f fun _ => h.j i) (h.W i) = _
    rw [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, rsT_resG_constFn, hA', hce]
    · ring
    · exact hle'
  refine ⟨h', fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB i
    refine ⟨b1, b2, b3, fun α V hV f hf => ?_⟩
    show IsWt Y α _ (h.d i _ f - combF Y.H.hom dd c₂ _ f)
    rw [wt₂ α _ ⟨V, rfl⟩ f hf]
    exact GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul R Dd.toPre O oa Y α _ _ f (ℓ₂ α) (b4 α V hV f hf) hf
  · intro k mu α σ σ' σ₁ σ₁' hk hS hT1 hT2
    have H := hD k mu α σ _ σ₁ _ hk hS (key _ _ _ _ hT1) (key _ _ _ _ hT2)
    have H2 := GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul R Dd.toPre k mu α σ σ' σ₁ σ₁' _ _ _ hS H
    convert H2 using 1
    exact defect_cancel w π π' half h2 hw1 hw2 hπ' hπ k mu α

end GlobalTheory.HeatMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorPeriodDefectZeroStatement
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
theorem _root_.GlobalTheory.T.exists_heatOperator_period_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  first | exact @GlobalTheory.HeatMod.exists_heat_defect_zero | exact GlobalTheory.HeatMod.exists_heat_defect_zero | (intros; apply GlobalTheory.HeatMod.exists_heat_defect_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditiveParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditiveParts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_polynomial_defect : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  intro R X _ _ _ _ w π π' h
  have key : ∀ k : ℕ, 1 ≤ k → ∀ mu mu' α : X,
      2 * (k : R) * (w (mu + mu') α - w mu α - w mu' α)
        + 2 * (k : R) ^ 2 * (π (mu + mu') - π mu - π mu' - w mu' mu)
        + 2 * (k : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
    intro k hk mu mu' α
    have e := h k hk mu mu' α
    simp only [map_add (f := _), map_nsmul, nsmul_eq_mul] at e
    linear_combination e
  have hAB : ∀ mu mu' : X, π (mu + mu') - π mu - π mu' - w mu' mu = 0 ∧
      π' (mu + mu') - π' mu - π' mu' = 0 := by
    intro mu mu'
    have h1 := key 1 le_rfl mu mu' 0
    have h2 := key 2 (by norm_num) mu mu' 0
    simp only [map_zero] at h1 h2
    push_cast at h1 h2
    have h4 : (4 : R) * (π (mu + mu') - π mu - π mu' - w mu' mu) = 0 := by
      linear_combination h2 - 2 * h1
    have hA : π (mu + mu') - π mu - π mu' - w mu' mu = 0 :=
      (mul_eq_zero.mp h4).resolve_left (by norm_num)
    refine ⟨hA, ?_⟩
    have h2' : (2 : R) * (π' (mu + mu') - π' mu - π' mu') = 0 := by
      linear_combination h1 - 2 * hA
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  have hw : ∀ mu mu' α : X, w (mu + mu') α = w mu α + w mu' α := by
    intro mu mu' α
    have e := key 1 le_rfl mu mu' α
    obtain ⟨hA, hB⟩ := hAB mu mu'
    push_cast at e
    have e2 : (2 : R) * (w (mu + mu') α - w mu α - w mu' α) = 0 := by
      linear_combination e - 2 * hA - 2 * hB
    have := (mul_eq_zero.mp e2).resolve_left (by norm_num)
    linear_combination this
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro mu mu'
    have a := (hAB mu mu').1
    have b := (hAB mu' mu).1
    rw [add_comm mu' mu] at b
    linear_combination a - b
  · intro mu mu'
    linear_combination (hAB mu mu').2
  · intro mu mu'
    linear_combination (hAB mu mu').1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditivePartsStatement
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
theorem _root_.GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  first | exact @GlobalTheory.cocycle_polynomial_defect | exact GlobalTheory.cocycle_polynomial_defect | (intros; apply GlobalTheory.cocycle_polynomial_defect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorCommutingPeriods
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.heat_commuting_periods_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hmon ht D hD
  obtain ⟨h, w, π, π', hb, hdef⟩ := GlobalTheory.T.exists_torusInvariant_heatOperator_polynomial_defect R Dd O oa Y n v dd hv m t gam hmon ht D hD
  have hcoc := GlobalTheory.T.heatOperator_period_defect_isCocycle R Dd O oa Y n v dd hv D h _ hb hdef
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts R Dd.toPre.X w π π' hcoc
  exact GlobalTheory.T.exists_heatOperator_period_defect_zero R Dd O oa Y n v dd hv D h w π π' hb hdef h1 h2 h3 h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorCommutingPeriodsStatement
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
theorem _root_.GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
  first | exact @GlobalTheory.heat_commuting_periods_exists | exact GlobalTheory.heat_commuting_periods_exists | (intros; apply GlobalTheory.heat_commuting_periods_exists <;> assumption)
end
