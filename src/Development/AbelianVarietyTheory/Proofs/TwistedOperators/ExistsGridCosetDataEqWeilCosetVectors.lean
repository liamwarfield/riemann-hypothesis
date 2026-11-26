module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixModStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  first | exact @GlobalTheory.FunObj.HatFrame.homLat_approx_mod | exact GlobalTheory.FunObj.HatFrame.homLat_approx_mod | (intros; apply GlobalTheory.FunObj.HatFrame.homLat_approx_mod <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCoset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetIndCompare

variable {D : D7}

theorem frame_smul {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D) (Y : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • Y).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val := by
  have : (a • Y).map (toEAf D) = toEAf D a • Y.map (toEAf D) := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem frame_sub {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (Y Z : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((Y - Z).map (toEAf D))) β.val =
      HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val -
        HMul.hMul (HMul.hMul (β'⁻¹).val (Z.map (toEAf D))) β.val := by
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Matrix.mul_sub, Matrix.sub_mul]

theorem frame_incA {m n : ℕ} (y : Matrix (Fin m) (Fin n) D.host.E) :
    (y.map (incA D)).map (toEAf D) = y.map (eToEAf D) := by
  ext i j; rfl

theorem frame_mem_idS {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (EAf D)} {β' : GL (Fin m) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (I : Ideal (𝓞 D.host.E))
    {y : GlobalTheory.ChiGrid.homLat Λ Λ'} (hy : y ∈ (I • ⊤ : Submodule (𝓞 D.host.E) (GlobalTheory.ChiGrid.homLat Λ Λ'))) (i : Fin m)
    (j : Fin n) : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I,
      (t : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val ((y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D))) β.val i j := by
  have h1 : (y : Matrix (Fin m) (Fin n) D.host.E) ∈ I • GlobalTheory.ChiGrid.homLat Λ Λ' := by
    have := Submodule.mem_map_of_mem (f := (GlobalTheory.ChiGrid.homLat Λ Λ').subtype) hy
    rwa [Submodule.map_smul'', Submodule.map_subtype_top] at this
  have h2 : (y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D) ∈
      GlobalTheory.FunObj.HatFrame.genGrp D.host.F (I • GlobalTheory.ChiGrid.homLat Λ Λ') :=
    by
      unfold GlobalTheory.FunObj.HatFrame.genGrp
      apply AddSubgroup.subset_closure
      exact ⟨1, one_mem _, _, h1, by ext a b; rfl⟩
  exact GlobalTheory.FunObj.HatFrame.genGrp_le_frGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) I h2 i j

theorem frame_smul_incA {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D)
    (y : Matrix (Fin m) (Fin n) D.host.E) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • y.map (incA D)).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (y.map (eToEAf D))) β.val := by
  rw [frame_smul, frame_incA]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quot_iff (I : Ideal (𝓞 E)) (y : E ⊗[F] Formalism.L2.Herm.Af F) (r : 𝓞 E) :
    (∃ h : y ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) ⟨y, h⟩ =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) (Formalism.L2.DIV.oToS F E r)) ↔
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - Formalism.L2.DIV.oToS F E r := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨h, _, Ideal.Quotient.eq.1 hq, rfl⟩
  · rintro ⟨h, t, ht, et⟩
    refine ⟨h, Ideal.Quotient.eq.2 ?_⟩
    have : (⟨y, h⟩ : Formalism.L2.Herm.intAf F E) - Formalism.L2.DIV.oToS F E r = t := Subtype.ext et.symm
    rw [this]; exact ht

theorem step_fwd {I : Ideal (𝓞 E)} {y N a s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hq : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a := by
  obtain ⟨t1, h1, e1⟩ := hq
  obtain ⟨t2, h2, e2⟩ := hv
  obtain ⟨t3, h3, e3⟩ := hs
  refine ⟨t1 - t2 + t3 * ⟨a, ha⟩, add_mem (sub_mem h1 h2) (Ideal.mul_mem_right _ _ h3), ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3]
  ring

theorem step_bwd {I : Ideal (𝓞 E)} {y N a a' s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hN : N ∈ Formalism.L2.Herm.intAf F E) (hsi : s ∈ Formalism.L2.Herm.intAf F E)
    (ht : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a')
    (hu : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a' - a)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N := by
  obtain ⟨t1, h1, e1⟩ := ht
  obtain ⟨t2, h2, e2⟩ := hu
  obtain ⟨t3, h3, e3⟩ := hv
  obtain ⟨t4, h4, e4⟩ := hs
  have hy : y = ((t1 + ⟨s, hsi⟩ * t2 + ⟨s, hsi⟩ * ⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [Subring.coe_add, Subring.coe_mul, e1, e2]
    ring
  refine ⟨hy ▸ Subtype.property _, t1 + ⟨s, hsi⟩ * t2 - t4 * ⟨a, ha⟩ + t3,
    add_mem (sub_mem (add_mem h1 (Ideal.mul_mem_left _ _ h2)) (Ideal.mul_mem_right _ _ h4)) h3, ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3, e4]
  ring

end Gen

theorem cmpS_mk (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.E) :
    Formalism.L2.DIV.cmpS D.host.F I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E r) := by
  unfold Formalism.L2.DIV.cmpS
  exact Ideal.quotientMap_mk


set_option maxHeartbeats 1600000 in
theorem mem_cosSet_iff {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)}
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) (r : Fin T.V.rank → Fin S.V.rank → 𝓞 D.host.E)
    (hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)))
    (x₀ : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (hx₀ : x₀ ∈ GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
    (hN : ∀ i j, ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) =
      HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val i j -
        (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j) : EAf D)) (x : WO S.V T.V) :
    (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ GlobalTheory.ChiGrid.cosSet e (GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩) := by
  have hAint : ∀ i j, (HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val :
      Matrix (Fin T.V.rank) (Fin S.V.rank) (EAf D)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.FunObj.HatFrame.frame_int hS hT hx₀

  have hfr : ∀ y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E,
      HMul.hMul (HMul.hMul (T.β⁻¹).val ((x - e • y.map (incA D)).map (toEAf D))) S.β.val =
        frMapO S.V T.V S.β T.β x - toEAf D e • HMul.hMul (HMul.hMul (T.β⁻¹).val (y.map (eToEAf D))) S.β.val := by
    intro y
    rw [frame_sub, frame_smul_incA]; rfl
  change _ ↔ IsHalf e x ∧ ∃ x₀' : GlobalTheory.ChiGrid.homLat S.Λ T.Λ, GlobalTheory.ChiGrid.Cos.mk I x₀' = GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩ ∧
    x - e • (x₀' : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈
      GlobalTheory.ChiGrid.hatMx (I • GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
  refine and_congr_right fun hx => ?_
  have hx' : ∀ i j, e * x i j = x i j := hx
  have hinf : ∀ (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) i j,
      infPart D ((x - e • y.map (incA D)) i j) = 0 := by
    intro y i j
    have h1 : (x - e • y.map (incA D)) i j = e * (x i j - y.map (incA D) i j) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, hx' i j]
    rw [h1, map_mul, he0, zero_mul]
  constructor
  · intro hc
    unfold InCosetOf at hc
    refine ⟨⟨x₀, hx₀⟩, rfl, ?_⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I]
    refine ⟨hinf x₀, fun i j => ?_⟩
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hq := ((quot_iff I _ (r i j)).1 ((hc i j).imp fun _ h => h.trans (hcos i j))).2
    exact step_fwd (hAint i j) hq (hN i j) h1s
  · rintro ⟨y, hyc, hmem⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I] at hmem
    have hdiff := (Submodule.Quotient.eq _).1 hyc
    unfold InCosetOf
    intro i j
    have et := hmem.2 i j
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at et
    have hu := frame_mem_idS hS hT I hdiff i j
    rw [Submodule.coe_sub, Matrix.map_sub _ (map_sub (eToEAf D)), Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at hu
    have h := step_bwd (hAint i j) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)).2 he_int et hu (hN i j) h1s
    exact ((quot_iff I _ (r i j)).2 h).imp fun _ h => h.trans (hcos i j).symm

theorem cosetInd_eq_cosInd {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥)
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) :
    ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ I, GlobalTheory.Grid.cosetInd S T e I c = GlobalTheory.ChiGrid.cosInd e κ := by
  choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (c i j)
  obtain ⟨x₀, hx₀, hN⟩ := GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod S.Λ T.Λ S.β T.β hS hT I hI (fun i j => Formalism.L2.DIV.oToS D.host.F D.host.E (r i j))
  have hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)) := fun i j =>
    (congrArg (Formalism.L2.DIV.cmpS D.host.F I) (hr i j)).symm.trans (cmpS_mk I (r i j))
  refine ⟨GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩, funext fun x => ?_⟩
  have key := mem_cosSet_iff hS hT he0 he_int h1s c r hcos x₀ hx₀ hN x
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  classical
  rw [Set.indicator_apply]
  by_cases h : IsHalf e x ∧ InCosetOf S T I c x
  · rw [if_pos h, if_pos (key.1 h)]; rfl
  · rw [if_neg h, if_neg fun h' => h (key.2 h')]

theorem coset_eq_cos : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he c
  obtain ⟨he0, he_int, h1s⟩ := GlobalTheory.T.idempotentSum_infPart_integral_one_sub_mem e P d he
  refine cosetInd_eq_cosInd hS hT he0 ?_ he_int h1s c
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

end GlobalTheory.CosetIndCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCosetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  first | exact @GlobalTheory.CosetIndCompare.coset_eq_cos | exact GlobalTheory.CosetIndCompare.coset_eq_cos | (intros; apply GlobalTheory.CosetIndCompare.coset_eq_cos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isThetaAt_unique {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, h1⟩ := h
  exact (h1 T hT).trans (h'.2 T hT).symm

theorem exists_cosetVec_of_match {D : D7} {S T : Grid.Node D} {V₁ V₂ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin V₂.rank → D.host.E)}
    {I I' : Ideal (𝓞 D.host.E)} {e : AE D} {ψ ψ' : AddChar (AF D.host.F) ℂ}
    (hS : S.V = V₁) (hT : T.V = V₂) (hΛ₁ : HEq S.Λ Λ₁) (hΛ₂ : HEq T.Λ Λ₂) (hI : I = I') (hψ : ψ = ψ')
    (vac : WO (negSp V₁) V₂ → ℂ) (cv : Cos Λ₁ Λ₂ I' → WO (negSp V₁) V₂ → ℂ)
    (hcv : ∀ κ : Cos Λ₁ Λ₂ I', IsThetaAt ψ (symplO (negSp V₁) V₂) (heisO ψ (negSp V₁) V₂) e
      (latO (negSp V₁) V₂ (Λ₁ : Set _) (Λ₂ : Set _) fun _ => True) 1 vac (cosInd e κ) (cv κ))
    (hA : ∀ c : Grid.Coset S T I, ∃ κ : Cos S.Λ T.Λ I, Grid.cosetInd S T e I c = cosInd e κ)
    (hB : ∀ κ : Cos S.Λ T.Λ I, ∃ c : Grid.Coset S T I, Grid.cosetInd S T e I c = cosInd e κ)
    (f : WO S.V T.V → ℂ) (hf : HEq f vac) :
    ∃ v : Grid.Coset S T I → (WO S.V T.V → ℂ), (∀ c, Grid.IsCosetVec ψ' true S T e I c f (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (cv κ)) ∧ ∀ κ, ∃ c, HEq (v c) (cv κ) := by
  subst hS hT hI hψ
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₂
  obtain rfl := eq_of_heq hf
  choose κ hκ using hA
  refine ⟨fun c => cv (κ c), fun c => ?_, fun c => ⟨κ c, HEq.rfl⟩, fun κ' => ?_⟩
  · show IsThetaAt ψ _ _ e _ 1 f (Grid.cosetInd S T e I c) (cv (κ c))
    rw [hκ c]
    exact hcv (κ c)
  · obtain ⟨c, hc⟩ := hB κ'
    refine ⟨c, heq_of_eq ?_⟩
    have h1 := hcv (κ c)
    have h2 := hcv κ'
    rw [← hκ c, hc] at h1
    exact isThetaAt_unique h1 h2

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isFrame_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hR : GlobalTheory.Hk3.Core R F) {G : GlobalTheory.Grid.GridPre R} (hsp : G.IsSpaces) {i : ℕ} (hi : i ≤ D.R.m) :
    Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
  cases i with
  | zero =>
    obtain ⟨c, hc⟩ := hR.lev.βY 0 (by have := D.R.two_le_m; omega)
    exact hc.1
  | succ k =>
    obtain ⟨c, hc⟩ := (hsp.vert k 0 hi (Nat.zero_le _)).frame
    exact hc.1

theorem exists_cosData_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hR hsc G' W hW G hsp hch hag hcos i hi f hf
  have hA := GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  have hB := GlobalTheory.T.exists_homLatticeCosetIndicator_eq_latticeHomCoset (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  exact exists_cosetVec_of_match (I := G.lvl R) (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).sp
    (hag.vert i 0 hi.le (Nat.zero_le _)).sp (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).lat
    (hag.vert i 0 hi.le (Nat.zero_le _)).lat hag.lvl hW.ψ (W.vac i) (W.cosVec i) (hcos i hi) hA hB f hf

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  first | exact @GlobalTheory.GridJoin.exists_cosData_agree | exact GlobalTheory.GridJoin.exists_cosData_agree | (intros; apply GlobalTheory.GridJoin.exists_cosData_agree <;> assumption)
end
