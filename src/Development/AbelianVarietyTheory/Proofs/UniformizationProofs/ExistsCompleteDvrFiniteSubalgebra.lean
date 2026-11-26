module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPrecompleteOfLeOfPowLe
namespace GlobalTheory.PrecompleteOfPowLe

universe u

theorem isPrecomplete_of_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m =>
    calc I ^ ((e + 1) * m) ≤ I ^ (e * m) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right m (Nat.le_succ e))
      _ = (I ^ e) ^ m := pow_mul I e m
      _ ≤ J ^ m := Ideal.pow_right_mono he m
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ (e + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos e)
  exact (hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))

end GlobalTheory.PrecompleteOfPowLe
end

namespace GlobalTheory

namespace CompleteFiniteExtension

open IsLocalRing

theorem isPrecomplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  first
  | (rename_i h_1 h_7; revert A h_1 I J hJ e he h_7; exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le)
  | exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | (apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le ..)

theorem isAdicComplete_of_finite_local (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  have := IsNoetherianRing.of_finite R S
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := R) S
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := R) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have := isPrecomplete_of_le_of_pow_le
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) S _ inferInstance) he
  exact ⟨⟩

end CompleteFiniteExtension

theorem exists_complete_dvr_finite_subalgebra :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F]
      [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (s : Finset F),
      ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W),
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧
        Module.Finite V W ∧ Module.Free V W ∧ IsLocalHom (algebraMap V W) ∧
        (∀ x ∈ s, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) ∧
        ∀ x ∈ s, IsIntegral V x → x ∈ W := by
  intro V _ _ _ _ _ F _ _ _ _ s
  let K := FractionRing V
  let _ : Algebra K F := FractionRing.liftAlgebra V F
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : Algebra.IsAlgebraic K F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mp inferInstance
  let L : IntermediateField K F := IntermediateField.adjoin K (s : Set F)
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let f : L →ₐ[V] F := L.val.restrictScalars V
  have hf : Function.Injective f := Subtype.val_injective
  let W : Subalgebra V F := (integralClosure V L).map f
  let e : integralClosure V L ≃ₐ[V] W := Subalgebra.equivMapOfInjective _ f hf
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hB : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing (integralClosure V L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have hfin : Module.Finite V W := Module.Finite.equiv e.toLinearEquiv
  have hd : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmem : ∀ x ∈ L, IsIntegral V x → x ∈ W := fun x hx hi =>
    ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hsL : ∀ x ∈ s, x ∈ L := fun x hx => IntermediateField.subset_adjoin K _ hx
  refine ⟨W, hd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra W, hfin, inferInstance, inferInstance,
    fun x hx => ?_, fun x hx => hmem x (hsL x hx)⟩
  obtain ⟨y, hy, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := V) x).exists_integral_multiple
  refine ⟨y • x, hmem _ ?_ h, algebraMap V F y, W.algebraMap_mem y,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective V F)).2 hy, ?_⟩
  · rw [← algebraMap_smul K y x]
    exact L.smul_mem (hsL x hx)
  · rw [Algebra.smul_def, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPullIso

theorem gs_sec_trans {X Z : Scheme.{0}} {L : LB X} (s : LB.Sec L) (r : Z ⟶ X) (z : Z) {j j' : L.ι}
    (hj : r z ∈ L.U j) (hj' : r z ∈ L.U j') :
    gs r z (L.U j) (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z (L.U j') (s.f j') := by
  have hm : r z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  have e : r z ∈ X.basicOpen a ↔ z ∈ Z.basicOpen ((r.app U).hom a) := by
    rw [← Scheme.preimage_basicOpen]; rfl
  rw [e]
  exact (Scheme.mem_basicOpen Z _ z h).symm

theorem exists_pull {X X' : Scheme.{0}} (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ))
    (hH : H.IsLB) (hH' : H'.IsLB) (hw : w.IsGen) (s : LB.Sec H) :
    ∃ s' : LB.Sec H', ∀ z (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ (s.f k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
  have hp := (isGen_iff w).1 hw
  have ind : ∀ (z : X') (k j : H.ι) (k' j' : H'.ι), φ z ∈ H.U k → φ z ∈ H.U j → z ∈ H'.U k' → z ∈ H'.U j' →
      ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) =
        (gm (𝟙 X') z _ (H'.g k' j')).val * (((Geo.Tor.gw w (𝟙 _) z j j')⁻¹).val * gs φ z _ (s.f j)) := by
    intro z k j k' j' hk hj hk' hj'
    have a := hp _ (𝟙 X') z k j k' j' hk hj hk' hj'
    rw [Category.id_comp] at a
    rw [a, gs_sec_trans s φ z hk hj, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    generalize gm φ z _ (H.g k j) = A
    generalize gm (𝟙 X') z _ (H'.g k' j') = B
    generalize Geo.Tor.gw w (𝟙 _) z j j' = C
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : H'.ι, ∃ a : Γ(X', H'.U k'), ∀ (z : X') (k : H.ι), φ z ∈ H.U k → z ∈ H'.U k' →
      gs (𝟙 X') z _ a = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) := by
    intro k'
    let W : H.ι → X'.Opens := fun k => (H.pull φ).U (fun _ => k) ⊓ H'.U k'
    have l₁ : ∀ k, W k ≤ φ ⁻¹ᵁ H.U k := fun k x hx => mem_pull.1 hx.1
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (z : X') k, z ∈ W k →
        gs (𝟙 X') z (W k) (u k) = ((Geo.Tor.gw w (𝟙 _) z k k')⁻¹).val * gs φ z _ (s.f k) :=
      ⟨fun k => ((show Γ(X', W k)ˣ from w.s (fun _ => k, k'))⁻¹).val *
          (X'.presheaf.map (homOfLE (l₁ k)).op).hom ((φ.app _).hom (s.f k)), fun z k hz =>
        (gs_mul (𝟙 X') z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit (𝟙 X') z _ hz _).trans (congrArg Units.val (map_inv _ _)))
          ((gs_res (𝟙 X') z _ hz _).trans ((gs_pull (𝟙 X') φ z _ (l₁ k hz) _).trans (by rw [Category.id_comp]))))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (H'.U k')
      (fun k => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hH (φ y)
        exact Opens.mem_iSup.2 ⟨k, mem_pull.2 hk, hy⟩) u
      (fun k j => fn_ext (V := W k ⊓ W j) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu y k hy.1, hu y j hy.2, ind y k j k' k' (l₁ k hy.1) (l₁ j hy.2) hy.1.2 hy.1.2,
          gm_self hH' (𝟙 X') y hy.1.2, Units.val_one, _root_.one_mul])
    refine ⟨a, fun z k h₁ h₂ => ?_⟩
    have hz : z ∈ W k := ⟨mem_pull.2 h₁, h₂⟩
    exact (gs_res (𝟙 X') z inf_le_right hz a).symm.trans ((congrArg (gs (𝟙 X') z (W k)) (ha k)).trans
      (hu z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun z k k' hk hk' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hH (φ y)
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X') y _ hy _) (gs_res (𝟙 X') y _ hy _))).symm)
    rw [ha j y k hk hy.1, ha j' y k hk hy.2]
    exact ind y k k j j' hk hk hy.1 hy.2
  · show _ = _ * gs (𝟙 X') z _ (a k')
    rw [ha k' z k hk hk', Units.mul_inv_cancel_left]

theorem section_pull : ∀ (X X' : Scheme.{0}) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ)), H.IsLB → H'.IsLB → w.IsGen → ∀ s : LB.Sec H, (∃! s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k'))) ∧ ∀ s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) → nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  intro X X' φ H H' w hH hH' hw s
  constructor
  · obtain ⟨s', hs'⟩ := exists_pull φ H H' w hH hH' hw s
    refine ⟨s', hs', fun t ht => ?_⟩
    obtain ⟨f, hf⟩ := t
    obtain ⟨g, hg⟩ := s'
    obtain rfl : f = g := funext fun k' => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact (Units.mul_right_inj _).1 ((ht z k k' hk hz).symm.trans (hs' z k k' hk hz))
    rfl
  · intro s' hs'
    have key : ∀ (z : X') (k : H.ι) (k' : H'.ι), φ z ∈ H.U k → z ∈ H'.U k' →
        (φ z ∈ X.basicOpen (s.f k) ↔ z ∈ X'.basicOpen (s'.f k')) := fun z k k' hk hk' => by
      rw [← isUnit_gs_iff φ z hk, hs' z k k' hk hk', Units.isUnit_units_mul]
      exact isUnit_gs_iff (𝟙 X') z hk' _
    ext z
    constructor
    · intro hz
      obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 hz
      obtain ⟨k, hk⟩ := exists_chart hH (φ z)
      exact Opens.mem_iSup.2 ⟨k, (key z k k' hk (X'.basicOpen_le _ hk')).2 hk'⟩
    · intro hz
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show φ z ∈ nonzeroLocus s from hz)
      obtain ⟨k', hk'⟩ := exists_chart hH' z
      exact Opens.mem_iSup.2 ⟨k', (key z k k' (X.basicOpen_le _ hk) hk').1 hk⟩

end GlobalTheory.SecPullIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxKernel

open GlobalTheory.KerPow

variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

theorem hasGen_flat (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]

theorem gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) : ∃ t : LB.Gen M, t.IsGen := by
  refine ⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have := LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y)
    (le_inf inf_le_left fun y _ => h y)
  refine (LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))
  exact unit_ext fun y hy => gm_res _ y _ hy _

theorem locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k

theorem locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  exact ⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩

end GlobalTheory.BoxKernel

namespace GlobalTheory


open KerPow BoxKernel in
theorem kTriv_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  intro S G' G _ _ _ _ j p L hL hK R _ t x hx
  classical
  have H : LocGen (boxLB L p.pr) (K := Fin 2) (fst (Over.mk t) G').left
      ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx
  clear hx
  generalize Over.mk t = T at x H
  refine p.lim.hom_ext fun ⟨i⟩ => ?_
  have := p.hom
  show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i
  rw [MonObj.one_comp]
  let u : G ⟶ G' := p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)
  have hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1 := fun i' => p.lim.fac _ ⟨i'⟩
  let a : Fin 2 → (T ⊗ G ⟶ G') := ![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]
  have H₁ := H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm)
    (φ' := fun k => (a k).left) (fun k => by
      fin_cases k
      · refine congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)
        rw [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T u))
  let b : Fin 2 × Fin j → (T ⟶ G) := fun q => ![x ≫ p.pr q.2, 1] q.1
  have H₂ := locGen_base hL (fst T G).left (fun q => (b q).left)
    (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)
  refine eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)
  have e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left := fun k i' hi => by
    refine congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)
    fin_cases k
    · show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]
    · show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1
      rw [Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]
  have e₁ : ∀ k, (a k).left ≫ (p.pr i).left =
      (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · refine congrArg (fun q => q.left)
        (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]
    · refine congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)
      rw [Category.assoc, hu, if_pos rfl, Category.comp_id]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]
  · simp only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]
  · simp only [if_neg hi, e₀ k i' hi, mul_inv_cancel]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.kTriv_external_tensor_power_lineBundle : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.kTriv_boxLB | exact GlobalTheory.kTriv_boxLB | (intros; apply GlobalTheory.kTriv_boxLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningClosed in
theorem isIso_of_isClosedImmersion_of_thickenings_of_isProper {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h' : ∀ n : ℕ, ∃ l : pullback Y.hom (thick R I n) ⟶ Z, l ≫ j = pullback.fst Y.hom (thick R I n) :=
    fun n => h n
  have hnear : ∀ x : Y.left, x ∈ zeroLocusOpen j.ker := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hSc : IsClosed (zeroLocusOpen j.ker)ᶜ := (isOpen_zeroLocusOpen j.ker).isClosed_compl
    have hT : IsClosed (Y.hom '' (zeroLocusOpen j.ker)ᶜ) := Y.hom.isClosedMap _ hSc
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (Y.hom x₀).asIdeal (Y.hom x₀).isPrime.ne_top
    have hcl : (⟨m, hm.isPrime⟩ : PrimeSpectrum (CommRingCat.of R)) ∈ closure {Y.hom x₀} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hpm
    obtain ⟨x, hxS, hx⟩ :=
      closure_minimal (Set.singleton_subset_iff.mpr
        (Set.mem_image_of_mem _ hx₀ : Y.hom x₀ ∈ Y.hom '' (zeroLocusOpen j.ker)ᶜ)) hT hcl
    apply hxS
    refine ThickeningClosed.mem_of_thickenings I Y.hom j h' x ?_
    rw [hx]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hker : j.ker = ⊥ := by
    ext U a
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Submodule.mem_bot]
    constructor
    · intro ha
      have hJ : LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) = ⊤ := by
        by_contra hJ
        obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
        obtain ⟨s, hs, hsa⟩ :=
          ThickeningClosed.exists_mul_eq_zero_of_mem j.ker U ⟨q, hq.isPrime⟩ (hnear _) ha
        exact hs (hJq (by simp [LinearMap.mem_ker, hsa]))
      have h1 : (1 : Γ(Y.left, U)) ∈ LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) :=
        hJ ▸ Submodule.mem_top
      simpa using h1
    · rintro rfl
      exact zero_mem _
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker

theorem hom_eq_of_thickenings_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by
  intro R _ _ _ I hI Y Z _ _ f g hfg
  have hf : f.left ≫ Z.hom = Y.hom := Over.w f
  have hg : g.left ≫ Z.hom = Y.hom := Over.w g
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.left ⟶ pullback Z.hom Z.hom,
      φ = pullback.lift f.left g.left (hf.trans hg.symm) := ⟨_, rfl⟩
  have hφ1 : φ ≫ pullback.fst Z.hom Z.hom = f.left := by rw [hφ, pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd Z.hom Z.hom = g.left := by rw [hφ, pullback.lift_snd]
  have hι : IsIso (pullback.fst φ (pullback.diagonal Z.hom)) := by
    refine isIso_of_isClosedImmersion_of_thickenings_of_isProper I hI Y _ fun n => ?_
    refine ⟨pullback.lift (fstG I n Y).left ((fstG I n Y).left ≫ f.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [hφ1]
    · simp [hφ2, hfg n]
  have key : φ = inv (pullback.fst φ (pullback.diagonal Z.hom)) ≫
      pullback.snd φ (pullback.diagonal Z.hom) ≫ pullback.diagonal Z.hom := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [← hφ1, ← hφ2, key]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace CosetQuotient

universe v u

theorem exists_grpObj {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {G T B : C} [GrpObj G] [IsCommMonObj G] [GrpObj T]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [Mono i]
    [EffectiveEpi q] [EffectiveEpi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)]
    (h : ∀ (Z : C) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) :
    ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  classical
  have same : ∀ {Z : C} (t : Z ⟶ T) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q :=
    fun t g => ((h _ _ _).2 ⟨t, rfl⟩).symm
  have hw2 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G ⊗ G), g₁ ≫ (q ⊗ₘ q) = g₂ ≫ (q ⊗ₘ q) →
      g₁ ≫ μ[G] ≫ q = g₂ ≫ μ[G] ≫ q := by
    intro Z g₁ g₂ hg
    have h1 : (g₁ ≫ fst G G) ≫ q = (g₂ ≫ fst G G) ≫ q := by
      simpa using hg =≫ fst B B
    have h2 : (g₁ ≫ snd G G) ≫ q = (g₂ ≫ snd G G) ≫ q := by
      simpa using hg =≫ snd B B
    obtain ⟨t, ht⟩ := (h _ _ _).1 h1
    obtain ⟨s, hs⟩ := (h _ _ _).1 h2
    have e : ∀ g : Z ⟶ G ⊗ G, g ≫ μ[G] = (g ≫ fst G G) * (g ≫ snd G G) := by
      intro g
      rw [MonObj.mul_eq_mul, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, e g₁, e g₂, ht, hs, _root_.mul_mul_mul_comm,
      ← MonObj.mul_comp, same]
  have hw1 : ∀ {Z : C} (g₁ g₂ : Z ⟶ G), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ ι[G] ≫ q = g₂ ≫ ι[G] ≫ q := by
    intro Z g₁ g₂ hg
    obtain ⟨t, ht⟩ := (h _ _ _).1 hg
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def, ht, _root_.mul_inv,
      ← GrpObj.inv_comp, same]
  let mB : B ⊗ B ⟶ B := EffectiveEpi.desc (q ⊗ₘ q) (μ[G] ≫ q) hw2
  have hmB : (q ⊗ₘ q) ≫ mB = μ[G] ≫ q := EffectiveEpi.fac _ _ _
  let iB : B ⟶ B := EffectiveEpi.desc q (ι[G] ≫ q) hw1
  have hiB : q ≫ iB = ι[G] ≫ q := EffectiveEpi.fac _ _ _
  let eB : 𝟙_ C ⟶ B := η[G] ≫ q
  have key : ∀ {Z : C} (a b : Z ⟶ G), lift (a ≫ q) (b ≫ q) ≫ mB = (a * b) ≫ q := by
    intro Z a b
    rw [← CartesianMonoidalCategory.lift_map, Category.assoc, hmB, ← Category.assoc]
    rfl
  have keyL : ∀ {Z : C} (f : Z ⟶ 𝟙_ C) (b : Z ⟶ G), lift (f ≫ eB) (b ≫ q) ≫ mB = b ≫ q := by
    intro Z f b
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have keyR : ∀ {Z : C} (a : Z ⟶ G) (f : Z ⟶ 𝟙_ C), lift (a ≫ q) (f ≫ eB) ≫ mB = a ≫ q := by
    intro Z a f
    have e : f ≫ eB = (f ≫ η[G]) ≫ q := (Category.assoc _ _ _).symm
    rw [e, key, toUnit_unique f (toUnit Z), ← Hom.one_def, _root_.mul_one]
  have epiL : Epi (𝟙_ C ◁ q) := by
    have e : 𝟙_ C ◁ q = (λ_ G).hom ≫ q ≫ (λ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have epiR : Epi (q ▷ 𝟙_ C) := by
    have e : q ▷ 𝟙_ C = (ρ_ G).hom ≫ q ≫ (ρ_ B).inv := by
      rw [← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  have invL : lift (ι[G] ≫ q) q ≫ mB = (ι[G] * 𝟙 G) ≫ q := by
    have e := key ι[G] (𝟙 G)
    rwa [Category.id_comp] at e
  have invR : lift q (ι[G] ≫ q) ≫ mB = (𝟙 G * ι[G]) ≫ q := by
    have e := key (𝟙 G) ι[G]
    rwa [Category.id_comp] at e
  let inst : GrpObj B :=
    { one := eB
      mul := mB
      inv := iB
      one_mul := by
        apply (cancel_epi (𝟙_ C ◁ q)).1
        have e : 𝟙_ C ◁ q = lift (fst _ _) (snd _ _ ≫ q) := by
          ext
          simp [CartesianMonoidalCategory.leftUnitor_hom]
        rw [e, lift_whiskerRight_assoc, keyL, lift_leftUnitor_hom]
      mul_one := by
        apply (cancel_epi (q ▷ 𝟙_ C)).1
        have e : q ▷ 𝟙_ C = lift (fst _ _ ≫ q) (snd _ _) := by
          ext
          simp [CartesianMonoidalCategory.rightUnitor_hom]
        rw [e, lift_whiskerLeft_assoc, keyR, lift_rightUnitor_hom]
      mul_assoc := by
        apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).1
        have e : (q ⊗ₘ q) ⊗ₘ q = lift (lift ((fst _ _ ≫ fst _ _) ≫ q) ((fst _ _ ≫ snd _ _) ≫ q))
            (snd _ _ ≫ q) := by ext <;> simp
        rw [e]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc,
          lift_whiskerLeft_assoc, key]
        rw [_root_.mul_assoc]
      left_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invL, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, inv_mul_cancel,
          Hom.one_def, Category.assoc]
      right_inv := by
        apply (cancel_epi q).1
        rw [← Category.assoc, comp_lift, hiB, Category.comp_id, invR, ← Category.assoc q,
          toUnit_unique (q ≫ toUnit B) (toUnit G), GrpObj.inv_eq_inv, mul_inv_cancel,
          Hom.one_def, Category.assoc] }
  refine ⟨inst, ⟨?_⟩, ⟨rfl, hmB.symm⟩, ?_⟩
  · show (β_ B B).hom ≫ mB = mB
    apply (cancel_epi (q ⊗ₘ q)).1
    have e : q ⊗ₘ q = lift (fst G G ≫ q) (snd G G ≫ q) := by ext <;> simp
    rw [e, ← Category.assoc, lift_braiding_hom, key, key, _root_.mul_comm]
  · have hsq : i ≫ q = toUnit T ≫ eB := by
      have e := same (𝟙 T) 1
      rw [Category.id_comp, _root_.mul_one] at e
      rw [e, Hom.one_def, Category.assoc]
    have ex : ∀ s : PullbackCone q eB, ∃ t : s.pt ⟶ T, s.fst = t ≫ i := by
      intro s
      have hs : (1 : s.pt ⟶ G) ≫ q = s.fst ≫ q := by
        rw [s.condition, Hom.one_def, toUnit_unique s.snd (toUnit s.pt), Category.assoc]
      obtain ⟨t, ht⟩ := (h _ _ _).1 hs
      exact ⟨t, by rw [ht, _root_.mul_one]⟩
    exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq (fun s => Classical.choose (ex s))
      (fun s => (Classical.choose_spec (ex s)).symm) (fun s => toUnit_unique _ _)
      (fun s m hm _ => by
        rw [← cancel_mono i, hm]
        exact Classical.choose_spec (ex s)))

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}}

lemma effectiveEpi_of_left {X Y : Over S} (f : X ⟶ Y) [EffectiveEpi f.left] :
    EffectiveEpi f := by
  have hw : ∀ {W : Over S} (e : X ⟶ W),
      (∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) →
      ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ f.left = g₂ ≫ f.left →
        g₁ ≫ e.left = g₂ ≫ e.left := by
    intro W e he Z g₁ g₂ hg
    have h2 : g₂ ≫ X.hom = g₁ ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hg, Category.assoc]
    have := he (Over.homMk g₁ rfl : Over.mk (g₁ ≫ X.hom) ⟶ X) (Over.homMk g₂ h2)
      (by ext; simpa using hg)
    exact congrArg CommaMorphism.left this
  exact ⟨⟨{
    desc := fun {W} e he => Over.homMk (EffectiveEpi.desc f.left e.left (hw e he)) (by
      rw [← cancel_epi f.left, ← Category.assoc, EffectiveEpi.fac, Over.w e, Over.w f])
    fac := fun {W} e he => by
      ext
      simp [EffectiveEpi.fac]
    uniq := fun {W} e he m hm => by
      ext
      exact EffectiveEpi.uniq f.left e.left (hw e he) m.left (by rw [← Over.comp_left, hm]) }⟩⟩

lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  have hc : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective :=
    ⟨fun _ _ hf hg => by
      have := hf
      have := hg
      infer_instance⟩
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) hf hg (Over.w f).symm
    (Over.w g).symm

lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

end CosetQuotient

attribute [local instance] Over.cartesianMonoidalCategory

theorem grpObj_of_flat_coset_quotient :
    ∀ (S : Scheme.{0}) (G T B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G)
      (q : G ⟶ B), IsMonHom i → Mono i → Flat q.left → Surjective q.left →
      QuasiCompact q.left →
      (∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) →
      ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by
  intro S G T B _ _ _ i q hi hm hf hs hc h
  have e1 : EffectiveEpi q := CosetQuotient.effectiveEpi_of_left q
  have f2 := CosetQuotient.flat_tensorHom q q
  have s2 := CosetQuotient.surjective_tensorHom q q
  have c2 := CosetQuotient.quasiCompact_tensorHom q q
  have e2 : EffectiveEpi (q ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  have f3 := CosetQuotient.flat_tensorHom (q ⊗ₘ q) q
  have s3 := CosetQuotient.surjective_tensorHom (q ⊗ₘ q) q
  have c3 := CosetQuotient.quasiCompact_tensorHom (q ⊗ₘ q) q
  have e3 : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q) := CosetQuotient.effectiveEpi_of_left _
  exact CosetQuotient.exists_grpObj i q h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

end SpecialFibreGenerator


end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusCube

open Rosenlicht SplitTorusPoints Geo.Tor

theorem toHom_comp_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z W : Over S} (ρ : W ⟶ Z)
    (t : Z ⟶ splitTorus S X) (a : Multiplicative X) :
    (toHom (ρ ≫ t) a).val = ρ.left.appTop.hom (toHom t a).val := by
  change (coord (ρ ≫ t)).hom _ = _
  rw [coord_comp]; rfl

theorem toHom_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} :
    toHom (1 : Z ⟶ splitTorus S X) = 1 :=
  map_one (splitTorusPointsEquiv S X Z)

theorem exists_form (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of k), ⊤)) (a b d : X), IsUnit c ∧
      ∀ (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X),
        (lift x (lift y u)).left.appTop.hom w = Z.hom.appTop.hom c *
          ((toHom x (Multiplicative.ofAdd a)).val * (toHom y (Multiplicative.ofAdd b)).val *
            (toHom u (Multiplicative.ofAdd d)).val) := by
  let Y := splitTorus (Spec (.of k)) (X × X × X)
  have hp : ∀ j : X →+ X × X × X, ∃ p : Y ⟶ splitTorus (Spec (.of k)) X,
      ∀ (Z : Over (Spec (.of k))) (ρ : Z ⟶ Y) (a : X),
        toHom (ρ ≫ p) (Multiplicative.ofAdd a) = toHom ρ (Multiplicative.ofAdd (j a)) := by
    intro j
    obtain ⟨p, hp⟩ := (toHom_bijective (Z := Y) (X := X)).2
      ((toHom (𝟙 Y)).comp (AddMonoidHom.toMultiplicative j))
    refine ⟨p, fun Z ρ a => Units.ext ?_⟩
    rw [toHom_comp_val, hp]
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  obtain ⟨p₀, h₀⟩ := hp (AddMonoidHom.inl _ _)
  obtain ⟨p₁, h₁⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  obtain ⟨p₂, h₂⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _))
  obtain ⟨c, ⟨a, b, d⟩, hc, e⟩ := torus_units k (X × X × X)
    (hw.map (lift p₀ (lift p₁ p₂)).left.appTop.hom)
  refine ⟨c, a, b, d, hc, fun Z x y u => ?_⟩
  obtain ⟨ρ, hρ⟩ := (toHom_bijective (Z := Z) (X := X × X × X)).2
    ((toHom x).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)) *
      (toHom y).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _))) *
      (toHom u).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  have r₀ : ρ ≫ p₀ = x := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₀ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₁ : ρ ≫ p₁ = y := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₁ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₂ : ρ ≫ p₂ = u := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₂ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have hl : lift x (lift y u) = ρ ≫ lift p₀ (lift p₁ p₂) := by
    rw [comp_lift, comp_lift, r₀, r₁, r₂]
  have hχ : ρ.left.appTop.hom (chi (X × X × X) (a, b, d)) =
      (toHom ρ (Multiplicative.ofAdd (a, b, d))).val := by
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  rw [hl, ← over_appTop_comp, e, map_mul, hχ, hρ, ← appTop_comp_apply, Over.w]
  simp

theorem unit_eq_one (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w)
    (h₀ : (lift (𝟙 _) (lift 1 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₁ : (lift 1 (lift (𝟙 _) 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₂ : (lift 1 (lift 1 (𝟙 _)) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X) :
    (lift x (lift y u)).left.appTop.hom w = 1 := by
  obtain ⟨c, a, b, d, hc, H⟩ := exists_form k X w hw
  rw [H] at h₀ h₁ h₂
  simp only [toHom_one, MonoidHom.one_apply, Units.val_one, _root_.mul_one, _root_.one_mul]
    at h₀ h₁ h₂
  have ha : a = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₀.trans (map_one _).symm)
  have hb : b = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₁.trans (map_one _).symm)
  have hd : d = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₂.trans (map_one _).symm)
  subst ha hb hd
  have hc1 : c = 1 := torus_const_injective k X (by simpa using h₀)
  rw [H, hc1]
  simp

section Val

variable {X Y : Scheme.{0}} (L : LB X)

def HasVal (form : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V)
    (f : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → L.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ (∀ (V : Type) [CommGroup V] (h : (Y ⟶ X) → V), ∏ k, h (φ k) ^ ε k = form V h) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t r z J = f Z r z J

variable {L}

theorem HasVal.mul {F F' : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f f'}
    (h : HasVal L F f) (h' : HasVal L F' f') :
    HasVal L (fun V _ k => F V k * F' V k) (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', a', b'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t',
    DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (a V k) (a' V k))
  · rw [val_mul hJ, b Z r z J hJ, b' Z r z J hJ]

theorem HasVal.inv {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) : HasVal L (fun V _ k => (F V k)⁻¹) (fun Z r z J => (f Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, a]
  · rw [val_inv, b Z r z J hJ]

theorem HasVal.exists_unit (hL : L.IsLB) {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) (hF : ∀ (V : Type) [CommGroup V] (k : (Y ⟶ X) → V), F V k = 1) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (f Z r z J).val = gs (𝟙 Z) z ⊤ (r.appTop.hom w.val) := by
  obtain ⟨K, _, φ, ε, u, hu, a, b⟩ := h
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (a V k).trans ((hF V k).trans (Fintype.prod_empty _).symm)) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← b Z r z J hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans
    ((gs_unit r z ⊤ trivial _).symm.trans ?_)
  refine Eq.trans ?_ (gs_pull (𝟙 Z) r z ⊤ trivial _).symm
  rw [Category.id_comp]

end Val

end TorusCube


end GlobalTheory
end
