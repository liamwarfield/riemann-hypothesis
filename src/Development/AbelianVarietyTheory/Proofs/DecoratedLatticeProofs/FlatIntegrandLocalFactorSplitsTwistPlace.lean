module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBiInvariantHasSumDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MainThm
open MeasureTheory DoubleCoset

namespace GlobalTheory.TwistedOperatorMainTheorem

theorem main_thm : ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (m : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure m] (J : Subgroup G), IsOpen (↑J : Set G) → IsCompact (↑J : Set G) → ∀ (ι : Type) [Countable ι] (x : ι → G), Pairwise (Function.onFun Disjoint fun (i : ι) ↦ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → ∀ (F : G → ℂ), (∀ (g j : G), j ∈ J → ∀ j' ∈ J, F (j * g * j') = F g) → (∀ (g : G), F g ≠ (0 : ℂ) → ∃ (i : ι), g ∈ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → (Summable fun (i : ι) ↦ MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) * ‖F (x i)‖) → MeasureTheory.Integrable F m ∧ HasSum (fun (i : ι) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G))) : ℂ) * F (x i)) (∫ (g : G), F g ∂m) ∧ HasSum (fun (c : DoubleCoset.Quotient (↑J : Set G) (↑J : Set G)) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (Quotient.out c) (↑J : Set G) (↑J : Set G))) : ℂ) * F (Quotient.out c)) (∫ (g : G), F g ∂m) := by
  intro G _ _ _ _ _ m _ J hJo hJc ι _ x hdisj F hF hsupp hsum

  have hmeas : ∀ a : G, MeasurableSet (doubleCoset a (J : Set G) J) := fun a =>
    (IsOpen.mul_left hJo).measurableSet
  have hfin : ∀ a : G, m (doubleCoset a (J : Set G) J) < ⊤ := fun a =>
    ((hJc.mul isCompact_singleton).mul hJc).measure_lt_top

  have hconst : ∀ a g, g ∈ doubleCoset a (J : Set G) J → F g = F a := by
    intro a g hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset.1 hg
    exact hF a u hu w hw
  have hint : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, F g ∂m =
      (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i) := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => hconst (x i) g hg), setIntegral_const, Complex.real_smul]
  have hnorm : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, ‖F g‖ ∂m =
      m.real (doubleCoset (x i) (J : Set G) J) * ‖F (x i)‖ := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => by rw [hconst (x i) g hg]), setIntegral_const, smul_eq_mul]
  have hon : ∀ i, IntegrableOn F (doubleCoset (x i) (J : Set G) J) m := fun i =>
    (integrableOn_const (hfin (x i)).ne).congr_fun (fun g hg => (hconst (x i) g hg).symm) (hmeas _)

  have hU : IntegrableOn F (⋃ i, doubleCoset (x i) (J : Set G) J) m :=
    integrableOn_iUnion_of_summable_integral_norm hon (by simpa only [hnorm] using hsum)
  have hout : ∀ g, g ∉ ⋃ i, doubleCoset (x i) (J : Set G) J → F g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨i, hi⟩ := hsupp g h
    exact hg (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hsumI : HasSum (fun i => (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i)) (∫ g, F g ∂m) := by
    have h := hasSum_integral_iUnion (fun i => hmeas (x i)) hdisj hU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h
    simp only [hint] at h
    exact h
  refine ⟨hU.integrable_of_forall_notMem_eq_zero hout, hsumI, ?_⟩

  have hinj : Function.Injective (fun i => DoubleCoset.mk J J (x i)) := by
    intro i j hij
    by_contra hne
    have hj : x j ∈ doubleCoset (x i) (J : Set G) J := by
      obtain ⟨u, hu, w, hw, e⟩ := (@DoubleCoset.eq _ _ J J (x i) (x j)).1 hij
      exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
    exact Set.disjoint_left.1 (hdisj hne) hj (mem_doubleCoset_self J J (x j))
  have hcls : ∀ i, Quotient.out (DoubleCoset.mk J J (x i)) ∈ doubleCoset (x i) (J : Set G) J := by
    intro i
    obtain ⟨u, hu, w, hw, e⟩ := DoubleCoset.mk_out_eq_mul J J (x i)
    exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
  have hzero : ∀ c ∉ Set.range (fun i => DoubleCoset.mk J J (x i)),
      (m.real (doubleCoset (Quotient.out c) (J : Set G) J) : ℂ) * F (Quotient.out c) = 0 := by
    intro c hc
    by_contra h
    obtain ⟨i, hi⟩ := hsupp _ (right_ne_zero_of_mul h)
    refine hc ⟨i, ?_⟩
    show DoubleCoset.mk J J (x i) = c
    rw [← DoubleCoset.out_eq' c]
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hi)).symm
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hsumI using 1
  funext i
  show (m.real (doubleCoset (Quotient.out (DoubleCoset.mk J J (x i))) (J : Set G) J) : ℂ) *
      F (Quotient.out (DoubleCoset.mk J J (x i))) = _
  rw [doubleCoset_eq_of_mem (hcls i), hconst (x i) _ (hcls i)]

end GlobalTheory.TwistedOperatorMainTheorem
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

open scoped Pointwise

namespace GlobalTheory

theorem integral_biInvariant_hasSum_doubleCoset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (m : Measure G) [m.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
  ∀ (ι : Type) [Countable ι] (x : ι → G),
    Pairwise (Function.onFun Disjoint fun i => DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
  ∀ F : G → ℂ, (∀ g, ∀ j ∈ J, ∀ j' ∈ J, F (j * g * j') = F g) →
    (∀ g, F g ≠ 0 → ∃ i, g ∈ DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) →
    Summable (fun i => m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) * ‖F (x i)‖) →
    Integrable F m ∧
    HasSum (fun i => (m.real (DoubleCoset.doubleCoset (x i) (J : Set G) (J : Set G)) : ℂ) * F (x i)) (∫ g, F g ∂m) ∧
    HasSum (fun c : DoubleCoset.Quotient (J : Set G) (J : Set G) =>
      (m.real (DoubleCoset.doubleCoset c.out (J : Set G) (J : Set G)) : ℂ) * F c.out) (∫ g, F g ∂m) := by
  first
  | exact @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm
  | (apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TwistedOperatorMainTheorem.main_thm ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvecto
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindex
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_torusElt_eq {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]

theorem sum_indic {n : Type} [Fintype n] [DecidableEq n] (s : Finset n) : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic, Finset.sum_ite_mem]

theorem reGL_symm_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m k) : GlobalTheory.ChainStepSupp.reGL k e.symm (GlobalTheory.ChainStepSupp.reGL k e g) = g := by
  ext i j
  simp [GlobalTheory.ChainStepSupp.val_reGL]

theorem reGL_mem_KO_iff {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} : GlobalTheory.ChainStepSupp.reGL k e g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => reGL_symm_reGL e g ▸ GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm h, GlobalTheory.ChainStepSupp.reGL_mem_KO e⟩

theorem unram_det_KO {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ KO k n) : μ₀ (GeneralLinearGroup.det κ) = 1 :=
  hμ _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hκ))

theorem unram_det_dcoset {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ}
    {s : Finset n} {g : GL n k}
    (h : ∃ κ ∈ KO k n, ∃ κ' ∈ KO k n, g = κ * torusElt k n ϖ (indic s) * κ') :
    μ₀ (GeneralLinearGroup.det g) = μ₀ ϖ ^ s.card := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := h
  rw [map_mul, map_mul, map_mul, map_mul, unram_det_KO hμ hκ, unram_det_KO hμ hκ', det_torusElt_eq, sum_indic,
    map_zpow, one_mul, mul_one, zpow_natCast]


open Classical in
theorem isRepsK_image {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g₀ : GL m k} {R : Finset (GL m k)} (hR : IsRepsK g₀ R) :
    IsRepsK (GlobalTheory.ChainStepSupp.reGL k e g₀) (R.image (GlobalTheory.ChainStepSupp.reGL k e)) := by
  refine ⟨fun g' hg' => ?_, fun κ hκ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hR.1 g hg
    exact ⟨_, GlobalTheory.ChainStepSupp.reGL_mem_KO e ha, _, GlobalTheory.ChainStepSupp.reGL_mem_KO e hb, by simp only [map_mul]⟩
  · obtain ⟨g, ⟨hg, hgK⟩, huniq⟩ := hR.2 (GlobalTheory.ChainStepSupp.reGL k e.symm κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm hκ)
    have key : ∀ x : GL m k, (GlobalTheory.ChainStepSupp.reGL k e x)⁻¹ * (κ * GlobalTheory.ChainStepSupp.reGL k e g₀) =
        GlobalTheory.ChainStepSupp.reGL k e (x⁻¹ * (GlobalTheory.ChainStepSupp.reGL k e.symm κ * g₀)) := by
      intro x
      rw [map_mul, map_mul, map_inv, GlobalTheory.ChainStepSupp.reGL_reGL_symm]
    refine ⟨GlobalTheory.ChainStepSupp.reGL k e g, ⟨Finset.mem_image_of_mem _ hg, ?_⟩, ?_⟩
    · rw [key]; exact GlobalTheory.ChainStepSupp.reGL_mem_KO e hgK
    · rintro y ⟨hy, hyK⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      rw [key, reGL_mem_KO_iff] at hyK
      rw [huniq x ⟨hx, hyK⟩]

theorem twist_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  intro k _ _ _ _ D _ _ N ε ϖ hϖ μ₀ hμ β f hf hH f₂ hf₂
  classical
  refine ⟨fun κ hκ m => ?_, fun s R hR m => ?_⟩
  · have hk1 := unram_det_KO hμ hκ
    have hρ := hf (GlobalTheory.ChainStepSupp.reGL k ε κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO ε hκ) (GlobalTheory.ChainStepSupp.reGL k ε m)
    simp only [hf₂, map_mul, hk1, one_mul, mul_one, hρ.1, hρ.2, and_self]
  · set ρ := GlobalTheory.ChainStepSupp.reGL k ε with hρdef
    set s' := s.map ε.toEmbedding with hs'
    have ht : ρ (torusElt k (Fin N) ϖ (indic s)) = torusElt k D ϖ (indic s') := by
      rw [hρdef, GlobalTheory.ChainStepSupp.reGL_torusElt]
      congr 1
      funext d
      simp [indic, hs', Finset.mem_map_equiv]
    have hR' : IsRepsK (torusElt k D ϖ (indic s')) (R.image ρ) := ht ▸ isRepsK_image ε hR
    have hcard : Fintype.card D = N := (Fintype.card_congr ε).symm.trans (Fintype.card_fin N)
    have hH' := hH s' _ hR' (ρ m)
    rw [Finset.sum_image (fun x _ y _ h => ρ.injective h), hs', Finset.card_map, hcard] at hH'
    have hterm : ∀ g ∈ R, f₂ (m * g) = ((((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
        (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card) * f (ρ m * ρ g) := by
      intro g hg
      rw [hf₂, map_mul, map_mul, map_mul, unram_det_dcoset hμ (hR.1 g hg), mul_inv, Units.val_mul, ← inv_pow,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hH', hf₂]
    ring

end GlobalTheory.TwistRenumber

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindexStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  first | exact @GlobalTheory.TwistRenumber.twist_renumber | exact GlobalTheory.TwistRenumber.twist_renumber | (intros; apply GlobalTheory.TwistRenumber.twist_renumber <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMul
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (n : ℕ) :
    (s.map (· * c)).esymm n = c ^ n * s.esymm n := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.sum_map_mul_left.symm]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hc : t.card = n := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hc, mul_comm, Multiset.map_id']

theorem genVal_map_mul (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) :
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  unfold genVal
  have e : ((B.map (· * c)).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (· * (c : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  rw [e, esymm_map_mul_const]
  ring

end GlobalTheory.ParHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMulStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ), genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  first | exact @GlobalTheory.ParHecke.genVal_map_mul | exact GlobalTheory.ParHecke.genVal_map_mul | (intros; apply GlobalTheory.ParHecke.genVal_map_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlock
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem isHgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ H hH
  refine ⟨fun κ hκ g => ?_, fun e => ?_⟩
  · have hK : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ KO k (A ⊕ D) :=
      (mem_parahoric.1 (GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (one_mem _) hκ)).1
    have e1 : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * g) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) * emb₂ k (Equiv.refl (A ⊕ D)) (1, g) := by
      rw [← map_mul]; simp
    have e2 : emb₂ k (Equiv.refl (A ⊕ D)) (1, g * κ) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, g) * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) := by
      rw [← map_mul]; simp
    exact ⟨by simp only [e1]; exact (hH.1 _ hK _).1, by simp only [e2]; exact (hH.1 _ hK _).2⟩
  · show H (emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e)) = _
    rw [GlobalTheory.ChainStepSupp.emb₂_one_torusElt, mtor, hH.2]
    congr 2
    simp [sumAbs, Fintype.sum_sum_type]

end GlobalTheory.ParHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlockStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  first | exact @GlobalTheory.ParHecke.isHgt_lower | exact GlobalTheory.ParHecke.isHgt_lower | (intros; apply GlobalTheory.ParHecke.isHgt_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvecto
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistedZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cellFun (r l t : ℕ) (ϖ : kˣ) (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k) : ℂ :=
  ∑' e : {e : Fin (l * t) → ℤ // Antitone e},
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k)).indicator (fun _ => v e.1) g

theorem cellFun_of_mem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ)
    (hdisj : Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))))
    (e : {e : Fin (l * t) → ℤ // Antitone e}) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : cellFun r l t ϖ v g = v e.1 := by
  unfold cellFun
  rw [tsum_eq_single e]
  · exact Set.indicator_of_mem hg _
  · intro e' he'
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj he'.symm) hg) _

theorem cellFun_of_notMem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : ∀ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∉ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) :
    cellFun r l t ϖ v g = 0 := by
  unfold cellFun
  simp [Set.indicator_of_notMem (hg _)]

theorem mem_dcell_mul_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {ϖ : kˣ}
    {f : D → ℤ} {g j j' : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (hj' : j' ∈ parahoric k A D) :
    j * g * j' ∈ dcell ϖ f ↔ g ∈ dcell ϖ f := by
  unfold dcell
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h
    refine DoubleCoset.mem_doubleCoset.2 ⟨j⁻¹ * a, mul_mem (inv_mem hj) ha, b * j'⁻¹, mul_mem hb (inv_mem hj'), ?_⟩
    calc g = j⁻¹ * (j * g * j') * j'⁻¹ := by group
      _ = _ := by rw [e]; group
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 h
    exact DoubleCoset.mem_doubleCoset.2 ⟨j * a, mul_mem hj ha, b * j', mul_mem hb hj', by group⟩

theorem cellFun_biinv {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k)
    {j j' : GL (Fin r ⊕ Blocks l t) k} (hj : j ∈ parahoric k (Fin r) (Blocks l t))
    (hj' : j' ∈ parahoric k (Fin r) (Blocks l t)) : cellFun r l t ϖ v (j * g * j') = cellFun r l t ϖ v g := by
  unfold cellFun
  congr 1
  funext e
  by_cases h : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_dcell_mul_iff hj hj').2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((mem_dcell_mul_iff hj hj').1 h'))]

theorem torusElt_zero {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) : torusElt k n ϖ 0 = 1 := by
  ext i j
  simp [val_torusElt, Matrix.one_apply, diagonal_apply]

theorem mtor_zero {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) :
    (mtor ϖ (0 : D → ℤ) : GL (A ⊕ D) k) = 1 := by
  rw [mtor, Sum.elim_zero_zero, torusElt_zero]

theorem sumAbs_comp {N : ℕ} {D : Type} [Fintype D] (ε : Fin N ≃ D) (e : Fin N → ℤ) :
    sumAbs (e ∘ ε.symm) = sumAbs e := by
  unfold sumAbs
  exact Equiv.sum_comp ε.symm (fun i => |e i|)

theorem sumAbs_elim {A D : Type} [Fintype A] [Fintype D] (e : D → ℤ) :
    sumAbs (Sum.elim (0 : A → ℤ) e) = sumAbs e := by
  simp [sumAbs, Fintype.sum_sum_type]

theorem det_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.zpow_add, Units.val_mul, ih, Units.val_zpow_eq_zpow_val ϖ (e i)]

theorem zonalInt_one {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k))
    (hμK : μK (KO k (Fin N)) = 1) {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (hψ : IsBorelSph k γ ψ) :
    zonalInt μK ψ 1 = 1 := by
  have h1 : ψ 1 = 1 := by
    have hb : (1 : GL (Fin N) k) ∈ borel k (Fin N) := (mem_borel _).2 fun i j hij => by
      simp [Matrix.one_apply, (ne_of_lt hij).symm]
    rw [hψ.2 1 hb (fun _ => 1) (fun i => by simp)]
    have : ord k 1 = 0 := by
      have := ord_mul k 1 1
      simp at this
      exact this
    simp [this]
  have hK : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := fun κ hκ => by
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun (SplitFlip.isOpen_KO.measurableSet) hK]
  simp [Measure.real, hμK]

theorem hgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ),
    IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) :=
  GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock

theorem genVal_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ),
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n :=
  GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul

theorem twist_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ),
    (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) →
    ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
      f (GlobalTheory.ChainStepSupp.reGL k ε m)) →
    (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧
    ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m :=
  GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex

theorem lower_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ →
  ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) →
  ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k)) (ψ : GL (Fin (l * t)) k → ℂ),
  (∀ f : GL (Fin (l * t)) k → ℂ, (∀ κ ∈ KO k (Fin (l * t)), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset (Fin (l * t))) R, IsRepsK (torusElt k (Fin (l * t)) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (l * t) (Finset.univ.val.map α) s.card * f m) →
    ∀ m, f m = f 1 * zonalInt μK ψ m) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V)
    (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ e : Fin (l * t) → ℤ,
  ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
    (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) * ℓ x := by
  intro k _ _ _ _ ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH _ μK ψ hψ V _ _ π x ℓ hx hℓ e
  classical
  have hH' := hgt_lower k (Fin r) (Blocks l t) ϖ H hH
  set H' : GL (Blocks l t) k → ℝ := fun m => H (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) with hH'def
  set f : GL (Blocks l t) k → ℂ := fun m => (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    ℓ (π (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) x) / ((Real.sqrt (H' m) : ℝ) : ℂ) ^ Fintype.card (Fin r)
    with hfdef
  obtain ⟨hfK, hfH⟩ := GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen k (Fin r) (Blocks l t) ϖ hϖ ξ hξt hξr V π B x ℓ hx hℓ H' hH' f (fun m => rfl)
  set f₂ : GL (Fin (l * t)) k → ℂ := fun m => (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    f (GlobalTheory.ChainStepSupp.reGL k (blkEquiv l t) m) with hf₂def
  obtain ⟨hf₂K, hf₂H⟩ := twist_transport k (Blocks l t) (l * t) (blkEquiv l t) ϖ hϖ μ₀ hμ₀
    (B.map (· * (ξ ϖ)⁻¹)) f hfK hfH f₂ (fun m => rfl)
  have hα : Finset.univ.val.map α = (B.map (· * (ξ ϖ)⁻¹)).map (· * (μ₀ ϖ)⁻¹) := by
    rw [hαB, Multiset.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply, MonoidHom.mul_apply, _root_.mul_inv_rev]
    ac_rfl
  have hz := hψ f₂ hf₂K (fun s R hR m => by rw [hf₂H s R hR m, hα, genVal_map_mul _ _ _ _ _ (μ₀ ϖ)⁻¹])
  have hval := hz (torusElt k (Fin (l * t)) ϖ e)

  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hf₂1 : f₂ 1 = ℓ x := by
    have h1 : H' 1 = 1 := by
      have := hH'.2 0
      rw [torusElt_zero] at this
      rw [this]; simp [sumAbs]
    have he1 : emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) ((1 : GL (Fin r) k), (1 : GL (Blocks l t) k)) = 1 := map_one _
    simp only [hf₂def, hfdef, map_one, h1, Real.sqrt_one, he1]
    simp
  have hS : ((Real.sqrt (H' (torusElt k (Blocks l t) ϖ (e ∘ (blkEquiv l t).symm))) : ℝ) : ℂ) ^ Fintype.card (Fin r) =
      (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    rw [hH'.2, sumAbs_comp, Fintype.card_fin, ← Complex.ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast; ring
  have hsum : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
  have hval' : f₂ (torusElt k (Fin (l * t)) ϖ e) = (((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
      ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) /
        (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ)) := by
    simp only [hf₂def, hfdef]
    rw [GlobalTheory.ChainStepSupp.reGL_torusElt, GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hS, det_torusElt, det_torusElt, hsum]
    simp [map_zpow, Units.val_zpow_eq_zpow_val]
  have key := hval'.symm.trans (hval.trans (by rw [hf₂1]))
  have hA : ((μ₀ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((ξ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hSne : (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  rw [MonoidHom.mul_apply, Units.val_mul, mul_zpow]
  have alg : ∀ (X Y S L : ℂ), X ≠ 0 → Y ≠ 0 → S ≠ 0 → L = X * Y * S * (X⁻¹ * (Y⁻¹ * L / S)) := by
    intro X Y S L hX hY hS; field_simp
  have hAn := zpow_ne_zero (∑ i, e i) hA
  have hBn := zpow_ne_zero (∑ i, e i) hB
  calc ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x)
      = ((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) * ((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
          (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
          ((((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
            ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) / (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ))) :=
        alg _ _ _ _ hAn hBn hSne
    _ = _ := by rw [key]; ring

theorem local_zeta_twisted : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  intro hUD k _ _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hξr hμ₀ hμ₀u B α ρ hαB hαρ H hH _ _ m _ hm c hc
  classical
  letI : MeasurableSpace (GL (Fin (l * t)) k) := borel _
  haveI : BorelSpace (GL (Fin (l * t)) k) := ⟨rfl⟩
  obtain ⟨μK, hμKH, hμK⟩ := GlobalTheory.GLDoubling.Model.exists_haar (k := k) (l * t)
  haveI := hμKH
  obtain ⟨ψ, hψB, hψ⟩ := GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical k (l * t) μK hμK ϖ hϖ α
  obtain ⟨hvol, hdisj⟩ := GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint k ϖ hϖ r l t m hm μK hμK
  have hceq : c = fun g => ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ) :=
    funext hc
  obtain ⟨hcBi, hcSupp, hcVal⟩ := GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted k ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hμ₀ hμ₀u
  rw [← hceq] at hcBi hcSupp
  beta_reduce at hcVal
  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hq1 : (1:ℝ) < resCard k := by exact_mod_cast one_lt_resCard k
  set C0 : ℝ := volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ with hC0
  have hC0pos : 0 < C0 := by
    refine mul_pos ?_ (inv_pos.2 (pow_pos hq _))
    rw [GlobalTheory.ChainStepIdentities.volAdd_eq k ν hν r]
    refine Finset.prod_pos fun i hi => inv_pos.2 ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    unfold zetaAt
    exact inv_pos.2 (sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))))
  have hcv : ∀ e : Fin (l * t) → ℤ, c (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
      ((C0 * (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    intro e
    have hsE : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
    rw [hc, hcVal, hsE, sumAbs_comp, Complex.ofReal_mul C0, Complex.ofReal_cpow hq.le, hC0]
    push_cast
    ring
  have hc1 : c 1 = ((C0 : ℝ) : ℂ) := by
    have := hcVal 0
    rw [mtor_zero, ← hc] at this
    rw [this]; simp [sumAbs, C0]
  set w : (Fin (l * t) → ℤ) → ℂ := fun e => (((resCard k : ℝ) ^
      (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
      zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) with hw
  refine ⟨by rw [hc1]; exact_mod_cast hC0pos.ne', cellFun r l t ϖ w, ?_, ?_, ?_⟩
  · intro V _ _ π x ℓ hx hℓ g
    have hE := lower_eigen k ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH μK ψ hψ V π x ℓ hx hℓ
    by_cases hg : ∃ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
    · obtain ⟨e, hge⟩ := hg
      rw [cellFun_of_mem w hdisj e hge]
      obtain ⟨j, hj, j', hj', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hge
      set a := (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) with ha
      set d := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj)
      set d' := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj')
      have hc_eq : c (j * a * j') = (ξ d : ℂ) * (ξ d' : ℂ) * c a := by
        rw [mul_assoc, (hcBi j hj d rfl _).1, (hcBi j' hj' d' rfl a).2]; ring
      have hℓ_eq : ℓ (π (j * a * j') x) = (ξ d : ℂ) * (ξ d' : ℂ) * ℓ (π a x) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.1 j' hj' d' rfl]
        simp only [map_smul, smul_eq_mul]
        rw [hℓ j hj d rfl]; ring
      have u1 : starRingEnd ℂ (ξ d : ℂ) * (ξ d : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d]; simp
      have u2 : starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d']; simp
      have hM : ‖(((μ₀ * ξ) ϖ : ℂˣ) : ℂ)‖ = 1 := by
        rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ₀u, hξu, one_mul]
      have u3 : starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i) = 1 := by
        rw [map_zpow₀, ← mul_zpow, Complex.conj_mul', hM]; simp
      have hqab : (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) *
          (resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ)) =
          (resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) := by
        rw [← Real.rpow_add hq]; congr 1; push_cast; ring
      rw [hc_eq, hℓ_eq, hcv e.1, hE e.1, hc1, hw]
      simp only [map_mul, Complex.conj_ofReal]
      have hqab' := congrArg (fun y : ℝ => (y : ℂ)) hqab
      simp only [Complex.ofReal_mul] at hqab' ⊢
      linear_combination (↑C0 * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e.1) * ℓ x) *
        ((starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) * (starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u1 +
        ((starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u2 +
        (((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u3 + hqab')
    · simp only [not_exists] at hg
      have hc0 : c g = 0 := by
        by_contra hne
        obtain ⟨e, he, hge⟩ := GlobalTheory.T.support_parahoricBiTransforming_doubleCosets k ϖ hϖ r l t ξ hξt hξr c hcBi hcSupp g hne
        exact hg ⟨e, he⟩ hge
      rw [cellFun_of_notMem w hg, hc0]; simp
  · intro g hgJ
    have h0 : g ∈ dcell ϖ ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) := by
      have : ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) = 0 := rfl
      rw [this]
      unfold dcell
      rw [mtor_zero]
      exact DoubleCoset.mem_doubleCoset.2 ⟨g, hgJ, 1, one_mem _, by simp⟩
    rw [cellFun_of_mem w hdisj ⟨0, fun _ _ _ => le_refl _⟩ h0, hw]
    simp [sumAbs, torusElt_zero, zonalInt_one μK hμK hψB]
  · intro s hs
    obtain ⟨hsum, hhas⟩ := GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value hUD k (l * t) μK hμK ϖ hϖ α ρ hαρ ψ hψB s hs
    have hHtor : ∀ e : Fin (l * t) → ℤ, H (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (resCard k : ℝ) ^ (-(sumAbs e)) := by
      intro e; rw [mtor, hH.2, sumAbs_elim, sumAbs_comp]
    have hqC : ((resCard k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hterm : ∀ e : {e : Fin (l * t) → ℤ // Antitone e},
        (m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) *
          (cellFun r l t ϖ w (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) *
            (H (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) ^ (s - (t : ℂ) / 2)) =
        (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
          zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := by
      intro e
      have hmem : (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) ∈
          dcell ϖ (e.1 ∘ (blkEquiv l t).symm) :=
        DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
      rw [cellFun_of_mem w hdisj e hmem, hHtor, hvol e.1]
      simp only [hw]
      have e1 : (((resCard k : ℝ) ^ ((r : ℤ) * sumAbs e.1) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cpow hq.le, Real.rpow_intCast]
      have e2 : (((resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hq.le]
      have e3 : (((resCard k : ℝ) ^ (-(sumAbs e.1)) : ℝ) : ℂ) ^ (s - (t : ℂ) / 2) =
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) := by
        rw [← Real.rpow_intCast, Complex.cpow_mul_ofReal_nonneg hq.le]
      have e4 : (resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [Complex.ofReal_natCast]
      have hadd : ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [← Complex.cpow_add _ _ hqC, ← Complex.cpow_add _ _ hqC]
        congr 1
        push_cast
        ring
      rw [Complex.ofReal_mul, e1, e2, e3, e4, ← hadd]
      ring
    set F : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => cellFun r l t ϖ w g * (H g : ℂ) ^ (s - (t : ℂ) / 2) with hF
    have hFbi : ∀ g j, j ∈ parahoric k (Fin r) (Blocks l t) → ∀ j' ∈ parahoric k (Fin r) (Blocks l t),
        F (j * g * j') = F g := by
      intro g j hj j' hj'
      have hjK := (mem_parahoric.1 hj).1
      have hj'K := (mem_parahoric.1 hj').1
      simp only [hF, cellFun_biinv w g hj hj', (hH.1 j' hj'K (j * g)).2, (hH.1 j hjK g).1]
    have hsupp : ∀ g, F g ≠ 0 → ∃ e : {e : Fin (l * t) → ℤ // Antitone e},
        g ∈ DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t)) := by
      intro g hg
      by_contra hne
      simp only [not_exists] at hne
      apply hg
      simp only [hF, cellFun_of_notMem w hne, zero_mul]
    have hsumm : Summable fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) *
          ‖F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))‖ := by
      refine hsum.congr fun e => ?_
      change _ = m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) * _
      rw [← hterm e, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
    obtain ⟨hInt, hHas, -⟩ := GlobalTheory.integral_biInvariant_hasSum_doubleCoset (GL (Fin r ⊕ Blocks l t) k) m
      (parahoric k (Fin r) (Blocks l t)) GlobalTheory.ParHecke.Model.isOpen_parahoric GlobalTheory.ParHecke.Model.isCompact_parahoric
      {e : Fin (l * t) → ℤ // Antitone e} (fun e => mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) hdisj F hFbi hsupp hsumm
    refine ⟨hInt, ?_⟩
    have hfun : (fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        ((m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) : ℝ) : ℂ) *
          F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))) = fun e : {e : Fin (l * t) → ℤ // Antitone e} => (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
            zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := funext hterm
    rw [hfun] at hHas
    exact hHas.unique hhas

end GlobalTheory.TwistedZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvectoStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  first | exact @GlobalTheory.TwistedZeta.local_zeta_twisted | exact GlobalTheory.TwistedZeta.local_zeta_twisted | (intros; apply GlobalTheory.TwistedZeta.local_zeta_twisted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.OnePlace

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Core.Rk.IP GlobalTheory.ParHecke GlobalTheory.Core.Rk.SphCoef

theorem transport {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H)
    (m : Measure G) [m.IsHaarMeasure] (P : Subgroup G) (hP : IsOpen (P : Set G)) (h1 : m P = 1) (f : G → ℂ)
    (hf : Integrable f m) :
    ∃ (J : Subgroup H) (μ : Measure H), IsOpen (J : Set H) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧
      Integrable (fun y => f (e.symm y)) μ ∧ (∀ y, y ∈ J ↔ e.symm y ∈ P) ∧ ∫ y, f (e.symm y) ∂μ = ∫ g, f g ∂m := by
  let e' : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have he : (e' : G → H) = e := rfl
  have hJ : ((P.comap e.symm.toMulEquiv.toMonoidHom : Subgroup H) : Set H) = e.symm ⁻¹' (P : Set G) := rfl
  refine ⟨P.comap e.symm.toMulEquiv.toMonoidHom, m.map e', ?_, ?_, ?_, ?_, fun y => Iff.rfl, ?_⟩
  · rw [hJ]; exact hP.preimage e.symm.continuous
  · rw [he]; exact e.isHaarMeasure_map m
  · rw [MeasurableEquiv.map_apply, hJ, he, ← h1]
    congr 1
    ext g; simp
  · rw [integrable_map_equiv]
    convert hf using 1
    funext g; simp [he]
  · rw [integral_map_equiv]
    simp [he]

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] (P : Subgroup G) (hP : IsOpen (P : Set G)) (hc : IsCompact (P : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m P = 1 := by
  let K : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨P, hc⟩, by
      simp only [hP.interior_eq]
      exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {D : D7}

theorem rcoef_eq_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {A : HSp D} (m : Measure (GA D A))
    (hm : m.IsHaarMeasure) {u₁ u₂ : GA D A → ℂ} (h1 : MemL2Quotient (GQ A) m u₁) (h2 : MemL2Quotient (GQ A) m u₂)
    (ι : GL (I ⊕ I') k →* GA D A) (x : GA D A) (hx : ∀ y, ι y * x = x * ι y) (ξ : kˣ →* ℂˣ) (hξ : GlobalTheory.SmGL.IsUnitaryChar ξ)
    (ϖ : kˣ) (B : Multiset ℂˣ) (hg : IsGen ((GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι) ξ ϖ B u₁)
    (ht : ∀ j ∈ parahoric k I I', ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ g, u₂ (g * ι j) = (ξ d : ℂ) * u₂ g) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (I ⊕ I') k) V) (u : V) (ℓ : V →ₗ[ℂ] ℂ),
      IsGen π ξ ϖ B u ∧ IsCoType π ξ ℓ ∧ (∀ y, ℓ (π y u) = rcoef m u₁ u₂ (x * ι y)) ∧ ℓ u = rcoef m u₁ u₂ x := by
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m F}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ρ : Representation ℂ (GL (I ⊕ I') k) (GA D A → ℂ) := (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι
  have hst : ∀ g, p ≤ p.comap (ρ g) := fun g F hF => MemL2Quotient.mul_right hF (ι g)
  let π : Representation ℂ (GL (I ⊕ I') k) p := ρ.subrepresentation p hst
  have hπ : ∀ g (F : p), ((π g F : p) : GA D A → ℂ) = ρ g F := fun _ _ => rfl
  let ℓ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left (MemL2Quotient.mul_right F.2 x) (MemL2Quotient.mul_right G.2 x) h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  refine ⟨p, inferInstance, inferInstance, π, ⟨u₁, h1⟩, ℓ, ⟨fun j hj d hd => Subtype.ext (hg.1 j hj d hd), hg.2.1,
    fun s R d hR => Subtype.ext ?_⟩, fun j hj d hd F => ?_, fun y => ?_, rfl⟩
  · rw [Submodule.coe_sum]
    exact hg.2.2 s R d hR
  · have e1 : rTr A x (π j F) = rTr A (ι j) (rTr A x F) := funext fun g => by
      show (F : GA D A → ℂ) (g * x * ι j) = (F : GA D A → ℂ) (g * ι j * x)
      rw [mul_assoc, mul_assoc, hx]
    have e2 := petersson_rTr (μ := m) (MemL2Quotient.mul_right F.2 x) h2 (ι j)
    have hn : (ξ d : ℂ) * conj (ξ d : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ d]; simp
    have e3 : ∀ φ : GA D A → ℂ, petersson A m φ u₂ = (ξ d : ℂ) * petersson A m φ (rTr A (ι j) u₂) := fun φ => by
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend, rTr, ht j hj d hd, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext q
      linear_combination (-(φ q.out * conj (u₂ q.out))) * hn
    show petersson A m (rTr A x (π j F)) u₂ = (ξ d : ℂ) * petersson A m (rTr A x F) u₂
    rw [e1, e3]
    exact congrArg _ e2
  · show petersson A m (rTr A x (ρ y u₁)) u₂ = petersson A m (rTr A (x * ι y) u₁) u₂
    congr 1
    funext g
    show u₁ (g * x * ι y) = u₁ (g * (x * ι y))
    rw [mul_assoc]

theorem val_type {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L)
    (g : GA D s.V) : PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ f) = PiTensorProduct.lift.symm u.1 f := by
      rw [PiTensorProduct.lift_symm]; rfl
    have := hT.lev f κ hκ g
    rw [← e] at this
    simp only [PiLocalization₂.val, map_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  | add a b ha hb =>
    simp only [PiLocalization₂.val, map_add (f := _), Pi.add_apply] at ha hb ⊢
    rw [ha, hb]; ring

theorem hgt_split {A : HSp D} {L : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat A} {a : GL (Fin A.rank) (AE D)} (hL : IsSelfDualC A L)
    (ha : GlobalTheory.Doubling.IsMaj A a) (Sf : Finset (HeightOneSpectrum (𝓞 D.host.F))) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ Sf) (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v 1 = 1) {x : GA D A} (hx : x ∈ openOff A L Sf)
    (hxv : proj D.sp.cm.sig A.gram v x = 1) (y : GlobalTheory.FinZeta.Gv A v) (t : ℂ) :
    GlobalTheory.Doubling.npow (hgtL A L a (x * emb D.sp.cm.sig A.gram v y)) t =
      GlobalTheory.Doubling.npow (hgtL A L a x) t * ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y : ℝ) : ℂ) ^ t := by
  classical
  obtain ⟨-, -, h⟩ := hgtL_props D A L a hL ha
  have hne : ∀ u, u ≠ v → proj D.sp.cm.sig A.gram u (x * emb D.sp.cm.sig A.gram v y) = proj D.sp.cm.sig A.gram u x :=
    fun u hu => by rw [map_mul, proj_emb_ne _ _ hu, mul_one]
  have hxy : x * emb D.sp.cm.sig A.gram v y ∈ openOff A L Sf := fun u hu => by
    rw [hne u (fun e => hu (e ▸ hv))]; exact hx u hu
  have e : (hgtL A L a (x * emb D.sp.cm.sig A.gram v y) : ℝ) = (hgtL A L a x : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := by
    rw [(h Sf).2 _ hxy, (h Sf).2 _ hx, ← Finset.mul_prod_erase Sf _ hv, ← Finset.mul_prod_erase Sf _ hv, hxv, h1,
      Finset.prod_congr rfl fun u hu => congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L u) (hne u (Finset.ne_of_mem_erase hu))]
    simp only [map_mul, projArch_emb, proj_emb_self, hxv, mul_one, one_mul]
    ring
  simp only [GlobalTheory.Doubling.npow]
  have h0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := NNReal.coe_nonneg _
  rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) h0]

theorem hgt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} {H : GL n k → ℝ} (hH : IsHgt ϖ H) {g : GL n k}
    (hg : g ∈ GlobalTheory.SplitWeil.KO k n) : H g = 1 := by
  have e : GlobalTheory.GLDoubling.torusElt k n ϖ 0 = 1 := by
    simp only [GlobalTheory.GLDoubling.torusElt, Pi.zero_apply, zpow_zero]
    exact map_one _
  have h := hH.2 0
  rw [e] at h
  rw [← mul_one g, (hH.1 g hg 1).1, h]
  simp [GlobalTheory.ZonalCellDecomposition.sumAbs]


set_option maxHeartbeats 1600000 in
theorem local_factor : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (ζ : GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hQ v₁ hv₁ v₂ hv₂ z hz PP hPP
  obtain ⟨⟨v, pr, hpr⟩, hch⟩ := GlobalTheory.T.exists_charts_at_twist_places_chain D c w hw k hk.le s hs PP hPP
  obtain ⟨-, ⟨x₀, ϖ, hxϖ⟩, ⟨ι, hι⟩, hchi⟩ := hch v pr hpr
  obtain ⟨μT, hμu, hμT⟩ := hchi (c.chT (k + 1))
  obtain ⟨hv, hres, htame, hlift, hdict⟩ := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v pr hpr
  subst hv
  have hL : LiftsChar pr PP μT (w.ξ PP) := hlift k hk μT (Or.inr hμT)
  obtain ⟨⟨e, he, -, hH⟩, hlev, hlc⟩ := hdict ι hι
  have hH := hH x₀ ϖ hxϖ
  obtain ⟨-, hcard, hα⟩ := GlobalTheory.T.lower_block_parameter_twist_L_factor D c w hw k hk PP hPP _ pr hpr x₀ ϖ hxϖ
  obtain ⟨α, hαe⟩ : ∃ α : Fin (k * D.R.t) → ℂˣ,
      Finset.univ.val.map α = (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) := by
    set M := (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) with hM
    have hl : M.toList.length = k * D.R.t := by rw [Multiset.length_toList, hM, Multiset.card_map, hcard]
    refine ⟨fun i => M.toList.get (i.cast hl.symm), ?_⟩
    rw [Fin.univ_val_map, ← List.ofFn_congr hl, List.ofFn_get, Multiset.coe_toList]
  obtain ⟨hbd, hval⟩ := hα α hαe
  obtain ⟨e₀, he₁, he₂, he₃, hϖ⟩ := id hxϖ
  have hμϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x₀) := hμT x₀ ϖ ⟨e₀, he₁, he₂, he₃⟩
  letI : MeasurableSpace (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := borel _
  haveI : BorelSpace (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := borel _
  haveI : BorelSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))
  obtain ⟨hPo, hPc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))
    (Fin D.R.r) (Blocks k D.R.t)
  obtain ⟨m₀, hm₀, hm₁⟩ := exists_haar _ hPo hPc
  obtain ⟨cf, hcf⟩ : ∃ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ℂ, ∀ g, cf g =
      GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) _) (datum μT)) (datum μT) :=
    ⟨_, fun _ => rfl⟩
  have hcoef := GlobalTheory.T.weilCoefficient_splits_localFactor_twistPlace D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP _ pr hpr ι hι μT hμT ν hν cf hcf φ
  obtain ⟨hc1, ζ₀, hζ, hζ1, hint⟩ := GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector hU _ ν hν ϖ hϖ D.R.r D.R.t k μT 1 hμu (htame μT hL).1 (htame μT hL).2
    (fun _ _ => rfl) (fun _ => by simp) (qPar c PP x₀ k) α (((D.R.t : ℝ) - 1) / 2) (by rw [one_mul, hμϖ]; exact hαe)
    (by rw [hres]; exact hbd) _ hH m₀ hm₁ cf (by rw [one_mul]; exact hcf)
  obtain ⟨hI, hIv⟩ := hint (z : ℂ) (by rw [Complex.ofReal_re]; linarith)
  obtain ⟨J, μ, hJo, hμH, hμ1, hμI, hJ, hμv⟩ := transport e m₀ _ hPo hm₁ _ hI
  obtain ⟨hr, -, hst⟩ := id hs
  obtain ⟨hr', -, hst'⟩ := id hs'
  have hH1 : ∀ y ∈ parahoric _ (Fin D.R.r) (Blocks k D.R.t), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) = 1 := fun y hy =>
    hgt_one hH (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric.1 hy).1
  refine ⟨J, μ, _, hJo, hμH, hμ1, hμI, fun y hy => ?_, fun g => ?_, fun hzt => ?_, fun x hx hxv y => ?_⟩
  · have hy' := (hJ y).1 hy
    simp only [hζ1 _ hy', hH1 _ hy']
    simp
  · rw [hJ, ← hlev, he, ContinuousMulEquiv.apply_symm_apply]
    rfl
  · rw [hμv, hIv, hres, ← hval, hzt]
    push_cast
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective y
    simp only [ContinuousMulEquiv.symm_apply_apply]
    have hθ := hw.com.inf
    haveI : s.ν.IsHaarMeasure := hst.haar
    have hL2 : ∀ (u : s.CC c), ∀ v ∈ s.KF, MemL2Quotient (GQ s.V) s.ν fun g => conj (PiLocalization₂.val u v g) := fun u v hv =>
      memL2_of_cusp_form hC hθ (mem_cuspForms.1
        (GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hθ s.M hst.sigOK u.1 u.2 v hv)).1
    obtain ⟨V, _, _, π, u, ℓ, hg, hco, hℓ, hℓ1⟩ := rcoef_eq_coef s.ν hst.haar (hL2 u₁ v₁ hv₁) (hL2 u₂ v₂ hv₂) ι x
      (fun y => by rw [he]; exact (commute_emb _ _ _ hxv).eq) μT hμu ϖ (qPar c PP x₀ k)
      (hQ v₁ PP hPP _ pr hpr x₀ ϖ hxϖ μT hL ι hι) (fun j hj d hd g => by
        rw [val_type u₂ v₂ ((hlev j).2 hj), hlc μT hL j hj d hd, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
          Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hμu d]
        simp)
    have h3 := hζ V π u ℓ hg hco y
    rw [hℓ, hℓ1] at h3
    have h2 := hcoef x (by simp only [gAt, hxv, map_one]) y
    have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := by
      classical
      refine Finset.mem_image.2 ⟨PP, ?_, rfl⟩
      rw [hw.union]
      exact Finset.mem_union_right _ hPP
    have h5 := hgt_split (A := s.V) (L := s.Λ) hst.selfDual ha.1 c.S hS
      (by simpa using hH1 1 (one_mem _)) hx hxv (e y) ((z : ℂ) - (D.R.t : ℂ) / 2)
    have hs0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
      have a1 : s.V.rank = D.R.r + k * D.R.t := hst.rank
      have a2 : s'.V.rank = D.R.r + (k + 1) * D.R.t := hst'.rank
      rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, a1, a2]
      push_cast
      ring
    have hw' : ∀ g, wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g := fun _ => rfl
    have hc1' : conj (cf 1) ≠ 0 := by simpa using hc1
    simp only [flatInt, integrand, hs0, hw']
    rw [h5, ← he]
    apply mul_left_cancel₀ hc1'
    linear_combination (GlobalTheory.Doubling.npow (hgtL s.V s.Λ a x) ((z : ℂ) - (D.R.t : ℂ) / 2) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) : ℝ) : ℂ) ^ ((z : ℂ) - (D.R.t : ℂ) / 2)) *
      (rcoef s.ν (fun g => conj (PiLocalization₂.val u₁ v₁ g)) (fun g => conj (PiLocalization₂.val u₂ v₂ g)) (x * ι y) * h2 +
        coefW p.ω m X (p.pt φ) x * h3)

end GlobalTheory.ChainTw.OnePlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) (ζ : GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  first | exact @GlobalTheory.ChainTw.OnePlace.local_factor | exact GlobalTheory.ChainTw.OnePlace.local_factor | (intros; apply GlobalTheory.ChainTw.OnePlace.local_factor <;> assumption)
end
