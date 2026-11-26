module

public import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfKapUnit
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_KapUnit_prod (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (e : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ e s'))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem kapUnit_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) := by
  intro s hs
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hΛ := Pf_KapUnit_prod hR c ell H s hp
  have hP := Pf_KapUnit_prod hR c ell (fun _ => m) s hp
  rw [hκ, map_mul, map_mul]
  refine IsUnit.mul ?_ hP
  rw [Formalism.ExponentWindows.abelian₂]
  exact hΛ

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.EvaluationExpansionAtRoot
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.TensorSumSingleEval
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Free

variable {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι] [DecidableEq ι]

def evK (i : ι) : (ι → LL) ⊗[LL] D →ₗ[LL] D :=
  (TensorProduct.lid LL D).toLinearMap ∘ₗ LinearMap.rTensor D (LinearMap.proj i)

theorem evaluation_tmul (i : ι) (b : ι → LL) (d : D) : evK i (b ⊗ₜ[LL] d) = b i • d := by
  simp [evK]

theorem evaluation_smul (i : ι) (a : ι → LL) (z : (ι → LL) ⊗[LL] D) :
    evK i (a • z) = a i • evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    rw [TensorProduct.smul_tmul', evaluation_tmul, evaluation_tmul, smul_eq_mul, Pi.mul_apply,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem tensor_sum_single_eval (z : (ι → LL) ⊗[LL] D) :
    z = ∑ i, (Pi.single i (1 : LL) : ι → LL) ⊗ₜ[LL] evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    have hb : ∑ i, b i • (Pi.single i (1 : LL) : ι → LL) = b := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    simp_rw [evaluation_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, hb]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem mem_baseChange_iff (X : Submodule LL D) (z : (ι → LL) ⊗[LL] D) :
    z ∈ X.baseChange (ι → LL) ↔ ∀ i, evK i z ∈ X := by
  constructor
  · intro h i
    have h' : z ∈ Submodule.span (ι → LL)
        ((X.map (TensorProduct.mk LL (ι → LL) D 1) : Submodule LL _) : Set ((ι → LL) ⊗[LL] D)) := by
      rw [← Submodule.baseChange_eq_span]; exact h
    clear h
    induction h' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      simpa [evaluation_tmul] using hm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact X.add_mem hx hy
    | smul a x _ hx => rw [evaluation_smul]; exact X.smul_mem _ hx
  · intro h
    rw [tensor_sum_single_eval z]
    exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (h i)

theorem xi_iff (X : ℤ → Submodule LL D) (f : Amb LL (ι → LL) D) :
    f ∈ Xi (ι → LL) X ↔ ∀ i k, evK i (cf f k) ∈ X k := by
  change (∀ k, cf f k ∈ (X k).baseChange (ι → LL)) ↔ _
  simp only [mem_baseChange_iff]
  exact forall_comm

theorem xi_unit_tp (X : ℤ → Submodule LL D) (hX : Monotone X) (a b : PowerSeries (ι → LL)) (hab : a * b = 1)
    (g : ℤ) (f : Amb LL (ι → LL) D) :
    (HahnSeries.ofPowerSeries ℤ (ι → LL) a * tp (ι → LL) g) • f ∈ Xi (ι → LL) X ↔
      f ∈ Xi (ι → LL) (fun i => X (i + g)) := by
  rw [mul_smul, ← xi_shift_holds LL (ι → LL) D X g f]
  constructor
  · intro h
    have h2 := xi_module_structure LL (ι → LL) D X hX b _ h
    rwa [← mul_smul, ← map_mul, show b * a = 1 by rw [mul_comm]; exact hab, map_one, one_smul] at h2
  · intro h
    exact xi_module_structure LL (ι → LL) D X hX a _ h

end Free

end Formalism.MainNotions.N.Ln03.K8
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem inverse_unit_mul_X_pow {Ks : Type} [CommRing Ks] (w : (PowerSeries Ks)ˣ) (m : ℕ) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m)) =
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ)) := by
  have h1 : HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) *
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ht : tp Ks (m : ℤ) * tp Ks (-(m : ℤ)) = 1 := by
    rw [tp, tp, HahnSeries.single_mul_single, add_neg_cancel, mul_one]
    rfl
  let U : (HahnSeries ℤ Ks)ˣ :=
    { val := HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) * tp Ks (m : ℤ)
      inv := HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ))
      val_inv := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht
      inv_val := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht }
  have hU : HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m) = ↑U := by
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
    rfl
  rw [hU, Ring.inverse_unit]
  rfl

theorem evaluation_comm_tensor {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι]
    [DecidableEq ι] (i : ι) (z : D ⊗[LL] (ι → LL)) :
    evK i (TensorProduct.comm LL D (ι → LL) z) = TensorProduct.piScalarRight LL LL D ι z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul d f =>
    rw [TensorProduct.comm_tmul, evaluation_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', map_add (f := _), Pi.add_apply]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}


open Classical in
theorem evaluation_expansion_at_root (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (g : Rs LL PD.p s → D) (ζ : Rs LL PD.p s) : evK ζ (toKsD W s D g) = g ζ := by
  rw [toKsD, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, evaluation_comm_tensor,
    LinearEquiv.apply_symm_apply]

theorem rho_product_unit_mul {ell : ℕ}
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) :
    ∃ w : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s') =
        (w : PowerSeries (KsW W s)) * PowerSeries.X ^ E s := by
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hrest : IsUnit (rhoL hR c s
      (∏ s' ∈ (Finset.range ell).erase s, (baseIdOf hR).Bs.p s' ^ E s')) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_
    rw [map_pow]
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.1 hs'
    exact ((hunits s hs).2 s' (Finset.mem_range.1 hlt) hne).pow _
  obtain ⟨u, hu⟩ := hrest
  refine ⟨ε ^ E s * u, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_mul, ← hu, map_pow, hε]
  push_cast
  ring


open Classical in
theorem levelCond_iff (ell : ℕ)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) (x : C.V) (hx : x ∈ (latOf C).N c)
    (hFil : ∀ s, Antitone (FilD W T c s)) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
        (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s'))) •
      expN Lb s T c ⟨C.t c x, hx⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) ↔
    ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c x, hx⟩ k, Lb.mem T c ζ ⟨C.t c x, hx⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((E s : ℤ) - k) := by
  obtain ⟨w, hw⟩ := rho_product_unit_mul hk1b hunits E s hs
  have hX : Monotone fun i : ℤ => FilD W T c s (-i) := fun i j hij => hFil s (neg_le_neg hij)
  rw [hw, inverse_unit_mul_X_pow, xi_unit_tp _ hX _ _ (Units.inv_mul w), xi_iff]
  refine forall_congr' fun ζ => forall_congr' fun k => ?_
  have hc : cf (expN Lb s T c ⟨C.t c x, hx⟩) k = coefN Lb s T c ⟨C.t c x, hx⟩ k := rfl
  rw [hc, coefN, evaluation_expansion_at_root, show -(k + -(E s : ℤ)) = (E s : ℤ) - k by ring]

end Formalism.MainNotions.N.Ln03.K8
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapFl
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section General

variable {LL Qp : Type} [Field LL] [Field Qp] [Algebra Qp LL]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
  {B₁ B₂ : Type} [AddCommGroup B₁] [Module Qp B₁] [AddCommGroup B₂] [Module Qp B₂]

theorem pfMapFl_map_comm (f : V₁ →ₗ[LL] V₂) (g : B₁ →ₗ[Qp] B₂) (z : V₁ ⊗[Qp] B₁) :
    AlgebraTensorModule.map f (LinearMap.id : B₂ →ₗ[Qp] B₂)
        (AlgebraTensorModule.map (LinearMap.id : V₁ →ₗ[LL] V₁) g z) =
      AlgebraTensorModule.map (LinearMap.id : V₂ →ₗ[LL] V₂) g
        (AlgebraTensorModule.map f (LinearMap.id : B₁ →ₗ[Qp] B₁) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Filt

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

abbrev pfMapFl_Fb : T₁.V ⊗[Qp] B →ₗ[LL] T₂.V ⊗[Qp] B :=
  AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)

abbrev pfMapFl_FdR : T₁.V ⊗[Qp] BdR →ₗ[LL] T₂.V ⊗[Qp] BdR :=
  AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR)

theorem pfMapFl_ιV (z : T₁.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_FdR F (ιV PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f (PD.ι.toLinearMap.restrictScalars Qp) z).symm

theorem pfMapFl_φ (z : T₁.V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_Fb F (φVB PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f PD.φ.toLinearMap z).symm

theorem pfMapFl_φpow (s : ℕ) (z : T₁.V ⊗[Qp] B) :
    ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ s)
        (pfMapFl_Fb F z) =
      pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ s) z) := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, pfMapFl_φ, ih]

theorem pfMapFl_act (g : G) (z : T₁.V ⊗[Qp] B) :
    actVB PD T₂.ρ g (pfMapFl_Fb F z) = pfMapFl_Fb F (actVB PD T₁.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, F.equiv]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem pfMapFl_dcris (z : T₁.V ⊗[Qp] B) (hz : z ∈ Dcris PD T₁.ρ) :
    pfMapFl_Fb F z ∈ Dcris PD T₂.ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [pfMapFl_act, hz g]

theorem pfMapFl_dcrisL (τ₀ : K₀ →ₐ[Qp] LL) (z : T₁.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T₁.ρ τ₀) :
    pfMapFl_Fb F z ∈ DcrisL PD T₂.ρ τ₀ := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  have h2 := hz.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  have h3 : mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c (pfMapFl_Fb F z) =
      pfMapFl_Fb F (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c z) :=
    (pfMapFl_map_comm F.f (LinearMap.mulLeft Qp (algebraMap K₀ B c)) z).symm
  rw [h3, h2 c, map_smul]

theorem pfMapFl_filV (a : ℤ) (z : T₁.V ⊗[Qp] BdR) (hz : z ∈ FilV PD (LL := LL) (V := T₁.V) a) :
    pfMapFl_FdR F z ∈ FilV PD (LL := LL) (V := T₂.V) a := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨AlgebraTensorModule.map F.f LinearMap.id w,
    (pfMapFl_map_comm F.f ((PD.Fil a).restrictScalars Qp).subtype w).symm⟩

theorem pfMapFl_filCris (a : ℤ) (z : T₁.V ⊗[Qp] B) (hz : z ∈ FilCris PD T₁.ρ a) :
    pfMapFl_Fb F z ∈ FilCris PD T₂.ρ a := by
  rw [FilCris, Submodule.mem_inf, Submodule.mem_comap] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  rw [pfMapFl_ιV]
  exact pfMapFl_filV F a _ hz.2

theorem pfMapFl_filD {c : ZMod n} (h : MemD W F c) (s : ℕ) (u : ℤ) (x : Dc W T₁ c)
    (hx : x ∈ FilD W T₁ c s u) : dmapOf h x ∈ FilD W T₂ c s u := by
  have hx' : ιV PD (LL := LL) (V := T₁.V) (x : T₁.V ⊗[Qp] B) ∈ FilLev W T₁ c s u := hx
  obtain ⟨y', hy', hxy⟩ := Submodule.mem_map.1 hx'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hy'
  show ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F (x : T₁.V ⊗[Qp] B)) ∈ FilLev W T₂ c s u
  refine Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨pfMapFl_Fb F y,
    ⟨pfMapFl_filCris F u y hy.1, pfMapFl_dcrisL F _ y hy.2⟩, rfl⟩, ?_⟩
  rw [pfMapFl_φpow, pfMapFl_ιV, pfMapFl_ιV, hxy]

end Filt

section Xi

variable {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}

theorem pfMapFl_ambF_xi (h : MemD W F c) (s : ℕ) (x : Amb LL (KsW W s) (Dc W T₁ c))
    (hx : x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0)) :
    ambF h s x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₂ c) 0) := by
  have hx' : ∀ i, cf x i ∈ (Tw (LL := LL) (D := Dc W T₁ c) 0 i).baseChange (KsW W s) := hx
  show ∀ i, cf (ambF h s x) i ∈ (Tw (LL := LL) (D := Dc W T₂ c) 0 i).baseChange (KsW W s)
  intro i
  have hi := hx' i
  have hc : cf (ambF h s x) i = (dmapOf h).baseChange (KsW W s) (cf x i) := rfl
  rw [hc]
  unfold Tw at hi ⊢
  split_ifs at hi ⊢ with h0
  · rw [Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [Submodule.baseChange_bot, Submodule.mem_bot] at hi ⊢
    rw [hi, map_zero]

theorem pfMapFl_mem_FlS {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ} (Λ f' : PowerSeries O) (s : ℕ)
    (e : LvT hR uZ ιZ T₁ c hΔ ell) :
    e ∈ FlS (hR := hR) (uZ := uZ) (ιZ := ιZ) (T := T₁) (c := c) (hΔ := hΔ) (ell := ell) Λ f' s ↔
      ∃ x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0),
        prL s (Λ • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s f') • x := Iff.rfl

end Xi

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapFl_holds
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) :
    ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s := by
  intro s hs e he
  obtain ⟨x, hx, hex⟩ := (pfMapFl_mem_FlS (hΔ := Hy₁.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s e).1 he
  refine (pfMapFl_mem_FlS (hΔ := Hy₂.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s _).2
    ⟨ambF Mh.memD s x, pfMapFl_ambF_xi Mh.memD s x hx, ?_⟩
  have hsm := (prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell).map_smul
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) e
  erw [← hsm, prL_prEOf Mh s hs, hex, Mh.smul]

theorem cMap_holds (hD : MemD W F c) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hLamP : ∀ k, dmapOf hD (lam₁ k) = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lam₂ l) :
    ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P := by
  intro s _ hk w hw
  have hw' : ∑ k, algebraMap O LL (w k) • lam₁ k ∈ FilD W T₁ c s ((b s : ℕ) : ℤ) := by
    have := hw
    simp only [UL, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      hk, UOf] at this
    exact this
  have hmap := pfMapFl_filD F hD s _ _ hw'
  have hsum : dmapOf hD (∑ k, algebraMap O LL (w k) • lam₁ k) =
      ∑ l, algebraMap O LL (P w l) • lam₂ l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hLamP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, ← LinearMap.toMatrix'_mulVec P w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum]
    refine congrArg (· • lam₂ l) (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul]
    ring
  rw [hsum] at hmap
  show ∑ l, algebraMap O LL (P w l) • lam₂ l ∈ UOf (kind s) (b s) η (FilD W T₂ c s)
  rw [hk]
  exact hmap

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvEquiv
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section Grd

variable {LL Ks : Type} [Field LL] [CommRing Ks] [Algebra LL Ks]

theorem Pf_LvEquiv_grdB_supp (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x : HahnSeries ℤ Ks) :
    (grdB τ a x).support ⊆ x.support := by
  intro i hi h0
  apply hi
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ (x.coeff i) = 0
  rw [h0, map_zero, mul_zero]

theorem Pf_LvEquiv_grdB_mul (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (x y : HahnSeries ℤ Ks) :
    grdB τ a (x * y) = grdB τ a x * grdB τ a y := by
  ext i
  rw [HahnSeries.coeff_mul (x := grdB τ a x)]
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ ((x * y).coeff i) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
  symm
  refine (Finset.sum_subset (fun ij h => ?_) (fun ij hb hs => ?_)).trans (Finset.sum_congr rfl ?_)
  · rw [Finset.mem_antidiagonal] at h ⊢
    exact ⟨Pf_LvEquiv_grdB_supp τ a x h.1, Pf_LvEquiv_grdB_supp τ a y h.2.1, h.2.2⟩
  · rw [Finset.mem_antidiagonal] at hb hs
    by_cases h1 : ij.1 ∈ (grdB τ a x).support
    · by_cases h2 : ij.2 ∈ (grdB τ a y).support
      · exact absurd ⟨h1, h2, hb.2.2⟩ hs
      · have h0 : (grdB τ a y).coeff ij.2 = 0 := by
          by_contra hc
          exact h2 hc
        rw [h0, mul_zero]
    · have h0 : (grdB τ a x).coeff ij.1 = 0 := by
        by_contra hc
        exact h1 hc
      rw [h0, zero_mul]
  intro ij hij
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.1 hij
  change (algebraMap LL Ks ((a ^ ij.1 : LLˣ) : LL) * τ (x.coeff ij.1)) *
    (algebraMap LL Ks ((a ^ ij.2 : LLˣ) : LL) * τ (y.coeff ij.2)) = _
  rw [map_mul τ, ← hsum, zpow_add, Units.val_mul, map_mul]
  ring

theorem Pf_LvEquiv_grdB_one (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) : grdB τ a (1 : HahnSeries ℤ Ks) = 1 := by
  ext i
  change algebraMap LL Ks ((a ^ i : LLˣ) : LL) * τ ((1 : HahnSeries ℤ Ks).coeff i) = _
  simp only [HahnSeries.coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

end Grd

theorem Pf_LvEquiv_cancel {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (X Y Z : A)
    (E₁ E₂ : M) (hX : IsUnit X) (hinv : Z * Y = 1) (key : Y • E₁ = X • E₂) :
    Ring.inverse X • E₁ = Z • E₂ := by
  calc Ring.inverse X • E₁ = (Ring.inverse X * (Z * Y)) • E₁ := by rw [hinv, mul_one]
    _ = (Ring.inverse X * Z) • (Y • E₁) := by rw [smul_smul, mul_assoc]
    _ = (Ring.inverse X * Z) • (X • E₂) := by rw [key]
    _ = Z • E₂ := by
      rw [smul_smul, mul_comm (Ring.inverse X) Z, mul_assoc, Ring.inverse_mul_cancel _ hX, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}


open Classical in
def Pf_LvEquiv_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem Pf_LvEquiv_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvEquiv_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvEquiv_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem Pf_LvEquiv_Φ_rTensor (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (a : (ZMod (PD.p ^ (s + 1)))ˣ) (z : KsW W s ⊗[LL] D) :
    Pf_LvEquiv_Φ W s D (LinearMap.rTensor D (precomp LL PD.p s a).toLinearMap z) =
      fun ζ => Pf_LvEquiv_Φ W s D z (powR LL PD.p s a ζ) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    funext ζ
    simp
  | tmul k d =>
    funext ζ
    simp [Pf_LvEquiv_Φ, TensorProduct.piScalarRightHom_tmul, precomp_apply]
  | add z z' hz hz' =>
    funext ζ
    rw [map_add (f := _), map_add (f := _), hz, hz', map_add (f := _)]
    rfl

variable {T : LocLat G Qp LL O} {c : ZMod n}

theorem Pf_LvEquiv_grd_expN (Lb : LevB W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)
    (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (m a : ℕ), IsPrimitiveRoot ζ (PD.p ^ m) →
      (m : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k =
        (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hK : W.gamK = W.gam)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (s : ℕ) (x : ↥(W.N T)) :
    grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (expN Lb s T c x) =
      expN Lb s T c ⟨W.γD T W.gamK (x : W.DD T), W.N_Γ T W.gamK _ x.2⟩ := by
  apply HahnModule.ext
  funext i
  change (((levW W uZ ιZ s).u ^ i : LLˣ) : LL) •
      LinearMap.rTensor (Dc W T c) (precomp LL PD.p s (redU PD.p s uZ)).toLinearMap
        (coefN Lb s T c x i) = coefN Lb s T c ⟨W.γD T W.gamK (x : W.DD T), W.N_Γ T W.gamK _ x.2⟩ i
  apply (Pf_LvEquiv_Φ W s (Dc W T c)).injective
  rw [LinearEquiv.map_smul, Pf_LvEquiv_Φ_rTensor]
  simp only [coefN, Pf_LvEquiv_Φ_toKsD]
  funext ζ
  apply Subtype.ext
  simp only [Pi.smul_apply, Submodule.coe_smul]
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hv : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gamK : O) -
      (((redU PD.p s uZ : (ZMod (PD.p ^ (s + 1)))ˣ) : ZMod (PD.p ^ (s + 1))).val : LL)) := by
    rw [hK]
    exact huZ (s + 1)
  rw [levB_Γ T hT W.gamK c ζ ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL) (s + 1) _
    hprim hv rfl x]
  congr 1
  rw [hK, Units.val_zpow_eq_zpow_val]
  rfl

theorem equiv_holds {C : Coord W (baseIdOf hR) T} {ell : ℕ} {Λ κ : PowerSeries O} {r : ℕ}
    {lam : Fin r → Dc W T c} (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (m a : ℕ), IsPrimitiveRoot ζ (PD.p ^ m) →
      (m : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k =
        (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hs1 : W.s = 1) (hl : 5 ≤ PD.p)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL))) :
    (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Equiv := by
  have hK : W.gamK = W.gam := W.gamK_eq_one hs1 (by omega)
  intro s _ w hw hγ
  show locM Lb C Hy.delta ell Λ κ Hy.kap Hy.expSemi Hy.locInv ⟨(latOf C).γ c w, hγ⟩ =
    gEL Hy (locM Lb C Hy.delta ell Λ κ Hy.kap Hy.expSemi Hy.locInv ⟨w, hw⟩)
  apply prL_inj
  intro s' hs'
  rw [prL_gEL Hy s' hs', prL_of_lt s' hs', prL_of_lt s' hs']
  have hmL : C.t c (κ • (latOf C).γ c w) ∈ W.N T := Hy.kap _ hγ
  have hmR : C.t c (κ • w) ∈ W.N T := Hy.kap _ hw
  change Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ)) •
      expN Lb s' T c ⟨C.t c (κ • (latOf C).γ c w), hmL⟩ =
    (levW W uZ ιZ s').γ (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ)) •
      expN Lb s' T c ⟨C.t c (κ • w), hmR⟩)
  by_cases hX : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ))
  · rw [Level.γ, graded_semilinear_holds,
      Pf_LvEquiv_grd_expN Lb uZ ιZ hT levB_Γ hK huZ s' ⟨C.t c (κ • w), hmR⟩]
    apply Pf_LvEquiv_cancel _ (HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' ((baseIdOf hR).Bs.γ κ)))
      _ _ _ hX
    · rw [← Hy.gamRho s' κ, ← Pf_LvEquiv_grdB_mul, Ring.inverse_mul_cancel _ hX, Pf_LvEquiv_grdB_one]
    · have hN : W.γD T W.gamK (C.t c (κ • w)) ∈ W.N T := W.N_Γ T W.gamK _ hmR
      rw [← Hy.expSemi s' ((baseIdOf hR).Bs.γ κ) ⟨_, hmL⟩ ((W.N T).smul_mem _ hmL),
        ← Hy.expSemi s' κ ⟨_, hN⟩ ((W.N T).smul_mem _ hN)]
      congr 1
      apply Subtype.ext
      change (baseIdOf hR).d ((baseIdOf hR).Bs.γ κ) • C.t c (κ • (latOf C).γ c w) =
        (baseIdOf hR).d κ • W.γD T W.gamK (C.t c (κ • w))
      rw [← t_γ, (latOf C).γ_semi, C.t_smul, C.t_smul]
      exact smul_comm _ _ _
  · rw [Ring.inverse_non_unit _ hX, zero_smul, zero_smul, map_zero]

theorem Pf_LvEquiv_unit_lam (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))) := by
  rw [Formalism.ExponentWindows.abelian₂, map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem locLIs_holds {C : Coord W (baseIdOf hR) T} {ell : ℕ} {Λ κ : PowerSeries O} {r : ℕ}
    {lam : Fin r → Dc W T c} (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (H : ℕ → ℕ) (hΛ : Λ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocLIs lam := by
  subst hΛ
  intro s hs y
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hU := Pf_LvEquiv_unit_lam hR c ell H s hp
  show prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell •
      locLM Hy.delta ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) lam Hy.loclInv y) =
    ∑ k, HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (y k)) • cstD (KsW W s) (lam k)
  rw [prL_smul, prL_of_lt s hs]
  change HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)) •
      locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) lam s y = _
  rw [locLF, smul_smul, Ring.mul_inverse_cancel _ hU, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvGam
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section GrdComm

variable {LL Ks D : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]

theorem Pf_LvGam_grd_comm (σ τ : Ks ≃ₐ[LL] Ks) (a b : LLˣ) (h : ∀ x, σ (τ x) = τ (σ x))
    (f : Amb LL Ks D) : grd τ b (grd σ a f) = grd σ a (grd τ b f) := by
  apply HahnModule.ext
  funext i
  change cf (grd τ b (grd σ a f)) i = cf (grd σ a (grd τ b f)) i
  rw [SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, SlopeTestRemainingChoices.cf_grd, map_smul, map_smul, smul_smul, smul_smul,
    SlopeTestRemainingChoices.tD_comm σ τ h, mul_comm]

end GrdComm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvGam_στ (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (s : ℕ) (j : DeltaT PD.p) (x : KsW W s) :
    (levW W uZ ιZ s).σ ((levW W uZ ιZ s).τ j x) = (levW W uZ ιZ s).τ j ((levW W uZ ιZ s).σ x) := by
  funext ζ
  show x (powR LL PD.p s (redU PD.p s j.1) (powR LL PD.p s (redU PD.p s uZ) ζ)) =
    x (powR LL PD.p s (redU PD.p s uZ) (powR LL PD.p s (redU PD.p s j.1) ζ))
  rw [powR_powR, powR_powR, mul_comm]

theorem gamInv_holds (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O) (c : ZMod n) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv ((levW W uZ ιZ s).γ f) := by
  intro s f hf j
  show grd ((levW W uZ ιZ s).τ j) ((levW W uZ ιZ s).a j) (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f) =
    grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u f
  rw [Pf_LvGam_grd_comm _ _ _ _ (Pf_LvGam_στ uZ ιZ s j)]
  exact congrArg (grd (levW W uZ ιZ s).σ (levW W uZ ιZ s).u) (hf j)

theorem Pf_LvGam_coeff_neg {Ks : Type} [CommRing Ks] (x : PowerSeries Ks) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ Ks x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem gamRho_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (c : ZMod n)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hK : W.gamK = W.gam)
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL))) :
    ∀ (s : ℕ) (a : PowerSeries O),
      grdB (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)) =
        HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.γ a)) := by
  intro s a
  refine HahnSeries.ext (funext fun i => ?_)
  change algebraMap LL (KsW W s) (((levW W uZ ιZ s).u ^ i : LLˣ) : LL) *
    (levW W uZ ιZ s).σ ((HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)).coeff i) = _
  rcases i with k | k
  · rw [Int.ofNat_eq_natCast, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
    funext ζ
    have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
      (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
    have hv : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gamK : O) -
        (((redU PD.p s uZ : (ZMod (PD.p ^ (s + 1)))ˣ) : ZMod (PD.p ^ (s + 1))).val : LL)) := by
      rw [hK]
      exact huZ (s + 1)
    have hL := lev_Γ W.gamK c ζ ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL) (s + 1) _
      hprim hv rfl (fun _ => (baseIdOf hR).ι a)
    have hR1 : PowerSeries.coeff k (rhoL hR c s ((baseIdOf hR).Bs.γ a)) ζ =
        PowerSeries.coeff k (W.lev c ζ (W.γA W.gamK (fun _ => (baseIdOf hR).ι a))) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      show PowerSeries.coeff k (W.lev c ζ (fun _ => (baseIdOf hR).ι ((baseIdOf hR).Bs.γ a))) = _
      rw [(baseIdOf hR).ι_γ a]
      rfl
    have hL1 : PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) =
        PowerSeries.coeff k (W.lev c ((powR LL PD.p s (redU PD.p s uZ) ζ : Rs LL PD.p s) : LL)
          (fun _ => (baseIdOf hR).ι a)) := by
      rw [rhoL, RingHom.comp_apply, coeff_psPi]
      rfl
    rw [hR1, hL, PowerSeries.coeff_rescale, ← hL1, hK]
    show (((levW W uZ ιZ s).u ^ (k : ℤ) : LLˣ) : LL) *
      PowerSeries.coeff k (rhoL hR c s a) (powR LL PD.p s (redU PD.p s uZ) ζ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · rw [Pf_LvGam_coeff_neg, Pf_LvGam_coeff_neg, map_zero, mul_zero]

end Formalism.MainNotions.N.Ln03.Pf
end
end
