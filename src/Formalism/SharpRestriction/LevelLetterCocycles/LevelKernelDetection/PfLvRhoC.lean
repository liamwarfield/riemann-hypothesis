module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvRhoC
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

theorem rhoC_holds (hR : Ring9 W) (c : ZMod n) (s : ℕ) (a : O) :
    rhoL hR c s (PowerSeries.C a) =
      PowerSeries.C (algebraMap LL (KsW W s) (algebraMap O LL a)) := by
  ext k ζ
  have hC : (PowerSeries.C a : PowerSeries O) = algebraMap O (PowerSeries O) a := by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h1 : PowerSeries.coeff k (rhoL hR c s (PowerSeries.C a)) ζ =
      PowerSeries.coeff k (rhoZ W c ζ ((baseIdOf hR).ι (PowerSeries.C a))) := by
    have h := congrArg (PowerSeries.coeff k) (map_eval_rhoL hR c s (PowerSeries.C a) ζ)
    rw [PowerSeries.coeff_map] at h
    exact h
  rw [h1, hC, AlgHom.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C,
    PowerSeries.coeff_C]
  split_ifs <;> rfl

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvExp
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Conv

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem Pf_LvExp_coeff_neg (x : PowerSeries R) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

theorem Pf_LvExp_coeff_smul (x : PowerSeries R) (y : HahnModule ℤ R M) (m : ℤ)
    (hy : ∀ k < m, ((HahnModule.of R).symm y).coeff k = 0) (k : ℤ) (N : ℕ) (hN : k - m < N) :
    ((HahnModule.of R).symm (HahnSeries.ofPowerSeries ℤ R x • y)).coeff k =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j x • ((HahnModule.of R).symm y).coeff (k - j) := by
  rw [HahnModule.coeff_smul]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => ((j : ℤ), k - j)) ?_ ?_ ?_ ?_
  · intro j _ hj
    have h1 : PowerSeries.coeff j x ≠ 0 := fun h => hj (by rw [h, zero_smul])
    have h2 : ((HahnModule.of R).symm y).coeff (k - j) ≠ 0 := fun h => hj (by rw [h, smul_zero])
    rw [Finset.mem_vaddAntidiagonal]
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply_coeff]
      exact h1
    · rw [HahnSeries.mem_support]
      exact h2
    · show (j : ℤ) + (k - j) = k
      ring
  · intro j _ _ j' _ _ h
    exact_mod_cast (Prod.mk.inj h).1
  · intro ij hij hne
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    obtain ⟨i, i'⟩ := ij
    simp only at h1 h2 h3 hne
    cases i with
    | negSucc t => exact absurd (Pf_LvExp_coeff_neg x t) ((HahnSeries.mem_support _ _).1 h1)
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, vadd_eq_add] at h3 hne
      have hi' : i' = k - j := by omega
      have hm' : m ≤ i' := by
        by_contra hlt
        push Not at hlt
        exact (HahnSeries.mem_support _ _).1 h2 (hy _ hlt)
      refine ⟨j, Finset.mem_range.2 (by omega), ?_, ?_⟩
      · rw [← hi']
        rwa [HahnSeries.ofPowerSeries_apply_coeff] at hne
      · simp [hi']
  · intro j _ _
    dsimp only
    rw [HahnSeries.ofPowerSeries_apply_coeff]

theorem Pf_LvExp_finsum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • g (k - j) = ∑ j ∈ Finset.range N, PowerSeries.coeff j f • g (k - j) := by
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hj
  show PowerSeries.coeff j f • g (k - j) = 0
  rw [hg (k - j) (by omega), smul_zero]

end Conv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem Pf_LvExp_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab


open Classical in
def Pf_LvExp_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem Pf_LvExp_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvExp_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem Pf_LvExp_Φ_smul (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (f : KsW W s)
    (z : KsW W s ⊗[LL] D) (ζ : Rs LL PD.p s) :
    Pf_LvExp_Φ W s D (f • z) ζ = f ζ • Pf_LvExp_Φ W s D z ζ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul g d => simp [Pf_LvExp_Φ, TensorProduct.smul_tmul', TensorProduct.piScalarRightHom_tmul, mul_smul]
  | add z z' hz hz' => rw [smul_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hz, hz', smul_add]

theorem Pf_LvExp_coeff_expN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) : ((HahnModule.of (KsW W s)).symm (expN Lb s T c y)).coeff k = coefN Lb s T c y k :=
  rfl

theorem Pf_LvExp_Φ_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) (ζ : Rs LL PD.p s) :
    ((Pf_LvExp_Φ W s (Dc W T c) (coefN Lb s T c y k) ζ : Dc W T c) : T.V ⊗[Qp] B) =
      Lb.levB T c ζ y k := by
  simp only [coefN, Pf_LvExp_Φ_toKsD]

theorem expSemi_holds (Lb : LevB W) (hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k)) :
    ExpSemi Lb hR T c := by
  intro s a y hy
  obtain ⟨m, hm⟩ := bdd_coefN Lb s T c y
  have hm' : ∀ k < m, coefN Lb s T c y k = 0 := fun k hk => by
    by_contra h
    exact absurd (hm h) (not_le.2 hk)
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [Pf_LvExp_coeff_smul _ _ m (fun k' hk' => by rw [Pf_LvExp_coeff_expN]; exact hm' k' hk') k N hN]
  simp only [Pf_LvExp_coeff_expN]
  apply (Pf_LvExp_Φ W s (Dc W T c)).injective
  funext ζ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp only [Pf_LvExp_Φ_smul]
  apply Subtype.ext
  apply Pf_LvExp_ιV_inj (PD := PD) T
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Pf_LvExp_Φ_coefN]
  simp only [← levN_eq]
  have hg : ∀ k' < m, W.levN T c ζ y k' = 0 := fun k' hk' => by
    rw [levN_eq, ← Pf_LvExp_Φ_coefN Lb s T c y k' ζ, hm' k' hk', map_zero]
    simp
  rw [show (⟨_, hy⟩ : ↥(W.N T)) = (baseIdOf hR).d a • y from rfl, W.levN_smul,
    Pf_LvExp_finsum _ _ m hg k N hN]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := congrArg (PowerSeries.coeff j) (map_eval_rhoL hR c s a ζ)
  rw [PowerSeries.coeff_map] at h
  exact h.symm

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvLoc
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

namespace LvLoc


open Classical in
def evKD (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem evKD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (F : Rs LL PD.p s → D) :
    evKD W s D (toKsD W s D F) = F := by
  classical
  show TensorProduct.piScalarRight LL LL D _ (TensorProduct.comm LL (KsW W s) D
    (TensorProduct.comm LL D (KsW W s) ((TensorProduct.piScalarRight LL LL D _).symm F))) = F
  rw [← TensorProduct.comm_symm LL (KsW W s) D, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem evKD_tD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (z : KsW W s ⊗[LL] D) (ξ : Rs LL PD.p s) :
    evKD W s D (tD D (precomp LL PD.p s b) z) ξ = evKD W s D z (powR LL PD.p s b ξ) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f d =>
    simp [evKD, tD, LinearMap.rTensor_tmul, TensorProduct.piScalarRightHom_tmul, precomp_apply]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hz, hz', map_add (f := _), Pi.add_apply]

theorem tD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (F : Rs LL PD.p s → D) :
    tD D (precomp LL PD.p s b) (toKsD W s D F) = toKsD W s D (fun ξ => F (powR LL PD.p s b ξ)) := by
  apply (evKD W s D).injective
  funext ξ
  rw [evKD_tD, evKD_toKsD, evKD_toKsD]

theorem dvd_sub_val (s : ℕ) (ω : ℤ_[PD.p]ˣ) :
    (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ (ω : ℤ_[PD.p]) - ((redU PD.p s ω : ZMod (PD.p ^ (s + 1))).val : ℤ_[PD.p]) := by
  have : NeZero (PD.p ^ (s + 1)) := ⟨(pos_pow PD.p s).ne'⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_eq_zero]
  rfl

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

theorem expN_inv (Lb : LevB W) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)))
    (s : ℕ) (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) :
    (levW W uZ ιZ s).Inv (D := Dc W T c) (expN Lb s T c y) := by
  intro j
  obtain ⟨g, hgD, hgχ⟩ := hω j
  apply HahnModule.ext
  funext k
  show ((((levW W uZ ιZ s).a j) ^ k : LLˣ) : LL) •
      tD (Dc W T c) (precomp LL PD.p s (redU PD.p s j.1)) (coefN Lb s T c y k) = coefN Lb s T c y k
  simp only [coefN]
  rw [tD_toKsD, ← map_smul]
  congr 1
  funext ζ
  apply Subtype.ext
  have hx : W.γD T g (y : W.DD T) ∈ W.N T := by rw [hy g hgD]; exact y.2
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hval : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) -
      (((redU PD.p s j.1 : ZMod (PD.p ^ (s + 1))).val : ℕ) : LL)) := by
    rw [hgχ, ← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub]
    exact hv s _ (dvd_sub_val s j.1)
  have key := levB_Γ T hT g c ζ _ (s + 1) _ hprim hval rfl y hx k
  have hyy : (⟨W.γD T g (y : W.DD T), hx⟩ : ↥(W.N T)) = y := Subtype.ext (hy g hgD)
  rw [hyy, hgχ] at key
  rw [Pi.smul_apply, SetLike.val_smul]
  show _ • Lb.levB T c (powR LL PD.p s (redU PD.p s j.1) ζ : LL) y k = Lb.levB T c ζ y k
  rw [key, Units.val_zpow_eq_zpow_val]
  rfl

end LvLoc

open LvLoc

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

theorem locInv_holds (Lb : LevB W) (C : Coord W (baseIdOf hR) T) (κ : PowerSeries O)
    (hΔ : DeltaRho hR uZ ιZ c) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z))) :
    LocInv Lb C c uZ ιZ κ := by
  intro s x hx j
  have he := expN_inv (c := c) (uZ := uZ) Lb hT levB_Γ hω hv s ⟨C.t c x, hx⟩ fun δ hδ => C.t_Δ c x δ hδ
  have hz := hΔ s j κ
  show Level.δ (levW W uZ ιZ s) j
      (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩) =
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩
  by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at hz ⊢
    rw [Ring.inverse_unit]
    have h1 : (u : HahnSeries ℤ (KsW W s)) • Level.δ (levW W uZ ιZ s) j
        (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        expN Lb s T c ⟨C.t c x, hx⟩ := by
      conv_lhs => rw [← hz]
      rw [Level.δ, ← graded_semilinear_holds, smul_smul, Units.mul_inv, one_smul]
      exact he j
    calc Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        ((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • ((u : HahnSeries ℤ (KsW W s)) •
          Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [h1]
  · rw [Ring.inverse_non_unit _ hu, zero_smul]
    exact map_zero _

namespace LvLoc

theorem phiIt_mem {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Formalism.ExponentWindows.E.Lat Bs n V) (m : ℕ) (hP : ∀ i, L.P5M i m) (i : ZMod n) :
    ∀ (k : ℕ), ∀ v ∈ L.N i, (∏ s ∈ Finset.range k, Bs.p s ^ m) • L.phiIt i k v ∈ L.N (i + (k : ZMod n))
  | 0 => fun v hv => by simpa [Formalism.ExponentWindows.E.Lat.phiIt] using hv
  | k + 1 => fun v hv => by
    have ih := phiIt_mem L m hP i k v hv
    have e1 : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    have h := hP (i + ((k + 1 : ℕ) : ZMod n)) _ (by rw [e1]; exact ih)
    rw [L.φ_semi, smul_smul] at h
    have e : (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) =
        Bs.q ^ m * Bs.φ (∏ s ∈ Finset.range k, Bs.p s ^ m) := by
      rw [Finset.prod_range_succ', map_prod, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [map_pow, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']
    show (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) • L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v) ∈
      L.N (i + ((k + 1 : ℕ) : ZMod n))
    rw [e]
    exact h

theorem latOf_P5M_of_p5_of_le (C : Coord W (baseIdOf hR) T) {M h : ZMod n → ℕ} (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m) (i : ZMod n) : (latOf C).P5M i m := by
  intro x hx
  show C.t i ((baseIdOf hR).Bs.q ^ m • (latOf C).φ i x) ∈ W.N T
  rw [C.t_smul, map_pow, BaseId.d_q]
  have h1 : C.t i ((latOf C).φ i x) = W.φD T (C.t (i - 1) x) := by
    show (((C.θ i) ((C.θ i).symm (φl W T i (C.θ (i - 1) x))) : ↥(DDl W T i)) : W.DD T) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [h1]
  have h2 : C.t (i - 1) x ∈ W.Nl T (i - 1) := Submodule.mem_map.2 ⟨_, hx, C.t_letter (i - 1) x⟩
  have h4 := qP_pow_mem hs hRA (W.N T) (hp5.1 i _ h2)
  have e : qP W ^ m = qP W ^ (m - M i) * qP W ^ M i := by rw [← pow_add, Nat.sub_add_cancel (hm i)]
  rw [e, mul_smul]
  exact (W.N T).smul_mem _ h4

end LvLoc

theorem kap_holds (C : Coord W (baseIdOf hR) T) (ell : ℕ) (Λ κ : PowerSeries O) {M h : ZMod n → ℕ}
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) (hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m)
    (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    ∀ w ∈ (latOf C).W c ell Λ, κ • w ∈ (latOf C).N c := by
  intro w hw
  have hL : ∀ i, (latOf C).P5M i m := latOf_P5M_of_p5_of_le C (hP5 T M h hT hJ) hs hRA m hm
  rw [hκ, mul_comm, mul_smul]
  have hw' : Λ • w ∈ (latOf C).pull (c - (ell : ZMod n)) ell := hw
  have hc : c - (ell : ZMod n) + (ell : ZMod n) = c := sub_add_cancel _ _
  refine Submodule.span_induction (p := fun y _ =>
    (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) • y ∈ (latOf C).N c) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨u, hu, rfl⟩
    have := phiIt_mem (latOf C) m hL (c - (ell : ZMod n)) ell u hu
    rwa [hc] at this
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz
  · intro a y _ hy
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hy

end Formalism.MainNotions.N.Ln03.Pf
end
end
