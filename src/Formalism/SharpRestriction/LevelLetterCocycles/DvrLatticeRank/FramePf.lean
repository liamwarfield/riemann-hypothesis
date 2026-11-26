module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfRec

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBA
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_βα_core (Bs : FramepfBas W T) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c)) (P R S : Fin Bs.r → Fin Bs.r → LetA O n)
    (hS : ∀ m k, S m k ∈ W.AΔ) (lam : O) (hPR : ∀ j k, ∑ m, P j m * R m k =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S j k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    Φ (Ψ x) - lam • x ∈ JLA W T π' Eπ h' M c := by
  choose a haΔ ha using (framepf_mem_toLA π' c eb _).1 hx
  have hee : (letE c : LetA O n) * letE c = letE c := Formalism.MainNotions.LiftingTheory.wmap_letE_idem c
  have hx' : algebraMap (LetA O n) W.EE (Eπ ^ h') • x =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a k) ⊗ₜ[O] eb k := by
    rw [← framepf_smulLA_alg, ← (Algebra.TensorProduct.basis W.EE eb).sum_repr (smulLA W T π' c _ x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hm : ∀ j, ∑ k, a k * S j k ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS j k)
  refine ⟨∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * ∑ k, a k * S j k) ⊗ₜ[O] eb j,
    ⟨∑ j, (⟨_, hm j⟩ : ↥W.AΔ) ⊗ₜ ⟨eb j, trivial⟩, by rw [map_sum]; rfl⟩, ?_⟩
  obtain ⟨Λ, hΛ⟩ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact huE.pow _
  have hcan : ∀ z z' : LA W T π' c, algebraMap (LetA O n) W.EE (Eπ ^ h') • z =
      algebraMap (LetA O n) W.EE (Eπ ^ h') • z' → z = z' := by
    intro z z' h
    have := congrArg (fun w => ((Λ⁻¹ : W.EEˣ) : W.EE) • w) h
    simpa only [← hΛ, smul_smul, Units.inv_mul, one_smul] using this
  apply hcan
  have h1 : Ψ (algebraMap (LetA O n) W.EE (Eπ ^ h') • x) =
      ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) • W.φD T (Bs.b m) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ j, ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
      algebraMap O (LetA O n) lam * ((letE c : LetA O n) * a j) +
        Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h') * ((letE c : LetA O n) * ∑ k, a k * S j k)) := by
    intro j
    have : ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
        ∑ k, (letE c : LetA O n) * a k * ∑ m, P j m * R m k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hPR, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · linear_combination (algebraMap O (LetA O n) lam * a j) * hee
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [smul_sub, ← map_smul Φ, ← map_smul Ψ, h1, hΦ, smul_comm _ lam x, hx', framepf_smulLA_alg,
    Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3, ← algebraMap_smul W.EE lam, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  simp only [TensorProduct.smul_tmul', smul_eq_mul]
  rw [← TensorProduct.sub_tmul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, add_sub_cancel_left]

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAB
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_αβ_core (Bs : FramepfBas W T) (hT : IsCrys PD T.ρ) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ)
    (eb : Fin Bs.r → LcQ W T π' c) (P R S : Fin Bs.r → Fin Bs.r → LetA O n) (hS : ∀ m k, S m k ∈ W.AΔ)
    (lam : O) (hRP : ∀ m k, ∑ j, R m j * P j k =
      (if m = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S m k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) : Ψ (Φ y) - lam • y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨h1, hΔ, hl⟩ := (mem_LamPS W T Eπ h' c y).1 hy
  obtain ⟨a, haΔ, hac, ha⟩ := framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1)
    (fun δ hδ => by rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ])
    (by rw [smul_comm, hl])
  refine ⟨∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m), framepf_mem_Pc Bs c _
    (fun m => Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS m k)) (fun m => ?_), ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hac]
  show (π' ^ M * Eπ ^ (3 * h')) • (∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m)) = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  have h2 : Eπ ^ h' • Ψ (Φ y) = ∑ m, (∑ j, (∑ k, a k * P j k) * R m j) • W.φD T (Bs.b m) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← algebraMap_smul W.EE, ← map_smul, ← map_smul, algebraMap_smul, ha, hΦ, map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ m, ∑ j, (∑ k, a k * P j k) * R m j =
      algebraMap O (LetA O n) lam * a m + π' ^ M * Eπ ^ (4 * h') * ∑ k, a k * S m k := by
    intro m
    have : ∑ j, (∑ k, a k * P j k) * R m j = ∑ k, a k * ∑ j, R m j * P j k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hRP, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · rw [mul_left_comm, mul_comm (a m), hac]
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : Eπ ^ h' • (lam • y) = ∑ m, (algebraMap O (LetA O n) lam * a m) • W.φD T (Bs.b m) := by
    rw [smul_comm, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_smul, algebraMap_smul]
  rw [smul_sub, smul_sub, h2, h4, smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [h3, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul (LetA O n) (W.φD T (Bs.b m)) using 2
  ring

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBeta
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_smulLA_eq (π' : LetA O n) (c : ZMod n) (a : LetA O n) (z : W.EE ⊗[O] LcQ W T π' c) :
    smulLA W T π' c a z = algebraMap (LetA O n) W.EE a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rw [framepf_smulLA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

variable (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_φA_ι_mem (g : PowerSeries O) : W.φA (framepf_ι π' (c - 1) g) ∈ W.AΔ := by
  intro δ hδ
  rw [← LocWach.φA_γA, framepf_ι_Δ π' hπ0 hΔπ γ0 _ g δ hδ]

theorem framepf_φD_vec (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    W.φD T (framepf_vec Bs π' (c - 1) H k) =
      ∑ m, W.φA (framepf_ι π' (c - 1) (H m k)) • W.φD T (Bs.b m) := by
  unfold framepf_vec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => framepf_φD_smul _ _

def framepf_ebar (j : Fin Bs.r) : LcQ W T π' c :=
  (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).symm (Pi.single j 1)

theorem framepf_hh_ebar (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j : Fin Bs.r) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j) =
      framepf_vec Bs π' (c - 1) H j := by
  unfold framepf_hh framepf_ebar
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Fintype.linearCombination_apply_single, one_smul]

def framepf_Ψβ (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) :
    W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c :=
  βφ.constr W.EE fun k => ∑ j, algebraMap (LetA O n) W.EE (W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
    framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j

variable (βφ : Module.Basis (Fin Bs.r) W.EE (W.DD T)) (hβφ : ∀ k, βφ k = W.φD T (Bs.b k))

include hβφ in
theorem framepf_Ψβ_sum (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (a : Fin Bs.r → LetA O n) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
  have e1 : ∀ k, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F (a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (a k * W.φA (framepf_ι π' (c - 1) (F j k))) ⊗ₜ
        framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := by
    intro k
    rw [← algebraMap_smul W.EE (a k), LinearMap.map_smul, ← hβφ k]
    unfold framepf_Ψβ
    rw [Module.Basis.constr_basis, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← TensorProduct.sum_tmul, ← map_sum]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_Pc (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (p : W.DD T) (hp : p ∈ PcS W T c) :
    ∃ t, framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F p = toLA W T π' c ⊤ t := by
  obtain ⟨a, haΔ, hac, hap⟩ := framepf_Pc_coord Bs hT c p hp
  have hmem : ∀ j, ∑ k, a k * W.φA (framepf_ι π' (c - 1) (F j k)) ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (haΔ k) (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨∑ j, (⟨_, hmem j⟩ : ↥W.AΔ) ⊗ₜ (⟨framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j, trivial⟩ :
    ↥(⊤ : Submodule O (LcQ W T π' c))), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hap, framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [framepf_toLA_tmul]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, hac k]

variable (Eπ : LetA O n) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hEΔ : ∀ δ ∈ W.DelF, W.γA δ Eπ = Eπ) (h' M : ℕ)


include hπ0 hΔπ γ0 hβφ hEΔ in
theorem framepf_Ψβ_Lam (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamPS] at hy
  obtain ⟨h1, hΔ, hl⟩ := hy
  have hP : Eπ ^ h' • y ∈ PcS W T c := by
    unfold PcS
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.restrictScalars_mem _ _ _).2 h1, ?_⟩, ?_⟩
    · rw [mem_DelS]
      intro δ hδ
      rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ]
    · rw [mem_letS, smul_smul, mul_comm, ← smul_smul, hl]
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F _ hP
  refine Submodule.mem_comap.2 ⟨t, ?_⟩
  rw [← ht, framepf_smulLA_eq, ← LinearMap.map_smul, algebraMap_smul]


include hπ0 hΔπ γ0 hβφ in
theorem framepf_Ψβ_J (hT : IsCrys PD T.ρ) (F : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (y : W.DD T) (hy : y ∈ JP W T π' Eπ h' M c) :
    framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ F y ∈ JLA W T π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht⟩ := framepf_Ψβ_Pc Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ hT F p hp
  refine Submodule.mem_map.2 ⟨_, ⟨t, rfl⟩, ?_⟩
  rw [framepf_smulLA_eq, ← ht, ← LinearMap.map_smul, algebraMap_smul]
  rfl

include hπ0 in
theorem framepf_ι_X_pow_mul (k : ℕ) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.X ^ k * g) = π' ^ k * framepf_ι π' (c - 1) g := by
  induction k with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, framepf_ι_mul π' (c - 1) (hπ0 _), ih, framepf_ι_X π' (c - 1) (hπ0 _),
      pow_succ']
    have := framepf_letE_ι π' (c - 1) hπ0 g
    calc letE (c - 1) * π' * (π' ^ k * framepf_ι π' (c - 1) g)
        = π' * π' ^ k * (letE (c - 1) * framepf_ι π' (c - 1) g) := by ring
      _ = π' * π' ^ k * framepf_ι π' (c - 1) g := by rw [this]


include hπ0 in
theorem framepf_φA_ι_entry (M : ℕ) (lam : O) (K : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (j k : Fin Bs.r) :
    W.φA (framepf_ι π' (c - 1) ((PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K) j k)) =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) +
        W.φA π' ^ M * W.φA (framepf_ι π' (c - 1) (K j k)) := by
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    framepf_ι_add π' (c - 1) (hπ0 _), map_add, framepf_ι_X_pow_mul π' c hπ0, map_mul, map_pow]
  congr 1
  by_cases h : j = k
  · subst h
    rw [Matrix.one_apply_eq, mul_one, framepf_ι_C π' (c - 1) (hπ0 _), map_mul,
      Formalism.MainNotions.LiftingTheory.wmap_φA_letE, AlgHom.commutes, if_pos rfl, mul_comm]
  · rw [Matrix.one_apply_ne h, mul_zero, framepf_ι_zero π' (c - 1) hπ0, map_zero, if_neg h]

include hπ0 in
theorem framepf_φA_ι_matmul (F H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (j k : Fin Bs.r) :
    ∑ m, W.φA (framepf_ι π' (c - 1) (F j m)) * W.φA (framepf_ι π' (c - 1) (H m k)) =
      W.φA (framepf_ι π' (c - 1) ((F * H) j k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, framepf_ι_sum π' (c - 1) hπ0, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), map_mul]

end Local

end Formalism.MainNotions.N.Ln34

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

theorem framepf_back (hT : IsCrys PD T.ρ) (Eπ : LetA O n) (h' M : ℕ)
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ) (u : LetA O n) (huΔ : u ∈ W.AΔ)
    (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u) :
    FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ h' M := by
  intro H H' K₁ K₂ lam h₁ h₂
  obtain ⟨βφ, hβφ⟩ := framepf_phiBasis Bs hT
  let eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c) :=
    Module.Basis.ofEquivFun (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu)
  have heb : ∀ j, eb j = framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := fun j => by
    simp only [eb, Module.Basis.coe_ofEquivFun, framepf_ebar]
  have hΨ : ∀ (e : W.EE) j, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ eb j) =
      e • ∑ m, W.φA (framepf_ι π' (c - 1) (H m j)) • W.φD T (Bs.b m) := fun e j => by
    rw [heb, framepf_Ψα_tmul, framepf_hh_ebar, framepf_φD_vec]
  have hΦ : ∀ a : Fin Bs.r → LetA O n,
      framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H' (∑ k, a k • W.φD T (Bs.b k)) =
        ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (H' j k))) ⊗ₜ eb j :=
    fun a => by simp only [heb]; exact framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ H' a
  have hS : ∀ (Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) m k,
      u * W.φA (framepf_ι π' (c - 1) (Km m k)) ∈ W.AΔ := fun Km m k =>
    W.AΔ.mul_mem huΔ (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H',
    framepf_Ψβ_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ hEΔ h' hT H',
    framepf_Ψβ_J Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ h' M hT H',
    framepf_βα_core Bs π' Eπ h' M c huE eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₁) lam (fun j k => ?_) _ _ hΨ hΦ,
    framepf_αβ_core Bs hT π' Eπ h' M c huE hEΔ eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₂) lam (fun j k => ?_) _ _ hΨ hΦ⟩
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₁, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₂, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]

end Local


set_option maxHeartbeats 1000000 in
theorem frame_pf : FrameStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hR h' hh' c
  exact framepf_rec D HW F Cm hA.1 l hl K LL hG π' E hR h' hh' c
    fun T hT Bs hπ0 hΔπ hR2 γ0 hu huE hEΔ u huΔ hφ =>
      framepf_back Bs π' c hπ0 hΔπ hR2 γ0 hu hT _ h' _ huE hEΔ u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
