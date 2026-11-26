module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivatives
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Expansion

open PowerSeries GlobalTheory.HWL.Ser

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
  {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

noncomputable def evOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)


omit [CharZero L] [Algebra ℚ L] in
theorem lev_eq (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (a : LetA O n) :
    W.lev i ζ a = evOne W i ζ (a i) := by
  have h := W.lev_letter i ζ (a - fun _ => a i) (by simp)
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem evOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    evOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := ode_unique 1 (by rw [h1, map_one, one_mul])
    (by rw [derivative_exp, map_one, one_mul]) (by rw [h0, constantCoeff_exp])
  rw [← hE, ← h2, lev_eq, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw (W : LocWach PD L O v n) (hp : PD.p = l) (c : W.Gam → ℤ_[l])
    (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O)) (hφ : W.φ₀ = GlobalTheory.Cyc.phi l O)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (c g))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    have e : W.γA g f i = GlobalTheory.Fon.gam O (c g) (f i) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← hγ]; rfl
    rw [lev_eq, lev_eq, e]
    exact ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (evOne_X W i ⟨j, h⟩)
      (evOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    have e : W.φA f i = GlobalTheory.Fon.gam O (l : ℤ_[l]) (f (i - 1)) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← GlobalTheory.Cyc.phi, ← hφ]; rfl
    have := ev_gam H (j := j) (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (evOne_X W i ⟨j, h⟩)
      (evOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [map_natCast] at this
    rw [lev_eq, lev_eq, e, hp]
    exact this

end Generic

theorem levLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  intro D HW l _ K s LL h W
  obtain ⟨χ, h1⟩ := exists_padic_char (LL := LL) (gamOf W ((HW l).W_s K s LL h))
  obtain ⟨_, hcomp, -, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hl : (l : ↥(OL LL)) ≠ 0 := fun h0 => by
    have h2 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  have key := fun g : W.Gam => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl hu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l])
    (by rw [W.φ₀_X, W.q₀_def, (D.loc l).PD_p K]) (W.γ₀_comm g) (W.γ₀_X g).1 ((W.γ₀_X g).2.trans (h1 g).symm)
  refine levLaws_of_evLaw W ((D.loc l).PD_p K) (fun g => χ g) h1 (key 1).1 (fun g => (key g).2) (dvd_of_le_v (D.loc l)) ?_
  convert evLaw_integers (D.loc l) LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

end GlobalTheory.NL.Expansion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnityStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  first | exact @GlobalTheory.NL.Expansion.levLaws | exact GlobalTheory.NL.Expansion.levLaws | (intros; apply GlobalTheory.NL.Expansion.levLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionRuleStmt
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_ext_cocycle [IsTopologicalRing LL] {T Y Z : LocLat G Qp LL O}
    (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (hs : IsSESLat (Qp := Qp) ι π)
    (hZ : ∀ g z, Z.ρ g z = z) (x : ↥Y.L.T) :
    ∃ c : ↥(latticeCocycles T.L), ∀ g, ι.f ((c : G → T.V) g) = Y.ρ g (x : Y.V) - (x : Y.V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := hs
  obtain ⟨r, hr⟩ := ι.f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h1)
  have hr' : ∀ y, r (ι.f y) = y := fun y => LinearMap.congr_fun hr y
  have hval : ∀ g, ι.f (r (Y.ρ g (x : Y.V) - (x : Y.V))) = Y.ρ g (x : Y.V) - (x : Y.V) := by
    intro g
    obtain ⟨y, hy⟩ := (h4 (Y.ρ g (x : Y.V) - (x : Y.V))).1 (by rw [map_sub, π.equiv, hZ, sub_self])
    rw [← hy, hr']
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have : IsTopologicalAddGroup Y.V := IsModuleTopology.topologicalAddGroup LL Y.V
  refine ⟨⟨fun g => r (Y.ρ g (x : Y.V) - (x : Y.V)), ⟨?_, fun g h => ?_⟩, fun g _ => ?_⟩, hval⟩
  · exact hrc.comp ((Y.cont x).sub continuous_const)
  · apply h1
    rw [map_add (f := _), ι.equiv, hval, hval, hval, map_mul, Module.End.mul_apply, map_sub]
    abel
  · apply h5
    change ι.f (r _) ∈ _
    rw [hval]
    exact Y.L.T.sub_mem (Y.actT g x).2 x.2

variable {K₀ K : Type} [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_unit_fixed (E : EtTie W RA RW inclR φR gR πA) (u : ↥W.one.L.T) :
    ∃ e₀ ∈ tableLineDegreeTwo.fixDD W W.one, E.jD W.one e₀ = (1 : RW) ⊗ₜ[O] u := by
  obtain ⟨e₁, f₀, hf₀, hj, -⟩ := E.one_e
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : u ∈ Submodule.span O {f₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] u := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hφ : W.φD W.one (c • e₁) = c • e₁ := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγ : ∀ g, W.γD W.one g (c • e₁) = c • e₁ := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g u = u := Subtype.ext (W.one_triv g u)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  refine ⟨c • e₁, ⟨⟨?_, ?_⟩, ?_⟩, hje⟩
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 hφ)
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ _))
  · exact (Submodule.mem_iInf _).2 fun δ => (Submodule.mem_iInf _).2 fun _ =>
      LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ δ))

end Generic

theorem herrExt_of_dense (S : LocalSituation.Sit) (E : S.Comparison₂) [IsTopologicalRing S.LL] [T2Space S.LL]
    (hR : Function.Injective (algebraMap S.O S.RW))
    (hDel : S.PD.p = 2 → S.W.DelF = {1})
    (hdens : ∀ A : Subgroup S.G, IsClosed (A : Set S.G) → (∀ g, S.W.resΓ g ∈ S.W.DelF → g ∈ A) →
      (∀ g, S.W.resΓ g = S.W.gamK → g ∈ A) → ∀ g, g ∈ A) : tableLineDegreeTwo.HerrExt S.W E := by
  refine ⟨exists_unit_fixed E, fun T Tp ι π hs x u hu e hδ he p h1 h2 => ?_⟩
  obtain ⟨c, hc⟩ := exists_ext_cocycle ι π hs S.W.one_triv x
  exact ⟨c, (dict_of_dense S E hR hDel hdens T Tp _ ι π hs x u e hu he hδ p h1 h2 c hc).symm, hc⟩

theorem extension_rule (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    InvariantsGenerators.HerrExtensionEtale D HW F := by
  intro l _ K LL hA
  let S := LocalSituation.sit D.loc HW l (D.locA l) K 1 LL hA.2.2
  let E : S.Comparison₂ := ((F l).E K 1 LL hA.2.2).tie
  have : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  have : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact herrExt_of_dense S E (algebraMap_RW_injective LL)
    (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) fun h2 => absurd h2 hA.2.1)

end GlobalTheory.ExtDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivatives
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivatives
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.DegDer

variable {g : ℕ} [Fact g.Prime]

theorem tl_one {a n : ℕ} (h : a ≤ n) : tl a (1 : Mt g n) = (1 : Mt g a) := by
  ext i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]

theorem br_one {a b n : ℕ} (h : a + b ≤ n) : br a b (1 : Mt g n) = (1 : Mt g b) := by
  ext i j
  have hi : a + (i : ℕ) < n := by omega
  have hj : a + (j : ℕ) < n := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
  simp

theorem toG_one {n : ℕ} : toG (1 : Mt g n) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  ext : 1
  simp

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 = ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1)) := by
  unfold hc hcT
  rw [← GlobalTheory.GLm.ParBasic.card_par]
  congr 1
  simp only [mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true,
    tl_one (Nat.le_add_right a b), br_one (le_refl (a + b)), toG_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem blockDiagonalWithIdentityGL_one (k : ℕ) : diag1 (1 : Gn g k) (k + 1) = 1 := by
  unfold diag1
  have : (fun i j : Fin (k + 1) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN ((1 : Gn g k) : Mt g k) i j
      else (1 : Mt g (k + 1)) i j) = (1 : Mt g (k + 1)) := by
    ext i j
    split_ifs with h
    · simp only [Units.val_one, entN, h, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
    · rfl
  rw [this, toG_one]

theorem prod_pow_add (a b : ℕ) :
    (∏ i : Fin (a + b), (g : ℂ) ^ (i : ℕ)) =
      (∏ i : Fin a, (g : ℂ) ^ (i : ℕ)) * (∏ i : Fin b, (g : ℂ) ^ (i : ℕ)) * (g : ℂ) ^ (a * b) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  ring

theorem prod_Icc_add (f : ℕ → ℂ) (a b : ℕ) :
    (∏ i ∈ Finset.Icc 1 (a + b), f i) = (∏ i ∈ Finset.Icc 1 a, f i) * ∏ i ∈ Finset.Ico (a + 1) (a + b + 1), f i := by
  have e : ∀ n, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, e, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

theorem card_Gn_factors_ne_zero (n : ℕ) :
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) ≠ 0 ∧ (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [GlobalTheory.GLq.GGDeg.card_Gn] at h
  exact mul_ne_zero_iff.mp h

theorem one_eq_sum_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ),
    0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  intro g _ ψ hψ n χ hn hχ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have h1 : χ 1 = χ (diag1 (1 : Gn g k) (k + 1)) := by rw [blockDiagonalWithIdentityGL_one]
  rw [h1, GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k χ hM 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨b, rfl⟩ : ∃ b, k = i + b := ⟨k - i, by omega⟩
  have hkb : i + b - i = b := by omega
  rw [hkb, hc_one, (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ b).1]
  push_cast
  rw [GlobalTheory.GLq.GGDeg.card_Gn i, GlobalTheory.GLq.GGDeg.card_Gn b, GlobalTheory.GLq.GGDeg.card_Gn (i + b), prod_pow_add,
    prod_Icc_add]
  obtain ⟨hPi, hQi⟩ := card_Gn_factors_ne_zero (g := g) i
  obtain ⟨hPb, hQb⟩ := card_Gn_factors_ne_zero (g := g) b
  have hg : (g : ℂ) ^ (i * b) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  field_simp

end GlobalTheory.GLq.DegDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunction_degree_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ), 0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  first | exact @GlobalTheory.GLq.DegDer.one_eq_sum_der | exact GlobalTheory.GLq.DegDer.one_eq_sum_der | (intros; apply GlobalTheory.GLq.DegDer.one_eq_sum_der <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmall
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmall
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSmall

def ballIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ) : Ideal A :=
  Submodule.comap (Algebra.linearMap A (PreDisc l u ρ)) (ball l u ρ r)

theorem mem_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} {x : A} :
    x ∈ ballIdeal l u ρ r ↔ algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ r := Iff.rfl

theorem ballIdeal_mul_le {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r s : ℝ} (hr : 0 ≤ r) :
    ballIdeal l u ρ r * ballIdeal l u ρ s ≤ ballIdeal l u ρ (r * s) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal, map_mul]
    exact mul_mem_ball l u ρ hr hx hy

theorem pow_le_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    {I : Ideal A} (hI : I ≤ ballIdeal l u ρ r) : ∀ n : ℕ, I ^ n ≤ ballIdeal l u ρ (r ^ n)
  | 0 => by
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    refine (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one).ge
    rw [mem_ballIdeal, map_one]
    exact Submodule.subset_span ⟨0, 0, 0, by simp, by simp⟩
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono (pow_le_ballIdeal hr hI n) hI).trans (ballIdeal_mul_le (pow_nonneg hr n))

theorem exists_E_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · rw [h, if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hd
  have h2 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  refine ⟨(q : bk.S), ?_⟩
  show ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  nth_rewrite 1 [h2]
  simp [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C]
  left
  exact map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) l

end GlobalTheory.BSP.DiscSmall


open GlobalTheory.BSP.DiscSmall in
theorem GlobalTheory.BSP.norm_toDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s,
    ‖toDisc l (s X) ρ x‖ ≤ r := by
  intro l hl K bk A _ s ρ hρ0 hρ1 r hr
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  set t : ℝ := max (1 / (l : ℝ)) ((ρ : ℝ) ^ bk.Ep.natDegree) with ht
  have ht0 : 0 < t := lt_max_of_lt_left (one_div_pos.2 hl0)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have ht1 : t < 1 := max_lt ((div_lt_one hl0).2 hl1) (pow_lt_one₀ ρ.2 hρ1' bk.deg_pos.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr ht1
  have hlmem : algebraMap A (PreDisc l (s X) ρ) (l : A) ∈ ball l (s X) ρ t := by
    refine Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩
    have : 1 / (l : ℝ) * l ≤ t * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0.le
    rw [one_div_mul_cancel hl0.ne'] at this
    simpa using this
  have hJ : bk.J.map s ≤ ballIdeal l (s X) ρ t := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_le_iff,
      Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    constructor
    · show s (l : bk.S) ∈ ballIdeal l (s X) ρ t
      rw [map_natCast, mem_ballIdeal]
      exact hlmem
    · show s bk.E ∈ ballIdeal l (s X) ρ t
      obtain ⟨q, hq⟩ := exists_E_eq bk
      rw [hq, map_add (f := _), map_mul, map_pow, map_natCast, mem_ballIdeal, map_add (f := _), map_mul, mul_comm, ← Algebra.smul_def]
      refine add_mem (Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, by simp⟩) (Submodule.smul_mem _ _ hlmem)
      show (l:ℝ)^0 * (ρ:ℝ)^bk.Ep.natDegree ≤ t * (l:ℝ)^0
      simp only [pow_zero, one_mul, mul_one]
      exact le_max_right _ _
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have hx' := pow_le_ballIdeal ht0.le hJ n hx
  rw [toDisc, RingHom.comp_apply, norm_ofPre]
  exact (gauge_le l (s X) ρ (pow_pos ht0 n) hx').trans hn.le
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmallStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  first | exact @GlobalTheory.BSP.norm_toDisc_J_pow_small | exact GlobalTheory.BSP.norm_toDisc_J_pow_small | (intros; apply GlobalTheory.BSP.norm_toDisc_J_pow_small <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.LocUnitPow

variable {L : Type} [Field L] [NumberField L]

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {z : v.adicCompletion L} (hz : Valued.v z = 1) (i : ℕ) :
    Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ m ih =>
    have e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ih
    rw [map_mul, map_pow, hz, one_pow, one_mul]

theorem val_pow_sub_one_step {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) {j : ℤ} (hj : Valued.v (z - 1) ≤ WithZero.exp (-j)) (hj1 : 1 ≤ j) :
    Valued.v (z ^ N - 1) ≤ WithZero.exp (-(j + 1)) := by
  have e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) := by
    rw [← geom_sum_mul, Finset.sum_sub_distrib]
    simp [mul_comm]
  have hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
    refine Valuation.map_add_le _ ?_ hN
    refine Valuation.map_sum_le _ fun i _ => ?_
    exact (val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))
  rw [e, map_mul]
  calc _ ≤ WithZero.exp (-j) * WithZero.exp (-1 : ℤ) := mul_le_mul' hj hS
    _ = _ := by rw [← WithZero.exp_add]; congr 1; ring

theorem val_pow_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) (hz1 : Valued.v (z - 1) ≤ WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (z ^ (N ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using hz1
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have hzk : Valued.v (z ^ N ^ k) = 1 := by rw [map_pow, hz, one_pow]
    have := val_pow_sub_one_step hN hzk ih (by omega)
    convert this using 3
    push_cast
    ring

theorem loc_pow_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  intro L _ _ χ v x hx
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef
  have hN2 : 1 < N := Fintype.one_lt_card
  have hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ) := by
    have hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0 := by
      rw [map_natCast]; exact FiniteField.cast_card_eq_zero _
    rw [IsLocalRing.residue_eq_zero_iff] at hr
    have hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr
    have e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L) := by
      push_cast; rfl
    rw [e] at hlt
    exact le_exp_neg_one' hlt
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  have e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) =
      (x : v.adicCompletion L) ^ (N - 1) - 1 := by
    push_cast; rfl
  rw [e] at hlt
  have hx1 := le_exp_neg_one' hlt
  have hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1 := by
    rw [map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  have key := val_pow_pow_sub_one_le hNv hz hx1 n
  refine ⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩
  rw [← map_pow]
  refine hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
  rw [Units.val_pow_eq_pow_val, pow_mul]
  exact key.trans (WithZero.exp_le_exp.mpr (by omega))

end GlobalTheory.LocUnitPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnitsStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  first | exact @GlobalTheory.LocUnitPow.loc_pow_eq_one | exact GlobalTheory.LocUnitPow.loc_pow_eq_one | (intros; apply GlobalTheory.LocUnitPow.loc_pow_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxed
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet GlobalTheory.AntiRamConj
open scoped Pointwise

namespace GlobalTheory.ResUnr

theorem cocycle_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R G M) (x : Z1 rho)
    (h σ : G) (hσ : x.1 σ = 0) : x.1 (h * σ * h⁻¹) = rho (h * σ * h⁻¹) (-x.1 h) - (-x.1 h) := by
  have e1 := x.2.2 (h * σ * h⁻¹) h
  have e2 := x.2.2 h σ
  rw [inv_mul_cancel_right, e2, hσ, map_zero, add_zero] at e1
  rw [map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq, add_comm]
  exact e1.symm

theorem res_mem_unrAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (G F Ω) M) (x : Z1 rho)
    (A : ValuationSubring Ω) (m : M) (hm : ∀ σ ∈ Ine (F := F) A, x.1 σ = rho σ m - m) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt rho A := by
  unfold Formalism.GaloisCohomology.unrAt H1ur
  rw [LinearMap.mem_ker]
  unfold ReciprocityTheory.Gal.resH1
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_coboundaries1 _ _).2 ⟨m, fun g => hm g.1.1 (Subgroup.mem_subgroupOf.1 g.2)⟩

theorem mem_of_subsingleton {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : Subsingleton M) (S : Submodule R M) (y : M) :
    y ∈ S := by
  rw [Subsingleton.elim y 0]
  exact S.zero_mem

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

theorem mem_ine_iff_isFrob {B : ValuationSubring N.Om} {σ : GE N} : σ ∈ Ine (F := D.host.E) B ↔ IsFrob B 1 σ := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx => by rw [pow_one]; exact h.2 x hx⟩
  · intro h
    exact ⟨h.1, fun x hx => by have := h.2 x hx; rwa [pow_one] at this⟩

theorem ine_smul {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) (g : GE N) :
    g * σ * g⁻¹ ∈ Ine (F := D.host.E) (g • B) :=
  mem_ine_iff_isFrob.2 (isFrob_smul (mem_ine_iff_isFrob.1 hσ) g)

theorem exists_ine_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    ∃ k : GE N, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P'), ∃ σ₀ ∈ Ine (F := D.host.E) (N.plOm.1 P),
      σ = k * cConj X σ₀ * k⁻¹ := by
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  refine ⟨(cConj X g)⁻¹, fun σ hσ => ?_⟩
  have h3 := ine_smul (cConj_mem_ine X hσ) g
  rw [hg] at h3
  refine ⟨_, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

theorem res_mem_unrAt_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P')
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GE N) M) (x : Z1 rho)
    (hz : ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), x.1 (cConj X σ) = 0) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := D.host.E) (N.plOm.1 P')).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈
      Formalism.GaloisCohomology.unrAt rho (N.plOm.1 P') := by
  obtain ⟨k, hk⟩ := exists_ine_of_conj X h
  refine res_mem_unrAt rho x (N.plOm.1 P') (-x.1 k) fun σ hσ => ?_
  obtain ⟨σ₀, h3, rfl⟩ := hk σ hσ
  exact cocycle_conj rho x k _ (hz _ h3)


set_option maxHeartbeats 800000 in
theorem unrelax : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  intro D N X bkP i s hF K _ _ _ _ hK M R P d φ φ' Q hM hpos hQ x hx hz
  unfold selOn Formalism.GaloisCohomology.SelAll at hx ⊢
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  by_cases h1 : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  · rw [if_pos h1] at hv ⊢
    exact hv
  rw [if_neg h1] at hv ⊢
  by_cases h2 : v ∈ Spl i
  · rw [if_pos (Set.mem_union_left _ h2)]
    exact Submodule.mem_top
  rw [if_neg (by simpa using h2)]
  by_cases h3 : v ∈ Q
  swap
  · rw [if_neg (by simp [h2, h3])] at hv
    exact hv
  obtain ⟨q, hq⟩ := (hQ v).1 h3
  rcases q with a | a
  · haveI : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun y hy => by
      by_contra hn
      exact hy.ne_zero (hK y ((IsLocalRing.mem_maximalIdeal y).2 hn))⟩
    have hT : Tors K K := fun b => ⟨1, fun y hy => by
      rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hy
      rw [hy, zero_smul]⟩
    have hs := (hF M R P d φ φ' hM hpos K (1 : GE N →* Kˣ) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K hT (Tgl i s) (Or.inl rfl)
      a v hq).2.1
    exact mem_of_subsingleton hs _ _
  · rcases hq with rfl | hq
    · refine res_mem_unrAt (red i K (Tgl i s)) x (N.plOm.1 (P (.inr a))) 0 fun σ hσ => ?_
      rw [(hz a σ hσ).1, map_zero, sub_zero]
    · exact res_mem_unrAt_of_conj X hq (red i K (Tgl i s)) x fun σ hσ => (hz a σ hσ).2

end GlobalTheory.ResUnr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relaxedResidualSelmer_mem_unrelaxed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  first | exact @GlobalTheory.ResUnr.unrelax | exact GlobalTheory.ResUnr.unrelax | (intros; apply GlobalTheory.ResUnr.unrelax <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.GWComplex

section Count

variable {R : Type*} [CommRing R] {A B C D E : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]

theorem card_eq_ker_mul_range (f : A →ₗ[R] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

theorem card_five {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {k : D →ₗ[R] E}
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h)
    (h3 : Function.Exact h k) :
    Nat.card (LinearMap.ker k) * Nat.card B = Nat.card C * Nat.card A := by
  rw [card_eq_ker_mul_range g, card_eq_ker_mul_range h, h1.linearMap_ker_eq,
    h2.linearMap_ker_eq, h3.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]
  ring

theorem card_comap {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (L : Submodule R B) :
    Nat.card (L.comap f) =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker (g.domRestrict L)) := by
  let u : L.comap f →ₗ[R] L := f.restrict (fun _ hx => hx)
  rw [card_eq_ker_mul_range u]
  have e1 : LinearMap.range u = LinearMap.ker (g.domRestrict L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, h x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact x.2⟩, Subtype.ext hy⟩
  have e2 : Nat.card (LinearMap.ker u) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.1 x.2]; exact L.zero_mem⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2]

theorem card_pi {I : Type*} [Fintype I] {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (L : ∀ i, Submodule R (P i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i trivial⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Count

theorem arith {k p h2 h0 s i h1 s' q h0' m : ℕ} (a1 : k * p = h2 * h0) (a2 : s = k * i)
    (a3 : i * h1 = s' * q) (a4 : h0' * h2 * m = h1) : s * h0' * p * m = s' * h0 * q := by
  calc s * h0' * p * m = (k * p) * i * h0' * m := by rw [a2]; ring
    _ = i * (h0' * h2 * m) * h0 := by rw [a1]; ring
    _ = s' * h0 * q := by rw [a4, a3]; ring


open PoitouTate in
theorem ker_flip_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Av : S → ValuationSubring Ω}
    {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
    {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
    (hj : ∀ v, Function.Injective (j v))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}
    (hρ : ContAction ρ) (L : LocCond ρ (locFam S Av)) :
    LinearMap.ker ((tr1 S Av μ j ρ hρ).domRestrict (Submodule.pi Set.univ L)).flip =
      Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)
        (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) := by
  classical
  ext y
  rw [mem_Sel, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [mem_perpCond, LinearMap.flip_apply, LinearMap.domRestrict_apply, poitouTateNineTerm_transgressionOne_apply,
    LinearMap.zero_apply]
  constructor
  · intro h v x hx
    have hm : Pi.single v x ∈ Submodule.pi Set.univ L := fun w _ => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
    have e := h ⟨_, hm⟩
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [Subtype.coe_mk, Pi.single_eq_of_ne hw, map_zero, map_zero]) (by simp),
      Subtype.coe_mk, Pi.single_eq_same] at e
    exact hj v (e.trans (map_zero _).symm)
  · intro h x
    exact Finset.sum_eq_zero fun v _ => by rw [h v _ (x.2 v trivial), map_zero]


open PoitouTate in
theorem greenbergWiles_totallyComplex : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (S : Finset (HeightOneSpectrum (𝓞 F))) (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), 0 < r → ContainsAbove S l → ∀ (hrho : ContAction rhoS) (muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ), muS.comp (toGS Ω _) = cycMod F Ω l r → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond rhoS (locFam S Av), Finite (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) ∧ Finite (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) ∧ Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) * Nat.card (H0 (twDual muS rhoS)) * (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) * Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hS hρ μ hμ Av hA L
  classical
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨inv, hinv, h⟩ := hPT F Ω l r hr ζ hζ
  obtain ⟨⟨δ₁, -, h0, h1, h2, h3, h4, -⟩, -⟩ := h S hS Av hA μ hμ M ρ hρ
  have := GlobalTheory.DualSide.finite_TDual_pow (l := l) (r := r) (M := M)
  have hρ' := GlobalTheory.DualSide.contAction_twDual (contAction_charRep hμ) hρ
  obtain ⟨-, f1, -⟩ := hGF F Ω l r M S ρ hr hS hρ
  obtain ⟨-, f1', f2', -⟩ := hGF F Ω l r _ S (twDual μ ρ) hr hS hρ'
  have fl : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v =>
    (hLF F Ω l r M (Av v) _ v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have a1 := card_five h0 h1 h2 h3
  rw [GlobalTheory.ZModDual.card_dual_eq, Nat.card_pi] at a1
  have a2 := card_comap h4 (Submodule.pi Set.univ L)
  have e2 : (Submodule.pi Set.univ L).comap (loc1 S Av ρ) =
      Sel ρ (locFam S Av) (continuous_locFam S Av) L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [e2] at a2
  have a3 := GlobalTheory.ZModDual.card_ker_mul_card_eq (l ^ r) _ _
    ((tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ).domRestrict (Submodule.pi Set.univ L))
  rw [ker_flip_eq (fun v => (invAt_bijective S Av μ hμ hinv v (hA v)).1), card_pi] at a3
  have a4 := hEC F Ω l r _ S (twDual μ ρ) hr hS hρ' (fun _ => 1)
    (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)))
  have hM : Nat.card (TDual (ZMod (l ^ r)) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq _ _
  rw [archH0Card, Finset.filter_false_of_mem (fun w _ =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)), Finset.prod_empty,
    one_mul, hM, IsTotallyComplex.finrank, two_mul, pow_add, ← mul_assoc] at a4
  have a5 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) a4
  exact arith a1 a2 a3 a5

end GlobalTheory.GWComplex
end
