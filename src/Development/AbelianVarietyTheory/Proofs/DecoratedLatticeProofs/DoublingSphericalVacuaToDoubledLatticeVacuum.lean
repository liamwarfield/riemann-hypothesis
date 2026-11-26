module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.VacBox

variable {D : D7}

theorem gram_dbl_inv (A : HSp D) : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) :=
  Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram A).2.isUnit, blkMat_one])

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (resR A B x) (resR A B y) := by
  simp only [hO]
  rw [gram_dbl_inv]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hO_neg_neg (A B : HSp D) (x y : WO A B) : hO A B (-x) (-y) = hO A B x y := by
  simp only [hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y = symplOH A B (resL A B x) (resL A B y) - symplOH A B (resR A B x) (resR A B y) := by
  simp only [symplOH, symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_neg_neg (A B : HSp D) (x y : WO A B) : symplOH A B (-x) (-y) = symplOH A B x y := by
  simp only [symplOH, symplO, hO_neg_neg]

theorem resL_add (A B : HSp D) (x y : WO (dblSp A) B) : resL A B (x + y) = resL A B x + resL A B y :=
  Matrix.ext fun _ _ => rfl

theorem resR_add (A B : HSp D) (x y : WO (dblSp A) B) : resR A B (x + y) = resR A B x + resR A B y :=
  Matrix.ext fun _ _ => rfl

def resLHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resL_add A B

def resRHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resR A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resR_add A B

theorem conj_psi_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (z : AF D.host.F) :
    conj (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ, one_pow, inv_one, Complex.ofReal_one,
    mul_one]

theorem heisO_delta {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (A B : HSp D) (w₀ : WO (dblSp A) B)
    (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B w₀ (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B w₀) f₁) (heisO ψ A B (-resR A B w₀) f₂) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, resL_add, resR_add, map_mul, conj_psi_eq hψ, symplOH_dbl, symplOH_neg_neg, neg_add]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem sum_dbl_gram_inl (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inl j)) =
      ∑ k, star ((fun k => s (finSumFinEquiv (Sum.inl k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem sum_dbl_gram_inr (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inr j)) =
      ∑ k, star ((-fun k => s (finSumFinEquiv (Sum.inr k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.neg_apply, Pi.neg_apply, star_neg, mul_neg, neg_mul]

theorem res_mem_latO {A B : HSp D} {LA : Lat A} {LB : Lat B} {P : FinPl D → Prop} {u : WO (dblSp A) B}
    (hu : u ∈ latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P) :
    resL A B u ∈ latO A B LA LB P ∧ resR A B u ∈ latO A B LA LB P := by
  have key : latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P ≤
      (latO A B LA LB P).comap (resLHom A B) ⊓ (latO A B LA LB P).comap (resRHom A B) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, fun k => s (finSumFinEquiv (Sum.inl k)), hs.1, t, ht, ?_⟩,
      AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, -fun k => s (finSumFinEquiv (Sum.inr k)), neg_mem hs.2, t, ht, ?_⟩⟩
    · ext i j
      simp only [resLHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resL, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inl A s j)
    · ext i j
      simp only [resRHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resR, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inr A s j)
  exact key hu

theorem latO_mono_at {A B : HSp D} (LA : Lat A) (LB : Lat B) {Sf : Finset (FinPl D)} {v : FinPl D} (hv : v ∉ Sf) :
    latO A B LA LB (fun u => u = v) ≤ latO A B LA LB (fun u => u ∉ Sf) := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hP, rest⟩
  refine ⟨α, hα, fun v' hv' => hP v' fun h => hv' (h ▸ hv), rest⟩

theorem pair_dbl (A : HSp D) (x y : Fin (dblSp A).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (dblSp A).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * A.gram i j * y (finSumFinEquiv (Sum.inl j))) -
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * A.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem selfDual_sumLat {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) :
    IsSelfDualC (dblSp A) (sumLat finSumFinEquiv L L) := by
  have hsum : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L) := by
    let φ : ((Fin A.rank → D.host.E) × (Fin A.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (A.rank + A.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L = (L.prod L).map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL.1.fg).map _)
  refine ⟨hsum, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ - b₂, ?_⟩
    rw [pair_dbl]
    push_cast
    linear_combination hb₁ - hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hb
      refine ⟨b, ?_⟩
      show (b : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inl j))
      exact hb
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hb
      refine ⟨-b, ?_⟩
      show ((-b : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inr j))
      push_cast
      linear_combination -hb

theorem doubling_isLatVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  intro D ψ A B LA LB hψ hLA
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨selfDual_sumLat hLA, ?_⟩
  intro Sf Φ₁ Φ₂ h₁ h₂ v hv
  have mono := latO_mono_at LA LB hv
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have eL : resL A B (2 • u) = 2 • resL A B u := by rw [two_nsmul, two_nsmul, resL_add]
    have eR : -resR A B (2 • u) = 2 • (-resR A B u) := by
      rw [two_nsmul, two_nsmul, resR_add, neg_add]
    rw [heisO_delta hn, eL, eR, h₁.1 _ (mono hL), h₂.1 _ (neg_mem (mono hR))]
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have hhL : IsHalf e (resL A B u) := fun i j => hh i (finSumFinEquiv (Sum.inl j))
    have hhR : IsHalf e (-resR A B u) := fun i j => by
      show e * -(u i (finSumFinEquiv (Sum.inr j))) = -(u i (finSumFinEquiv (Sum.inr j)))
      rw [mul_neg, hh]
    rw [heisO_delta hn, h₁.2 e he _ (mono hL) hhL, h₂.2 e he _ (neg_mem (mono hR)) hhR]

end GlobalTheory.Core.Rk.VacBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuumStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_sphericalVacua_to_doubled_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  first | exact @GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | exact GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | (intros; apply GlobalTheory.Core.Rk.VacBox.doubling_isLatVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat IsInertChart IsFrameAt)

noncomputable section

namespace GlobalTheory.DblInert

open Formalism.UG GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E} {h : w.under (𝓞 F) = v}
  {c : w.adicCompletion E →+* w.adicCompletion E} {m : ℕ}

theorem bc_mem_iff_gram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) (g : GL (Fin m) (Fv F v ⊗[F] E)) :
    g ∈ HR (Fv F v) σ J ↔ a⁻¹ * bc (toCompl h) g * a ∈ UJ c T := by
  have h1 : cT c (bc (toCompl h) g).1 = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (toCompl h) :=
    Matrix.ext fun i j => hc _
  have h2 : g ∈ HR (Fv F v) σ J ↔ bc (toCompl h) g ∈ UJ c (J.map (algebraMap E _)) := by
    change _ ↔ cT c (bc (toCompl h) g).1 * _ * g.1.map (toCompl h) = _
    rw [h1, ← JR_map h, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (toCompl_bijective hw h).1).eq_iff.symm
  have h3 : ∀ x : GL (Fin m) (w.adicCompletion E), cT c (a⁻¹ * x * a).1 * T * (a⁻¹ * x * a).1 =
      cT c a.1 * (cT c x.1 * J.map (algebraMap E _) * x.1) * a.1 := fun x => by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc,
      mul_inv_cancel_left, Units.val_mul, cT_mul]
    simp only [Matrix.mul_assoc]
  have h4 : IsUnit (cT c a.1) := IsUnit.of_mul_eq_one (cT c (a⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
  rw [h2]
  change _ ↔ _ * _ * _ = _
  rw [h3, ← ha, a.isUnit.mul_left_inj, h4.mul_right_inj]
  rfl

def chartGram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) : GLoc σ J v ≃* UJ c T :=
  have e1 : ∀ x : GL (Fin m) (w.adicCompletion E), bc (toCompl h) (bc (complEquiv hw h).symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).apply_symm_apply _)
  have e2 : ∀ x : GL (Fin m) (Fv F v ⊗[F] E), bc (complEquiv hw h).symm.toRingHom (bc (toCompl h) x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).symm_apply_apply _)
  { toFun := fun g => ⟨a⁻¹ * locMat σ J h g * a, (bc_mem_iff_gram hw hc ha _).1 g.2⟩
    invFun := fun u => ⟨bc (complEquiv hw h).symm.toRingHom (a * u * a⁻¹), (bc_mem_iff_gram hw hc ha _).2 (by
      rw [e1, show a⁻¹ * (a * u * a⁻¹) * a = u by group]; exact u.2)⟩
    left_inv := fun g => Subtype.ext ((congrArg (bc (complEquiv hw h).symm.toRingHom)
      (show a * (a⁻¹ * locMat σ J h g * a) * a⁻¹ = locMat σ J h g by group)).trans (e2 g.1))
    right_inv := fun u => Subtype.ext ((congrArg (a⁻¹ * · * a) (e1 _)).trans (by group))
    map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }

section Conj

variable {A B n ι : Type} [CommRing A] [CommRing B] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

theorem blkGL_mem_diag (a : GL n A) : blkGL e (a, a) ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)

theorem conj_mem_diag (a : GL n A) (x : GL ι A) :
    (blkGL e (a, a))⁻¹ * x * blkGL e (a, a) ∈ stabGL (diagSub A e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem bc_mem_diag {f : A →+* B} (hf : Function.Injective f) (x : GL ι A) :
    bc f x ∈ stabGL (diagSub B e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [mem_stabGL_diagSub, mem_stabGL_diagSub]
  refine ⟨fun hx => (keepsDiag_iff e).2 fun i j => hf ?_, fun hx => hx.map e f⟩
  rw [map_add (f := _), map_add (f := _)]
  exact (keepsDiag_iff e).1 hx i j

theorem det_leviMat_conj (a : GL n A) {x : GL ι A} (hx : x ∈ stabGL (diagSub A e)) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let D : stabGL (diagSub A e) →* Aˣ := Matrix.GeneralLinearGroup.det.comp (leviGL e)
  let b : stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  have h1 : D (b⁻¹ * ⟨x, hx⟩ * b) = D ⟨x, hx⟩ := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  exact congrArg Units.val h1

end Conj

theorem exists_dblChart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  intro F E _ _ _ _ _ σ _ n J _ Q hQ L _ v w h hw c e he
  obtain ⟨hc, ⟨a, ha', ha, hea⟩, -⟩ := he
  have hA' : IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) :=
    GlobalTheory.LFun.isFrameAt_sumLat_blkGL E w n L a ha'
  have hT : cT c (blkGL finSumFinEquiv (a, a)).1 * Q.map (algebraMap E _) * (blkGL finSumFinEquiv (a, a)).1 =
      dblGram finSumFinEquiv (antiJ (w.adicCompletion E) n) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, ha,
      Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, ha]
    rfl
  have hinj := (toCompl_bijective hw h).1
  refine ⟨chartGram hw hc hT, fun g => ?_, fun y => Subtype.ext ?_, fun g => ?_, fun p hp => Units.ext ?_⟩
  · refine Iff.trans ?_ (((isFrameAt_mul hA' (one_mem _)).2 (locMat σ Q h g)).trans
      ⟨fun hg => ⟨(chartGram hw hc hT g).2, hg⟩, fun hg => hg.2⟩)
    rw [mem_stabLoc]
    refine ⟨fun hg z => ?_, fun hg y => ?_⟩
    · obtain ⟨y, rfl⟩ := exists_comp h z
      rw [← mem_latLoc_iff hw, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
    · rw [mem_latLoc_iff hw h, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
  · change (blkGL finSumFinEquiv (a, a))⁻¹ * bc (toCompl h) (blkGL finSumFinEquiv
      (GlobalTheory.AdelicU.matHom _ σ J y, GlobalTheory.AdelicU.matHom _ σ J 1)) * blkGL finSumFinEquiv (a, a) =
        blkGL finSumFinEquiv ((e y : GL (Fin n) (w.adicCompletion E)), 1)
    rw [bc_blkGL, ← map_inv, ← map_mul, ← map_mul, hea, map_one, map_one, Prod.inv_mk, Prod.mk_mul_mk,
      Prod.mk_mul_mk, mul_one, inv_mul_cancel]
    rfl
  · exact ((conj_mem_diag finSumFinEquiv a _).trans (bc_mem_diag finSumFinEquiv hinj _)).symm
  · refine (det_leviMat_conj finSumFinEquiv a ((bc_mem_diag finSumFinEquiv hinj _).2 p.2)).trans ?_
    exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (toCompl h) _)).trans (RingHom.map_det _ _).symm

end GlobalTheory.DblInert

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubling_chart_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  first | exact @GlobalTheory.DblInert.exists_dblChart | exact GlobalTheory.DblInert.exists_dblChart | (intros; apply GlobalTheory.DblInert.exists_dblChart <;> assumption)
end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

namespace GlobalTheory.KerInert

open scoped TensorProduct

theorem npow_zpow {q : ℕ} (hq : q ≠ 0) (r : ℝ≥0) (m : ℤ) (hr : (r : ℝ) = (q : ℝ) ^ (-(2 * m))) (t : ℂ) :
    GlobalTheory.Doubling.npow r t = (q : ℂ) ^ (-(2 * (m : ℂ) * t)) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by rw [hr]; exact_mod_cast (zpow_pos h0 _).ne'
  rw [GlobalTheory.Doubling.npow, Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hq),
    ← Complex.ofReal_log r.coe_nonneg, hr, Real.log_zpow, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem exists_isSphSec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (μ : (AF F ⊗[F] E)ˣ →* Circle)
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (hq : qV F v ≠ 0) {s : ℂ} {φ : GLoc σ Q v → ℂ} (h1 : φ ∈ degPSFin σ Q L v (charAt μ v) s)
    (h2 : ∀ k ∈ KFin σ Q L v, ∀ g, φ (g * k) = φ g) (h3 : φ 1 = 1)
    {c : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) :
    ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV F v) n (locChar μ w) s Φ ∧
      ∀ y, φ (ioH _ σ hQ (y, 1)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) := by
  obtain ⟨f, hK, hio, hP, ha⟩ := GlobalTheory.T.exists_doubling_chart_inert_place F E σ hc n J hJ Q hQ L v w h hw c e he
  refine ⟨fun g => φ (f.symm g), fun p k hk => ?_, fun y => ?_⟩
  · have hp : f.symm p ∈ siegelH (Fv F v) σ Q := (hP _).2 (by rw [f.apply_symm_apply]; exact p.2)
    have hk' : f.symm k ∈ KFin σ Q L v := (hK _).2 (by rwa [f.apply_symm_apply])
    have e1 := (mem_degPSH.1 h1).1 ⟨_, hp⟩ 1
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (GlobalTheory.LFun.toCompl h).toMonoidHom (aH _ σ Q ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (f.apply_symm_apply _).symm)).trans (ha ⟨_, hp⟩ ((hP _).1 hp))
    rw [mul_one, h3, mul_one, GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert F E μ v w h hw, npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hc v w h hw _)] at e1
    show φ (f.symm (p * k)) = _
    rw [map_mul, h2 _ hk', e3]
    exact e1
  · show _ = φ (f.symm _)
    rw [← hio y, f.symm_apply_apply]

theorem sphSec_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ (v : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χ w → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : (w.adicCompletion D.host.E)ˣ) (e : Gv A v ≃* GU c A.rank), IsUnramInv (ϖ : w.adicCompletion D.host.E) c (qV D.host.F v) → IsInertChart D.sp.cm.sig A.gram L h c e → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr (locChar χ⁻¹ w) ∧ locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ ∧ ((locChar χ⁻¹ w ϖ : ℂˣ) : ℂ) = (-1) ^ b ∧ ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV D.host.F v) A.rank (locChar χ⁻¹ w) s Φ ∧ ∀ y, φ (ioAt A v y) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c A.rank (e y)) := by
  intro D A L hL χ b hχ v w h hw hu s φ hφ c ϖ e hU he
  have h2 : locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ :=
    (hu.inv.locChar_eq_val hU.2.2.2.1).trans (GlobalTheory.LFun.val_inv χ w)
  have hq : qV D.host.F v ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  refine ⟨hu.inv, h2, ?_, exists_isSphSec (isCMExt_host D) (isHermND_gram A) (gram_hdbl A) L hL.1 χ⁻¹ h hw hq
    hφ.1 hφ.2.1 hφ.2.2 he⟩
  rw [h2, ((GlobalTheory.LFun.resEta_iff χ b).1 hχ).val_of_isInertAt (isCMExt_host D).2.2.1 hw hu, ← inv_pow, inv_neg_one]
  simp

end GlobalTheory.KerInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPoint
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Eis

theorem modGrowth_eis_sph : GlobalTheory.Published.SiegelEisensteinContinuation → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  intro hP D V h0 a ha hI σ hσ
  have hμ : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hb : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  have hφ := sph_mem hI (σ : ℂ)
  obtain ⟨k, hk⟩ := (hP D V h0 a ha hI 1 0 hμ hb σ _ hφ).2 σ
  have hv := (sphConv D V a hI).eisValueAt_flat hI hφ hμ (by simpa using hσ)
  obtain ⟨r, hr, -, -, C, N, h⟩ := hk.of_eisValueAt hv
  exact ⟨C, N, fun g => hv.eisCont_eq ▸ h σ (Metric.mem_ball_self hr) g⟩

end GlobalTheory.Eis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPointStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point : GlobalTheory.Published.SiegelEisensteinContinuation → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  first | exact @GlobalTheory.Eis.modGrowth_eis_sph | exact GlobalTheory.Eis.modGrowth_eis_sph | (intros; apply GlobalTheory.Eis.modGrowth_eis_sph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero : ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  first | exact @GlobalTheory.ChainOnto.val_eq_zero_imp | exact GlobalTheory.ChainOnto.val_eq_zero_imp | (intros; apply GlobalTheory.ChainOnto.val_eq_zero_imp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro hgap c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe hgap c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan hgap c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj hgap c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar hgap c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hF
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hPF

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.ChainOnto.stepUp | exact GlobalTheory.ChainOnto.stepUp | (intros; apply GlobalTheory.ChainOnto.stepUp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelOpen

theorem exists_open_princ : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V β Z
  have hOpen : IsOpen (((Kg D.sp.cm V.gram β Z).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    set N : ℕ := ∏ PP ∈ Z, Ideal.absNorm PP.asIdeal with hN
    have hN0 : 0 < N := Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
    have hNm : ∀ PP ∈ Z, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hP => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
      rw [hN, hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    let P : GA D V → Prop := fun k => ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (β⁻¹ * Lev.finE V k * β).1 i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j = N • s
    have hP : ∀ᶠ k in nhds (1 : GA D V), P k := by
      have hc := (GlobalTheory.Member.continuous_finHom_val D V).tendsto 1
      rw [map_one, Units.val_one] at hc
      exact hc.eventually (GlobalTheory.DefiniteEnd.eventually_cong β N hN0)
    have hP' : ∀ᶠ k in nhds (1 : GA D V), P k⁻¹ := by
      have : Filter.Tendsto (fun k : GA D V => k⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv (G := GA D V)).tendsto 1
      exact this.eventually hP
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hP.and hP') ?_)
    rintro k ⟨h1, h2⟩
    obtain ⟨y, hy, hred⟩ := GlobalTheory.DefiniteEnd.exists_int_of_entries _ (β⁻¹ * Lev.finE V k * β) N h1 (by
      rw [show (β⁻¹ * Lev.finE V k * β)⁻¹ = β⁻¹ * Lev.finE V k⁻¹ * β by rw [map_inv]; group]; exact h2)
    have hy' : frGL β y = Lev.finE V k := by
      show β * Formalism.UG.bc _ y * β⁻¹ = _
      rw [hy]; group
    have hSt : Lev.finE V k ∈ St β := ⟨y, hy'⟩
    refine ⟨⟨GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k), hSt⟩, ?_⟩
    refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hSt, ?_⟩
    rw [← hy', redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hNm PP hP)
  
  refine ⟨_, hOpen, fun k hk => ?_⟩
  have hk' : Lev.finE V k ∈ Kg D.sp.cm V.gram β Z := hk
  have h1 : Lev.finE V k ∈ ⨅ PP ∈ Z, princAt β PP := hk'.2
  refine ⟨hk'.1.2, fun PP hP => ?_⟩
  exact (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

end GlobalTheory.ChainOnto.LevelOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | exact GlobalTheory.ChainOnto.LevelOpen.exists_open_princ | (intros; apply GlobalTheory.ChainOnto.LevelOpen.exists_open_princ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Level

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt' {D : D7} (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_mul_mt {D : D7} (S T : HSp D) (k : GA D S) (u : WO S T) :
    actO S T k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) = u := by
  unfold actO
  rw [mt_one', Matrix.one_mul, Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]

theorem exists_common_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  intro D ψ S T χS χT om hW K hK f hf
  obtain ⟨U₀, hU₀, hUf⟩ := hf.level
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ k ∈ K,
        (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀}
      add_mem' := fun {a b} ha hb k hk => by
        have := U₀.add_mem (ha k hk) (hb k hk)
        rwa [← Matrix.add_mul] at this
      zero_mem' := fun k _ => by
        rw [Matrix.zero_mul]; exact U₀.zero_mem
      neg_mem' := fun {a} ha k hk => by
        have := U₀.neg_mem (ha k hk)
        rwa [← Matrix.neg_mul] at this }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 0) ?_, fun k hk u hu h0 => ?_⟩
  · refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T)) (P := fun u k =>
      (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀) fun k _ => ?_
    have hc : Continuous fun p : WO S T × GA D S =>
        (HMul.hMul (p.1 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S p.2) : WO S T) :=
      continuous_fst.matrix_mul ((continuous_mt' S).comp continuous_snd)
    refine (hU₀.preimage hc).mem_nhds ?_
    show (HMul.hMul (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k) : WO S T) ∈ U₀
    rw [Matrix.zero_mul]; exact U₀.zero_mem
  · have h1 := hUf _ (hu k hk) (by rw [Matrix.map_mul, h0]; simp)
    have h2 := hW.om_heis k 1 (HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S k)) f hf
    rw [h1, actO_mul_mt] at h2
    exact h2.symm

end GlobalTheory.Core.Rk.Level
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunctionStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_level_compact_translates_thetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ K : Set (GA D S), IsCompact K → ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ k ∈ K, ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (k, 1) f) = om (k, 1) f := by
  first | exact @GlobalTheory.Core.Rk.Level.exists_common_level | exact GlobalTheory.Core.Rk.Level.exists_common_level | (intros; apply GlobalTheory.Core.Rk.Level.exists_common_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dite_eq_left hy', dite_eq_left hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dite_eq_right hy', dite_eq_right hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPlacesDatum_mul_right_source_level : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  first | exact @GlobalTheory.ChainOnto.RightMove.omegaG_mul_right | exact GlobalTheory.ChainOnto.RightMove.omegaG_mul_right | (intros; apply GlobalTheory.ChainOnto.RightMove.omegaG_mul_right <;> assumption)
end
end
