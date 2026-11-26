module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem charpoly_dualMap (f : End ℂ V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f.dualMap (finBasis ℂ V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem exists_proj (a : WDRep h V) : ∃ e : End ℂ V, (∀ v, e v ∈ a.tameSpace) ∧
    (∀ v ∈ a.tameSpace, e v = v) ∧
    (∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → e * a.ρ σ = e) ∧
    ∀ f ∈ a.dual.tameSpace, ∀ v, f (e v) = f v := by
  classical
  let K : Subgroup (Weil h) := (Wild E A).subgroupOf (Weil h)
  let P : Subgroup (End ℂ V)ˣ := K.map a.ρ.toHomUnits
  have hfin : Finite P := by
    refine Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_)
      Units.val_injective.injOn
    rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨⟨σ, Wild_le_Ine hσ⟩, rfl⟩
  have := Fintype.ofFinite P
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card P : ℂ)⁻¹ • ∑ p : P, (p.1 : End ℂ V), fun v => ?_, fun v hv => ?_,
    fun σ hσ => ?_, fun f hf v => ?_⟩
  · refine a.mem_tameSpace.mpr fun σ hσ => ?_
    rw [← End.mul_apply, mul_smul_comm, Finset.mul_sum]
    congr 2
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, (p.1 : End ℂ V) v = v := by
      rintro ⟨_, σ, hσ, rfl⟩
      exact a.mem_tameSpace.mp hv σ hσ
    simp [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · rw [smul_mul_assoc, Finset.sum_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, f ((p.1 : End ℂ V) v) = f v := by
      rintro ⟨_, σ, hσ, rfl⟩
      have := LinearMap.congr_fun (a.dual.mem_tameSpace.mp hf σ⁻¹ (K.inv_mem hσ)) v
      simpa using this
    simp [this, hc]

theorem charpoly_dual_tamePart (a : WDRep h V) (σ : Weil h) :
    (a.dual.tamePart.ρ σ).charpoly = (a.tamePart.ρ σ⁻¹).charpoly := by
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_proj a
  let r : a.dual.tameSpace →ₗ[ℂ] Dual ℂ a.tameSpace :=
    a.tameSpace.dualRestrict ∘ₗ a.dual.tameSpace.subtype
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).mpr fun f hf => ?_, fun φ => ?_⟩
    · ext v
      rw [← h4 f.1 f.2 v]
      exact LinearMap.congr_fun hf ⟨e v, h1 v⟩
    · refine ⟨⟨φ ∘ₗ e.codRestrict _ h1, a.dual.mem_tameSpace.mpr fun u hu => ?_⟩, ?_⟩
      · ext v
        exact congrArg φ (Subtype.ext
          (LinearMap.congr_fun (h3 u⁻¹ ((Wild E A).inv_mem hu)) v))
      · ext v
        exact congrArg φ (Subtype.ext (h2 v v.2))
  rw [← charpoly_dualMap (a.tamePart.ρ σ⁻¹),
    ← LinearEquiv.charpoly_conj (LinearEquiv.ofBijective r hr)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective r hr).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem tameEig_lpDual (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    WD.tameEig (WD.lpDual x) γ = (WD.tameEig x γ).map (·⁻¹) := by
  obtain ⟨k, hk, -, hk1⟩ := WD.exists_pow_tameEig x hγ
  induction x using WD.ind with
  | hP m a =>
    have hγ' := Ine_le_Weil h hγ
    obtain ⟨n, h0, -, hn⟩ := a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, hγ'⟩) hγ
    have hp : n * k - 1 + 1 = n * k := Nat.sub_add_cancel (Nat.mul_pos h0 hk)
    have h1 : a.tamePart.ρ (⟨γ, hγ'⟩ : Weil h)⁻¹ = a.tamePart.ρ ⟨γ, hγ'⟩ ^ (n * k - 1) := by
      rw [← one_mul (a.tamePart.ρ _), ← one_pow k, ← hn, ← pow_mul, ← hp, pow_succ, mul_assoc,
        ← map_mul, mul_inv_cancel, map_one, mul_one, hp]
    have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (n * k - 1)
      (LinearMap.toMatrix (finBasis ℂ _) (finBasis ℂ _) (a.tamePart.ρ ⟨γ, hγ'⟩))
    rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
    rw [WD.tameEig_mk _ hγ'] at hk1
    rw [WD.lpDual_mk, WD.tameEig_mk _ hγ', WD.tameEig_mk _ hγ', charpoly_dual_tamePart, h1, h2]
    refine Multiset.map_congr rfl fun z hz => eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hp, pow_mul', hk1 z hz, one_pow]

theorem rootsBar_lab_lpDual : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (τ : Fbar g →* ℂ) (γ : G E Ω), ∀ x : WD h,
    rootsBar (WD.lab τ γ (WD.lpDual x)) = (rootsBar (WD.lab τ γ x)).map (·⁻¹) := by
  intro E Ω _ _ _ _ _ A w h g _ τ γ x
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · refine Multiset.map_injective H.2.2.injective ?_
    rw [WD.map_rootsBar_lab H, tameEig_lpDual x H.2.1, ← WD.map_rootsBar_lab H, Multiset.map_map,
      Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    show (τ y)⁻¹ = τ y⁻¹
    rcases eq_or_ne y 0 with rfl | hy
    · rw [inv_zero, H.2.2.map_zero, inv_zero]
    · exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hy, map_one])
  · simp [WD.lab_of_not H, rootsBar]

end GlobalTheory.WeilDeligne.LabDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeFnFinsetSumSmul
open MeasureTheory
namespace GlobalTheory.FinsetSumSmulCoe

theorem coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • u a) (∑ i ∈ s, c i • u i), Lp.coeFn_smul (c a) (u a), ih]
      with x h1 h2 h3
    rw [Finset.sum_insert ha]
    change (((c a • u a + ∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ)) : α → ℂ) x = _
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by
  intro α _ μ ι _ c u
  exact coeFn_finset_sum_smul c u Finset.univ

end GlobalTheory.FinsetSumSmulCoe
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem coeFn_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type} [Fintype ι] (c : ι → ℂ)
    (u : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • u i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i, c i * (u i : α → ℂ) x := by
  first
  | exact @_root_.GlobalTheory.FinsetSumSmulCoe.main
  | exact _root_.GlobalTheory.FinsetSumSmulCoe.main
  | (apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetSumSmulCoe.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetSumSmulCoe.main ..)

theorem sum_smul_apply {ι α : Type} [Fintype ι] (L : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (c : ι → ℂ) (φ : α → ℂ) (y : α) :
    (∑ i, c i • L i) φ y = ∑ i, c i * L i φ y := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp

theorem iotaX_symm_rat {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : X.B.I.GA)
    (hz : z ∈ X.B.I.GFset) : (iotaX X h).symm z ∈ GQ (D.sp.Y 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (z : I.GA), z ∈ I.GFset →
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm z ∈ GQ (D.sp.Y 0) := by
    intro I hI z hz
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm z =
        (Formalism.IndefR.RationalEmbedding.iota D).symm z := rfl
    rw [e, Formalism.IndefR.RationalEmbedding.iota_rat, ContinuousMulEquiv.apply_symm_apply]
    exact hz
  exact aux X.B.I h z hz

theorem ev_translate {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F)
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (x : X.B.I.GA) :
    ev (MP R) v₀ S ((iotaX X h).symm (x * (1, k)) * t) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
  have hk' := hB.2 k hk S hS v₀ ((iotaX X h).symm x * t)
  refine Eq.trans ?_ hk'
  have e : (iotaX X h).symm (x * (1, k)) * t = (iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k) := by
    unfold kap
    rw [map_mul]
    group
  show S v₀ _ = S v₀ _
  rw [e]
  rfl

theorem evalAct_intertwines : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) [Fintype (G0g D.nd)] (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd), LevelMatchB R F X h t σ red → ∀ S ∈ MultR R F, ∀ f : L2X X, (f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g) → ∀ (a : G0g D.nd → ℂ) (s : G0g D.nd → X.B.I.Gf), (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) =ᵐ[muX X] fun x => gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (a (σ.symm g))) (S v₀) ((iotaX X h).symm x * t) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F _ X h t v₀ σ red hB S hS f hf hinv a s hs
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      ev (MP R) v₀ S ((iotaX X h).symm (γ * y) * t) = ev (MP R) v₀ S ((iotaX X h).symm y * t) := by
    intro γ hγ y
    show S v₀ _ = S v₀ _
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have key : ∀ k ∈ X.B.I.Kset, ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
    intro k hk
    have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
      Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
    have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
      have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
      rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
    obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
    have e1 := X.B.R_spec (1, k) f
    have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
        ev (MP R) v₀ S ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
      refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = ev (MP R) v₀ S ((iotaX X h).symm y * t)) h1 ?_
      rw [h2]
      exact hf
    filter_upwards [e1, e3] with x a1 a3
    rw [a1]
    show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
    rw [a3]
    obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
    rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
      hφinv γ hγ]
    exact ev_translate R F X h t v₀ σ red hB S hS k hk x
  have hall : ∀ᵐ x ∂(muX X), ∀ γ, ((X.B.R (1, s γ) f : L2X X) : X.B.I.GA → ℂ) x =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red (s γ)))) (S v₀) ((iotaX X h).symm x * t) :=
    ae_all_iff.2 fun γ => key (s γ) (hs γ).1
  have hsum := coeFn_sum_smul (μ := muX X) (fun γ => star (a γ)) (fun γ => star (X.B.R (1, s γ) (star f)))
  filter_upwards [hsum, hall] with x b1 b2
  rw [b1]
  simp only [Formalism.L2.SG.Pf.RowDictPf.R_star, star_star]
  simp only [b2, (hs _).2]
  unfold gaL
  refine Eq.trans ?_ (sum_smul_apply _ _ _ _).symm
  refine Fintype.sum_equiv σ.toEquiv _ _ (fun γ => ?_)
  show _ = star (a (σ.symm (σ γ))) * _
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRows
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCarry

theorem inner_eq_zero_of_normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →ₗ[ℂ] H) (hT : Commute T (LinearMap.adjoint T)) {a b : ℂ} (hab : a ≠ b) {x y : H}
    (hx : T x = a • x) (hy : T y = b • y) : ⟪x, y⟫_ℂ = 0 := by
  set S : H →ₗ[ℂ] H := T - b • LinearMap.id with hS
  have hSy : S y = 0 := by simp [hS, hy]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ b) • LinearMap.id := by
    rw [hS, map_sub, LinearEquiv.map_smulₛₗ, LinearMap.adjoint_id]
  have hSc : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    have h1 : Commute T (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) := (Commute.one_right T).smul_right _
    have h2 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (LinearMap.adjoint T) := (Commute.one_left _).smul_left _
    have h3 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) :=
      ((Commute.one_left _).smul_left _).smul_right _
    exact (hT.sub_right h1).sub_left (h2.sub_right h3)
  have hSa : LinearMap.adjoint S y = 0 := by
    have h0 : ⟪LinearMap.adjoint S y, LinearMap.adjoint S y⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      have : S (LinearMap.adjoint S y) = LinearMap.adjoint S (S y) := by
        have := congrArg (fun f : H →ₗ[ℂ] H => f y) hSc.eq
        simpa [Module.End.mul_apply] using this
      rw [this, hSy, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 h0
  have hTa : LinearMap.adjoint T y = (starRingEnd ℂ b) • y := by
    have := hSa
    rw [hSadj, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have key : ⟪T x, y⟫_ℂ = ⟪x, LinearMap.adjoint T y⟫_ℂ := (LinearMap.adjoint_inner_right T x y).symm
  rw [hx, hTa, inner_smul_left, inner_smul_right] at key
  have hne : starRingEnd ℂ a ≠ starRingEnd ℂ b := fun h => hab ((starRingEnd ℂ).injective h)
  have : (starRingEnd ℂ a - starRingEnd ℂ b) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

theorem twSub_iSup {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (V : I → Submodule ℂ E) :
    Tw.sub s (⨆ p, V p) = ⨆ p, Tw.sub s (V p) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun p x hx => Submodule.mem_iSup_of_mem (p := V) p hx)
  exact Submodule.iSup_induction V (motive := fun y => Tw.mk s y ∈ ⨆ p, Tw.sub s (V p)) hx
    (fun p y hy => Submodule.mem_iSup_of_mem p hy) (zero_mem _) fun y z hy hz => add_mem hy hz

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem carries_of_eq (R : RealDat3 D A3 Ks) (p : A3.fam3.base3.Ix) {c c' : Pl D.host.E → List ℤ → ℂ}
    (heq : R.EEc c' = R.EEc c) (h : R.Carries p c') : R.Carries p c := by
  have key : ∀ V W : Submodule ℂ R.HE.H, V = W →
      (V ≠ ⊥ ∧ V.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) →
      (W ≠ ⊥ ∧ W.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) := by
    rintro V W rfl hV; exact hV
  exact key _ _ heq h

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry


set_option maxHeartbeats 1000000 in
theorem carried : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)

end GlobalTheory.Mem.R3.LabCarry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRowsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigensystem_carried_by_finiteType_of_meets_level_rows : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  first | exact @GlobalTheory.Mem.R3.LabCarry.carried | exact GlobalTheory.Mem.R3.LabCarry.carried | (intros; apply GlobalTheory.Mem.R3.LabCarry.carried <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemOfFiniteTypeWithParts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemOfFiniteTypeWithParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

open GlobalTheory.Hk3 (Core Good IsSF SchurAll EEc Wcc IsLab SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.Mem.R3.LabEig

def IsSphScalars {D : D7} {V : HSp D} {n : ℕ} (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  ∀ P d, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
    principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = c P d • x

theorem exists_isSphScalars {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E)
    (Q : principalLevelFrame.RowPsi V n) (hQ : StdPsi hF Q) (π : Formalism.L2.NG.FinTyp D.host.E n) : ∃ c, IsSphScalars Q π c := by
  have h : ∀ P d, ∃ a : ℂ, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
      principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = a • x := by
    intro P d
    by_cases hd : IsLab V P d
    · obtain ⟨a, ha⟩ := GlobalTheory.SphScalar.spherical_scalar hF Q hQ π P d _ (GlobalTheory.Hk3.OpsRows.sphOp_rep hd)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using h
  exact ⟨c, hc⟩

theorem isotE_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π, ∃ x ∈ EEc R SF c, R.HE.e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF n hF PY PW hPY hPW π i0 c hEig b U hU
  obtain ⟨h, hOps, hNorm, -, -, hIn⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  obtain ⟨-, hg, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨nY, hβY⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hi := hC.models.HE.1
  have hUi := Submodule.mem_inf.1 hU
  have hUE : U ∈ R.EEat (R.levR F b) := hUi.1
  have hUT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R _ hUE
  obtain ⟨x, rfl⟩ : U ∈ LinearMap.range R.HE.e := by rw [hC.models.HE.2.1]; exact hUT
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = star (c P d) • x := by
    intro P hP d hd
    have levY := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβY P
      (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hP).1 (P.isPrime.mem_of_pow_mem nY hm))
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
    have hB := GlobalTheory.Hk3.OpsRows.sphOp_rep hd
    have hdW : IsLab (Wc D i0) P d := ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP).2).2 hd
    have hB' := GlobalTheory.Hk3.OpsRows.sphOp_rep hdW
    have ha := hEig P d hdW
    obtain ⟨htr1, htr2⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF PY (PW i0) hPY (hPW i0) P d
    have hvec : ∀ y ∈ (principalLevelFrame.FinTyp.conjT π).S, (∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
        principalLevelFrame.Hecke₃ PY (GlobalTheory.Hk3.rep (Yc D 0) P d) y = star (c P d) • y := by
      intro y hy hfy
      have hy' : (fun g => star (y g)) ∈ π.S := hy
      have hfy' : ∀ κ, PY.ψ κ ∈ hyp (Yc D 0) P →
          Formalism.L2.NG.rt D.host.E n κ (fun g => star (y g)) = fun g => star (y g) := by
        intro κ hκ
        rw [← principalLevelFrame.conj_rt, hfy κ hκ]
      have e := htr2 _ _ hB hB' _ hfy'
      rw [ha _ hy' (fun κ hκ => hfy' κ ((htr1 κ).2 hκ)), GlobalTheory.TypePart.heckeOperator_conj] at e
      funext g
      have e2 := congrArg star (congrFun e g)
      simp only [Pi.smul_apply, smul_eq_mul, star_star, star_mul'] at e2
      rw [Pi.smul_apply, smul_eq_mul, e2, mul_comm]
    have hfixU : ∀ k ∈ hyp (Yc D 0) P, postOn (R.MY 0) (principalLevelFrame.rtA k) (R.HE.e x) = R.HE.e x := by
      intro k hk
      ext1 v
      rw [postOn_apply]
      funext g
      have := GlobalTheory.Hk3.OpsRows.mult_lev (goodPart_le _ _ _ _ _ hUT) v k (levY.1 k hk).1 g
      rw [(levY.1 k hk).2, one_mul] at this
      exact this
    have hU2 := GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF PY hPY R.θ (R.MY 0) (principalLevelFrame.FinTyp.conjT π) P d _ _ hB hvec _ hUi.2 hfixU
    apply hi
    rw [hOps P hP, map_smul, GlobalTheory.Hk3.OpsRows.hk_single]
    exact hU2
  refine ⟨x, hIn c x fun P d hP hd => ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hdd : IsLab (Yc D 0) P (dualLab d) := by
    have l1 := GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP
    exact l1.1.1 (l1.2.2 hd)
  have h1 := key P hP d hd
  have e := GlobalTheory.TypePart.star_eq_of_adj hNorm hP d hx0 h1 (key P hP _ hdd)
  have e' : star (c P d) = c P (dualLab d) := by
    rw [star_star] at e
    rw [e, star_star]
  rw [h1, e']

theorem isotL_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF n hF PW hPW π i0 c hEig i U hU
  have hLev := hC.lev
  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P
  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'
  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  have hd0 : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  have hB0 := GlobalTheory.Hk3.OpsRows.sphOp_rep hd0
  have ha := hEig P d hd0
  obtain ⟨hiff, htr⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B _ hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ))]
  have hUfix : ∀ k ∈ hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

theorem eig_parts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  intro hW hDS hHC hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨hC3, hSF, -, -, hEE, hWc, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hPins.char
  have hCore := hC3 hHolds.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  have hPY : StdPsi Y.hF Y.PY := Y.stdPsi.1
  have hPW : ∀ i, StdPsi Y.hF (Y.PW i) := Y.stdPsi.2
  obtain ⟨c, hc⟩ := exists_isSphScalars Y.hF (Y.PW ⟨0, Y.hm⟩) (hPW _) (principalLevelFrame.rowRepR R.θ (Y.eFT σ))
  refine ⟨c, fun b U hU => ?_, fun i U hU => ?_⟩
  · obtain ⟨x, hx, hxU⟩ := isotE_sub R.toRealDat F.lv2 hCore hS R.SF hSF Y.hF Y.PY Y.PW hPY hPW _ ⟨0, Y.hm⟩ c hc b U hU
    exact ⟨x, by rw [hEE]; exact hx, hxU⟩
  · obtain ⟨x, hx, hxU⟩ := isotL_sub R.toRealDat F.lv2 hCore R.SF hSF Y.hF Y.PW hPW _ ⟨0, Y.hm⟩ c hc i U hU
    exact ⟨x, by rw [hWc]; exact hx, hxU⟩

end GlobalTheory.Mem.R3.LabEig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemOfFiniteTypeWithPartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_of_finiteType_with_parts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  first | exact @GlobalTheory.Mem.R3.LabEig.eig_parts | exact GlobalTheory.Mem.R3.LabEig.eig_parts | (intros; apply GlobalTheory.Mem.R3.LabEig.eig_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem coBear_comp_of_isHom : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ ψ hψ hgen g hg K _ p
  have hgf : g ≫ f₂ = f₁ := by
    have := h₂.1.comp hg
    rw [hψ] at this
    exact this.unique h₁.1

  let y : Y₁.X := p (IsLocalRing.closedPoint K)
  let R := Y₁.X.presheaf.stalk y
  let v₁ : Sp R ⟶ Y₁.X := Y₁.X.fromSpecStalk y
  have hpt : spMap (algebraMap R Y₁.Fn) ≫ v₁ = (ratOf Y₁).pt :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ R Y₁.Fn v₁ (v₁ ≫ g)
    (by rw [Category.assoc, hgf]) (by
      have e1 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ f₁ = (ratOf Y₁).pt ≫ f₁ := by
        rw [← Category.assoc]; exact congrArg (· ≫ f₁) hpt
      have e2 : spMap (algebraMap R Y₁.Fn) ≫ v₁ ≫ g = spMap ψ.toRingHom ≫ (ratOf Y₂).pt := by
        rw [← Category.assoc, hpt]; exact hg
      rw [e1, hpt, e2]; exact hgen)

  let c := Scheme.stalkClosedPointTo (R := .of K) p
  let σ : IsLocalRing.ResidueField R →+* K := IsLocalRing.ResidueField.lift c.hom
  have hσ : σ.comp (IsLocalRing.residue R) = c.hom := IsLocalRing.ResidueField.lift_comp_residue c.hom
  have hp : spMap σ ≫ spMap (IsLocalRing.residue R) ≫ v₁ = p := by
    rw [← Category.assoc, ← spMap_comp, hσ]
    exact spMap_stalkClosedPointTo p
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ (IsLocalRing.ResidueField R) K σ _ _ _ hinc
  rw [← hp]
  simpa only [Category.assoc] using hbc

end GlobalTheory.FlagBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGenericStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.coBear_comp_of_isHom | exact GlobalTheory.FlagBundle.coBear_comp_of_isHom | (intros; apply GlobalTheory.FlagBundle.coBear_comp_of_isHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member.character_quotient_values_in_embedding_field

theorem small_quot_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (k : Type) [Field k] (σ : k →+* ℂ), SmallIn R i σ → (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) σ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i k _ σ h v hv
  have hE : R.C.eta.UnrAt v := R.C.isEta.unr v
  have hM : (R.C.mu0 i).UnrAt v := by
    intro x hx
    have h1 := hv x hx
    have h2 := hE x hx
    have h3 : ((R.C.mu0 i * R.C.eta⁻¹).loc v) x = (R.C.mu0 i).loc v x * (R.C.eta.loc v x)⁻¹ := rfl
    rw [h3, h2, inv_one, mul_one] at h1
    exact h1
  obtain ⟨y1, hy1⟩ := h.1 v hM
  obtain ⟨y2, hy2⟩ := h.2 v hE
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast this
  have hval : ((R.C.mu0 i * R.C.eta⁻¹).val v : ℂ) = ((R.C.mu0 i).val v : ℂ) * ((R.C.eta.val v : ℂ))⁻¹ := by
    have : (R.C.mu0 i * R.C.eta⁻¹).val v = (R.C.mu0 i).val v * (R.C.eta.val v)⁻¹ := rfl
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]
  have hy2' : σ y2 ≠ 0 := by
    rw [hy2, Formalism.L2.Host.HChar.valTw]
    exact mul_ne_zero (Units.ne_zero _) ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hN)
  refine ⟨y1 / y2, ?_⟩
  rw [map_div₀, hy1, hy2]
  simp only [Formalism.L2.Host.HChar.valTw, hval]
  have e1 : (-((-1 / 2 : ℝ) : ℂ)) = -(-((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, Complex.cpow_neg _ (-((1/2 : ℝ) : ℂ))]
  push_cast
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  field_simp

end GlobalTheory.Member.character_quotient_values_in_embedding_field
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_quotient_values_in_embedding_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (k : Type) [Field k] (σ : k →+* ℂ), SmallIn R i σ → (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) σ := by
  first | exact @GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values | exact GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values | (intros; apply GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.IsotPart

theorem stdPsi_of_stdFrame {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (h : GlobalTheory.Mem.R3.StdFrame hF P) : GlobalTheory.StdFrame.StdPsi hF P := h


set_option maxHeartbeats 2000000 in
theorem isot_le_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hC i
  obtain ⟨hcore, hSF, -, hW⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hcore.lev).1
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    intro v
    have hS : R.Sb = R.Pg := hP.char.allPl
    rw [ht]
    unfold SsetF
    rw [hQ, hS]
    simp only [Finset.union_empty, Finset.mem_image]
    constructor
    · rintro ⟨PP, h1, rfl⟩
      exact ⟨PP, h1, rfl⟩
    · rintro ⟨PP, h1, h2⟩
      exact ⟨PP, h1, HeightOneSpectrum.ext h2⟩
  have hEq : SsetF R.toRealDat (Y.tupT D.what₂.mu0) = R.SF := by
    ext v
    rw [hSF v, hSF' v]
  unfold HasEig at hE
  rw [hEq] at hE
  intro y hy
  have hy' := (Y.tied.lift.isot i π y).1 hy
  rw [Y.prtWE, Y.mjRead] at hy'
  obtain ⟨U, hU, hUy⟩ := hy'
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hcore R.SF hSF Y.hF Y.PY Y.PW
    (stdPsi_of_stdFrame Y.stdPsi.1) (fun j => stdPsi_of_stdFrame (Y.stdPsi.2 j)) _ _ c hE i U hU
  have h1 : U = (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hUy
  have h2 : x = Y.mj.eW i y := (hcore.models.HW i (sg0 D A3.A)).1 (hxU.trans h1)
  rw [Submodule.mem_comap, ← h2]
  rw [← hW] at hx
  exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.Wc' i c) c hC) hx

end GlobalTheory.Mem.R3.IsotPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrank
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamDim

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : V ≃+ Tw.sub s V :=
    { toFun := fun x => ⟨Tw.mk s (x : E), x.2⟩
      invFun := fun y => ⟨Tw.out (y : Tw s E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hi : Function.Bijective (cj s) :=
    ⟨fun a b h => by simpa [cj_cj] using congrArg (cj s) h, fun z => ⟨cj s z, cj_cj s z⟩⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hi (fun r m => by
    apply Subtype.ext
    show r • (m : E) = cj s (cj s r) • (m : E)
    rw [cj_cj])
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := by
  ext x; exact Iff.rfl

theorem finrank_comap_of_inj {M E : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup E] [Module ℂ E]
    (f : M →ₗ[ℂ] E) (hf : Function.Injective f) (S : Submodule ℂ E) :
    Module.finrank ℂ (S.comap f) = Module.finrank ℂ (S ⊓ LinearMap.range f : Submodule ℂ E) := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf (S.comap f)), Submodule.map_comap_eq, inf_comm]

end GlobalTheory.Mem.R3.LamDim


open GlobalTheory.Mem.R3.LamDim in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  set s := twAt D.what₂.embLL A3.A.v0 with hs

  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero, zero_pow two_ne_zero] at h1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

  have hrg : LinearMap.range (Y.mj.eW i) = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [Y.mj.eW_range i, hH.aux.levelW false i (sg0 D A3.A)]

  have hw : LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) •
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).1 ∈ _
      exact Submodule.smul_mem (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) _
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).2
    · intro x hx
      have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
          Submodule.comap (Tw.mkL s (R.HW i (sg0 D A3.A)).H) (LinearMap.range ((R.toCx3 F).w0C false i)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
      exact hle hx
  have hD := hH.prim.dimParts i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have key := CxData.finrank_Ep (R.toCx3 F) F.cr false (hR.wf false) (hR.what₂ false).1 (hR.rowHyp false).h3
    (hR.partsE false) p
  have key2 : Module.finrank D.what₂.LL ((s0Of R F).Ep p) =
      Module.finrank ℂ ((R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) := key
  rw [key2, ← hD, finrank_comap_of_inj _ hinj, hrg, hw]
  show _ = Module.finrank ℂ (Tw.sub s (R.Wp3 i p) ⊓ Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) : Submodule ℂ _)
  rw [← twSub_inf, finrank_twSub]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrankStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  first | exact @GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | exact GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 | (intros; apply GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 <;> assumption)
end
end
