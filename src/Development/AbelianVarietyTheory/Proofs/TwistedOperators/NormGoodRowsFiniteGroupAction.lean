module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_gE_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hE hg h0 g x
  unfold RealDat.models_HE RealDat.models_gE RealDat.models_ν0 at *
  obtain ⟨hinj, hrange, hip⟩ := hE
  obtain ⟨hm, hfd⟩ := h0
  obtain ⟨hHaar, -⟩ := hm

  let u : R.HE.H ≃ₗ[ℂ] R.HE.H :=
    LinearEquiv.ofLinear (R.gE g) (R.gE g⁻¹)
      (by
        ext y
        show R.gE g (R.gE g⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (by
        ext y
        show R.gE g⁻¹ (R.gE g y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])

  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have hy : R.HE.e y ∈ LinearMap.range R.HE.e := ⟨y, rfl⟩
    rw [hrange] at hy
    exact (Submodule.mem_inf.mp hy).1

  have hact : ∀ y v, R.HE.e (u y) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e y v) := by
    intro y v
    show R.HE.e (R.gE g y) v = _
    rw [hg]
    rfl
  exact GlobalTheory.T.norm_eq_of_actG0_intertwining_isometric_embedding R.θ (R.MY 0) (R.βY 0) (R.dat0 R.triv) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) R.HE.H R.HE.e 1 R.ν0 R.fd0
    (fun y z => by rw [one_mul]; exact hip y z) hinj hmem hHaar hfd (R.eG g) u hact x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupActionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_goodRows_finiteGroup_action : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  first | exact @GlobalTheory.norm_gE_rows | exact GlobalTheory.norm_gE_rows | (intros; apply GlobalTheory.norm_gE_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.ParabConj

theorem stdBlocks_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s} (i : Fin (d a)) (j : Fin (d b))
    (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_stdMaxParab_of_le_conjBy (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r) (g : GL (Fin r) F) (H : parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h)) :
    g ∈ stdMaxParab F h := by
  by_contra hg
  have hg' := hg
  rw [mem_stdMaxParab] at hg'
  push Not at hg'
  obtain ⟨q, j, hj, hq, hne⟩ := hg'
  refine hg (inv_mem_iff.1 ((mem_stdMaxParab h).2 fun i p hp hi => ?_))
  have hpq : p < q := by rw [Fin.lt_def]; omega
  let t : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : F))
    (by rw [Matrix.det_transvection_of_ne p q hpq.ne]; exact one_ne_zero)
  have ht : (t : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q 1 := rfl
  have htP : t ∈ parab F (stdBlocks d hd) := by
    refine mem_parab_iff.2 fun x y u v hyx => ?_
    have hlt := stdBlocks_lt d hd u v hyx
    rw [ht, Matrix.add_apply, Matrix.one_apply_ne hlt.ne', zero_add]
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨e1, e2⟩
    rw [← e1, ← e2] at hlt
    exact lt_asymm hlt hpq
  have h0 := (mem_stdMaxParab h).1 (mem_conjBy.1 (H htP)) i j hj hi
  have hij : i ≠ j := by rintro rfl; omega
  have hmul : ((g⁻¹ * t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * Matrix.single p q (1 : F) *
        (g : Matrix (Fin r) (Fin r) F) := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, add_mul, mul_one, Units.inv_mul]
  rw [hmul, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.mul_apply,
    Finset.sum_eq_single q (fun x _ hx => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]) (by simp),
    Matrix.mul_single_apply_same, mul_one] at h0
  exact (mul_eq_zero.1 h0).resolve_right hne

end GlobalTheory.ParabConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConjStatement
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod]
    simp only [h, MultilinearMap.map_smul_univ, RingHom.id_apply]
    rw [smul_comm]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp [leviEmb, blockDiagonal'_apply_eq, GeneralLinearGroup.scalar, diagonal_apply]
    · simp [leviEmb, blockDiagonal'_apply_ne _ _ _ hab, GeneralLinearGroup.scalar,
        diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have hm : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    rw [h1]
    simp [GeneralLinearGroup.scalar, diagonal_apply, hab.ne']
  have hp : leviProj k e ⟨_, hm⟩ = (fun a => GeneralLinearGroup.scalar (m a) z) := by
    funext a
    ext i j
    simp [leviProj, diagBlock, leviEmb, GeneralLinearGroup.scalar, diagonal_apply]
  have h2 := parInd_law e _ f ⟨_, hm⟩ x
  rw [hp, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear
section -- merged from Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.SubsingletonOfEvInj
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalInj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem evAt_injective_of_ne {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : ∀ τ, (v τ : (R.MW i σ).H τ) ≠ 0) : Function.Injective (evAt R i σ v) := by
  intro x y hxy
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [map_sub]
    show (R.HW i σ).e x v - (R.HW i σ).e y v = 0
    exact sub_eq_zero.2 hxy
  have hip : ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) = 0 := by
    by_cases h : ∃ c, IsMultIP (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e (x - y)) ((R.HW i σ).e (x - y)) c
    · have h1 := (ipM_spec _ _ _ _ _ h v v).2
      rw [h0] at h1
      simp only [Pi.zero_apply, mul_zero, integral_zero] at h1
      rcases mul_eq_zero.1 h1.symm with h2 | h2
      · exact h2
      · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h2
        exact absurd (inner_self_eq_zero.1 hτ) (hv τ)
    · unfold ipM
      rw [dite_eq_right h]
  have h3 := (hm i σ).2.2 (x - y) (x - y)
  unfold ipAt at h3
  rw [hip, mul_zero] at h3
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

end GlobalTheory.EvalInj
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEval

theorem exists_label {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    ∃ τ, labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      labE σ (D.eTau.symm ⟨t, ht⟩) = D.host.emb (g * t) := fun t ht => by
    refine RingHom.ext fun x => ?_
    have h1 : D.host.sigmaOf (g * t) = D.host.sigmaOf g * D.host.sigmaOf t :=
      map_mul (D.host.gal).symm g t
    show (σ.comp D.embE) (D.host.sigmaOf (D.eTau (D.eTau.symm ⟨t, ht⟩)).1 x) = D.host.φ₀ (D.host.sigmaOf (g * t) x)
    rw [Equiv.apply_symm_apply, ← hg, h1]
    rfl
  by_cases h : g⁻¹ * (D.eTau ρ).1 ∈ D.R.Psi
  · refine ⟨D.eTau.symm ⟨_, h⟩, Or.inl ?_⟩
    rw [key, mul_inv_cancel_left]
    rfl
  · have h' : g⁻¹ * (D.eTau ρ).1 * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, mul_assoc, mul_inv_cancel_left, Formalism.L2.Geo.emb_mul_cc_comp]
    exact RingHom.ext fun x => D.host.conjE_apply (tauE D ρ) x

theorem conj_comp_eq_iff {E : Type} [Field E] (a b : E →+* ℂ) :
    (starRingEnd ℂ).comp a = b ↔ a = (starRingEnd ℂ).comp b := by
  constructor
  · rintro rfl
    ext x; simp
  · rintro rfl
    ext x; simp

theorem labE_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

theorem lab_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ := by
  have e : (fun τ => labE ((starRingEnd ℂ).comp σ) τ = tauE D ρ ∨
        labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (tauE D ρ)) =
      fun τ => labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    funext τ
    rw [labE_conj, conj_comp_eq_iff, conj_comp_eq_iff, ← (conj_comp_eq_iff (tauE D ρ) _).1 rfl, or_comm]
  unfold lab
  rw [dite_eq_left (exists_label _ ρ), dite_eq_left (exists_label σ ρ)]
  congr 1

theorem evEx_conj {K C H H' Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] (σ : K →+* ℂ) (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev') (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (φ : C → Y → ℂ)
    (h : EvEx ((starRingEnd ℂ).comp σ) ev φ) : EvEx σ ev' fun f g => starRingEnd ℂ (φ f g) := by
  obtain ⟨j, hj⟩ := h
  choose x hx using hx
  refine ⟨⟨⟨fun f => x (j f), fun f f' => hinj (funext fun g => ?_)⟩, fun a f => hinj (funext fun g => ?_)⟩,
    fun f => funext fun g => ?_⟩
  · rw [ha', hx, hx, hx, map_add (f := _), ha, map_add (f := _)]
  · refine (hx _ g).trans ?_
    rw [j.map_smulₛₗ, hs, hs', hx, map_mul, RingHom.comp_apply, Complex.conj_conj]
  · exact (hx (j f) g).trans (congrArg (starRingEnd ℂ) (congrFun (hj f) g))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem levChi_principal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [h1]
  simp [LevCh.datWp, datY]

end GlobalTheory.ConjEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidification
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.RigExists

theorem exists_cartan_onb {k p q : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (h : Formalism.UG.HasSignature G p q) :
    ∃ s B : Matrix (Fin k) (Fin k) ℂ, IsCartanInv G s ∧ IsONBasis G s B p := by
  obtain ⟨e, P, hP⟩ := h
  have hk : k = p + q := by simpa using Fintype.card_congr e
  subst hk
  set f : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm with hf
  set ε : Fin (p + q) → ℝ := fun a => if a.val < p then 1 else -1 with hε
  set B : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := (P : Matrix _ _ ℂ).submatrix e f with hB
  set A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).submatrix f e with hA
  set Dg : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := Matrix.diagonal fun a => (ε a : ℂ) with hDg
  have e1 : B * A = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ f.bijective, Units.mul_inv, Matrix.submatrix_one_equiv]
  have e2 : A * B = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_one_equiv]
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j; simp
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (P : Matrix _ _ ℂ)ᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT] at hP
  have hD : Bᴴ * G * B = Dg := by
    have : Bᴴ * G * B = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * G.reindex e e *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix f f := by
      rw [hB, Matrix.conjTranspose_submatrix, hG, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
        ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← hG]
    rw [this, hP]
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [Formalism.UG.Jpq, hf, hDg, hε, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> (try omega) <;> split_ifs <;> simp
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; simp only [hε]; split_ifs <;> simp
  have hDh : Dgᴴ = Dg := by
    rw [hDg, Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp [hε]
  have e3 : Bᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  have e4 : Aᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have hGA : G = Aᴴ * Dg * A := by
    rw [← hD]
    calc G = (Aᴴ * Bᴴ) * G * (B * A) := by rw [e4, e1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨B * Dg * A, B, ⟨?_, ?_, ?_⟩, ε, fun a => ?_, hD, ?_⟩
  · calc B * Dg * A * (B * Dg * A) = B * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one, e1]
  · conv_lhs => rw [hGA]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ Aᴴ, e3, Matrix.one_mul, ← Matrix.mul_assoc A B, e2, Matrix.one_mul,
      ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hGA, Matrix.mul_assoc]
  · have : G * (B * Dg * A) = Aᴴ * A := by
      rw [hGA]
      calc Aᴴ * Dg * A * (B * Dg * A) = Aᴴ * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
        _ = Aᴴ * A := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one]
    rw [this]
    exact Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e1)))
  · simp only [hε]; split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, not_lt.1 h⟩
  · calc B * Dg * A * B = B * Dg * (A * B) := by simp only [Matrix.mul_assoc]
      _ = B * Dg := by rw [e2, Matrix.mul_one]

theorem exists_rig : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  intro D V Λ hV hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hfull
  have hτ : ∀ τ : D.what₂.Tau, ∃ s B : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      IsCartanInv (gramAt D V τ) s ∧ ∃ p, IsONBasis (gramAt D V τ) s B p := fun τ => by
    obtain ⟨s, B, h1, h2⟩ := exists_cartan_onb (gramAt D V τ) (hV (tauE D τ))
    exact ⟨s, B, h1, _, h2⟩
  choose s B hsB using hτ
  exact ⟨⟨Λ, β, s, B⟩, rfl, hΛ, hβ, hsB⟩

end GlobalTheory.RigExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidificationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_has_rigidification : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK → IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  first | exact @GlobalTheory.RigExists.exists_rig | exact GlobalTheory.RigExists.exists_rig | (intros; apply GlobalTheory.RigExists.exists_rig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacProj

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem coords {m : ℕ} (v : Mx D S.rank m) :
    v = d.jX ⬝ (d.pX ⬝ v) + d.j0 ⬝ (d.p0 ⬝ v) + d.jY ⬝ (d.pY ⬝ v) := by
  conv_lhs => rw [← Matrix.one_mul v, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem pY_inv (g : GA D S) : d.pY ⬝ mt S g⁻¹ = adj (mt S g ⬝ d.jX) ⬝ gA S := by
  rw [mt_inv, d.pY_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

theorem witt_anisotropic_projection_unitary_inv_eq (g : GA D S) : d.p0 ⬝ mt S g⁻¹ = giA S₀ ⬝ (adj (mt S g ⬝ d.j0) ⬝ gA S) := by
  rw [mt_inv, d.p0_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def Keeps (g : GA D S) : Prop :=
  d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.j0) = 0

theorem expand {k m : ℕ} (Q : Mx D k S.rank) (A B : Mx D S.rank S.rank) (v : Mx D S.rank m) :
    Q ⬝ ((A * B) ⬝ v) = Q ⬝ (A ⬝ d.jX) ⬝ (d.pX ⬝ (B ⬝ v)) + Q ⬝ (A ⬝ d.j0) ⬝ (d.p0 ⬝ (B ⬝ v)) +
      Q ⬝ (A ⬝ d.jY) ⬝ (d.pY ⬝ (B ⬝ v)) := by
  conv_lhs => rw [← Matrix.mul_one A, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem keeps_jX {g : GA D S} (h : Keeps d g) : mt S g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jX)) := by
  have e := coords d (mt S g ⬝ d.jX)
  rw [h.1, h.2.1] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem preserves_flag_anisotropic_action {g : GA D S} (h : Keeps d g) :
    mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
  have e := coords d (mt S g ⬝ d.j0)
  rw [h.2.2] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem keeps_unitary {g : GA D S} (h : Keeps d g) :
    adj (d.p0 ⬝ (mt S g ⬝ d.j0)) ⬝ (gA S₀ ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0))) = gA S₀ := by
  have hXX : ∀ {k : ℕ} (M : Mx D ρ k), adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_XX, Matrix.zero_mul]
  have hX0 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
  have h0X : ∀ {k : ℕ} (M : Mx D ρ k), adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_0X, Matrix.zero_mul]
  have h00 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ M)) = gA S₀ ⬝ M := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_00]
  have hu : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
    calc adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))
        = adj d.j0 ⬝ ((adj (mt S g) * (gA S * mt S g)) ⬝ d.j0) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = gA S₀ := by rw [mt_unitary, d.gram_00]
  rw [preserves_flag_anisotropic_action d h] at hu
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = P at hu
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = C at hu ⊢
  simpa only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, hX0, h0X, h00,
    Matrix.mul_zero, zero_add, add_zero] using hu

theorem keeps_mul {g g' : GA D S} (h : Keeps d g) (h' : Keeps d g') : Keeps d (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, expand, h.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h.2.2, h'.2.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem keeps_inv {g : GA D S} (h : Keeps d g) : Keeps d g⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ ρ, mt S g ⬝ d.jX = d.jX ⬝ P := ⟨_, keeps_jX d h⟩
  obtain ⟨P', C, hC⟩ : ∃ (P' : Mx D ρ S₀.rank) (C : Mx D S₀.rank S₀.rank), mt S g ⬝ d.j0 = d.jX ⬝ P' + d.j0 ⬝ C := ⟨_, _, preserves_flag_anisotropic_action d h⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hC]
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.gram_XX, d.gram_0X,
      Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.gram_XX, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.mul_zero]

theorem preserves_flag_anisotropic_block_one_inv {g : GA D S} (h : Keeps d g) (h1 : d.p0 ⬝ (mt S g ⬝ d.j0) = 1) : d.p0 ⬝ (mt S g⁻¹ ⬝ d.j0) = 1 := by
  have e := preserves_flag_anisotropic_action d h
  rw [h1, Matrix.mul_one] at e
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.jX ⬝ P + d.j0 := ⟨_, e⟩
  rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hP]
  simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, d.gram_00,
    Matrix.mul_zero, zero_add]
  exact giA_mul_gA S₀

theorem keeps_one : Keeps d 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mt_one, Matrix.one_mul]
  · exact d.p0_jX
  · exact d.pY_jX
  · exact d.pY_j0

def keepSub : Subgroup (GA D S) where
  carrier := {g | Keeps d g}
  one_mem' := keeps_one d
  mul_mem' := keeps_mul d
  inv_mem' := keeps_inv d

def keepSub1 : Subgroup (GA D S) where
  carrier := {g | Keeps d g ∧ d.p0 ⬝ (mt S g ⬝ d.j0) = 1}
  one_mem' := ⟨keeps_one d, by rw [mt_one, Matrix.one_mul, HypDec.p0_j0]⟩
  mul_mem' := fun {a b} ha hb => ⟨keeps_mul d ha.1 hb.1, by
    rw [mt_mul, expand, ha.1.1, ha.2, hb.1.2.2, hb.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]⟩
  inv_mem' := fun {a} ha => ⟨keeps_inv d ha.1, preserves_flag_anisotropic_block_one_inv d ha.1 ha.2⟩

theorem flag_le : flagN d ≤ keepSub1 d := by
  intro n hn
  obtain ⟨T, b, -, hX, h0⟩ := exists_blocks d hn
  have eX : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.jX) = Q ⬝ d.jX + Q ⬝ d.jX ⬝ T := fun Q => by
    rw [hX, Matrix.mul_add, Matrix.mul_assoc]
  have e0 : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.j0) = Q ⬝ d.j0 + Q ⬝ d.jX ⬝ b := fun Q => by
    rw [h0, Matrix.mul_add, Matrix.mul_assoc]
  show (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [eX, d.p0_jX, Matrix.zero_mul, add_zero]
  · rw [eX, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.pY_j0, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.p0_j0, d.p0_jX, Matrix.zero_mul, add_zero]

theorem range_le : d.emb0.range ≤ keepSub d := by
  rintro _ ⟨h, rfl⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.p0_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.pY_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.pY_j0, Matrix.zero_mul]

theorem jac_le : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) ≤ keepSub d :=
  sup_le (fun _ hg => (flag_le d hg).1) (range_le d)

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 h) ⬝ d.j0) = mt S₀ h := by
  have h1 : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := (flag_le d hn).2
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, h1,
    Matrix.one_mul]

def proj (g : (flagN d ⊔ d.emb0.range : Subgroup (GA D S))) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ (mt S g.1 ⬝ d.j0)) (keeps_unitary d (jac_le d g.2))

theorem continuous_proj : Continuous (proj d) := by
  apply continuous_of_mt
  simp only [proj, mt_ofMat]
  exact continuous_const.matrix_mul (((continuous_mt S).comp continuous_subtype_val).matrix_mul continuous_const)

theorem proj_mul (h : GA D S₀) (n : flagN d) :
    proj d ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  apply mt_injective S₀
  simp only [proj, mt_ofMat]
  exact witt_anisotropic_block_flag_mul_embedded d n.2 h

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ p : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) → GA D S₀, Continuous p ∧
      ∀ (h : GA D S₀) (n : flagN d),
        p ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ ρ d
  exact ⟨proj d, continuous_proj d, proj_mul d⟩

end GlobalTheory.JacProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.FrameAdjAdd

theorem frMapAdj_add_isIntM_redM : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  intro D S T βS βT x y hx hy
  have hadd : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
    unfold frMapAdj
    rw [Matrix.map_add (⇑(cA D)) (map_add (cA D)), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.map_add (⇑(toEAf D)) (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]
  have hI : IsIntM (frMapAdj S T βS βT (x + y)) := by
    intro i j
    rw [hadd]
    exact add_mem (hx i j) (hy i j)
  refine ⟨hI, fun PP => ?_⟩
  ext i j
  have h1 := hI i j
  have h2 := hx i j
  have h3 := hy i j
  simp only [redM, Matrix.add_apply, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← RingHom.map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp [hadd]

end GlobalTheory.FrameAdjAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameMatrix_add_integral_reduction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  first | exact @GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | exact GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | (intros; apply GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacu
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacu
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem exists_linearForm_invariant_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs hfix hspan A hA
  have key : ∀ z y, y - z ∈ Λ → W z s = γ (w • z) (y - z) • W y s := by
    intro z y hyz
    have h1 := h.comp z (y - z) s
    rwa [hfix _ hyz, add_sub_cancel] at h1
  let P : X ⧸ Λ → Prop := fun q => ∃ a ∈ A, (Submodule.Quotient.mk a : X ⧸ Λ) = q
  let rep : X ⧸ Λ → X := fun q => if hq : P q then hq.choose else Quotient.out q
  have hrep : ∀ q, (Submodule.Quotient.mk (rep q) : X ⧸ Λ) = q := by
    intro q
    by_cases hq : P q
    · simp only [rep, dif_pos hq]; exact hq.choose_spec.2
    · simp only [rep, dif_neg hq]; exact Quotient.out_eq q
  have hrepA : ∀ q, P q → rep q ∈ A := by
    intro q hq
    simp only [rep, dif_pos hq]; exact hq.choose_spec.1
  let e : X ⧸ Λ → M := fun q => W (rep q) s
  have he : ∀ z, W z s = γ (w • z) (rep (Submodule.Quotient.mk z) - z) • e (Submodule.Quotient.mk z) := by
    intro z
    exact key z _ ((Submodule.Quotient.eq Λ).1 (hrep _))
  have hli : LinearIndependent ℂ e := by
    refine linearIndependent_of_simultaneous_eigen e (fun q (l : Λ) => γ l (rep q)) (fun l : Λ => W l) ?_ ?_ ?_
    · intro q q' hq
      have hm : rep q - rep q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (rep q) = γ a (rep q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← hrep q, ← hrep q']
      exact (Submodule.Quotient.eq Λ).2 hm
    · intro l q
      show W l (W (rep q) s) = γ l (rep q) • W (rep q) s
      rw [h.comm, hfix l l.2]
    · intro q h0
      have h1 := h.neg_comp (rep q) s
      rw [show W (rep q) s = 0 from h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [he z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  let ℓ : M →ₗ[ℂ] ℂ := b.constr ℂ (fun q => if P q then (1 : ℂ) else 0)
  have hℓ : ∀ q, ℓ (e q) = if P q then (1 : ℂ) else 0 := by
    intro q
    have := b.constr_basis ℂ (fun q => if P q then (1 : ℂ) else 0) q
    rwa [Module.Basis.mk_apply] at this
  have hwA : ∀ a ∈ A, ∀ b ∈ A, γ (w • a) b = 1 := fun a ha b hb => hA _ (A.smul_mem w ha) b hb
  refine ⟨ℓ, ?_, ?_⟩
  · have h0 : P (Submodule.Quotient.mk 0) := ⟨0, A.zero_mem, rfl⟩
    have h1 := he 0
    rw [h.zero, hwA 0 A.zero_mem _ (A.sub_mem (hrepA _ h0) A.zero_mem), one_smul] at h1
    rw [h1, hℓ, if_pos h0]
  · intro a ha v
    have hext : ℓ ∘ₗ W a = ℓ := by
      refine b.ext fun q => ?_
      rw [Module.Basis.mk_apply, LinearMap.comp_apply]
      show ℓ (W a (W (rep q) s)) = ℓ (e q)
      rw [h.comp, he (a + rep q), map_smul, map_smul, hℓ, hℓ]
      by_cases hq : P q
      · have hA1 : a + rep q ∈ A := A.add_mem ha (hrepA q hq)
        have hq' : P (Submodule.Quotient.mk (a + rep q)) := ⟨_, hA1, rfl⟩
        rw [if_pos hq, if_pos hq', hwA a ha _ (hrepA q hq), hwA _ hA1 _ (A.sub_mem (hrepA _ hq') hA1)]
        simp
      · have hq' : ¬ P (Submodule.Quotient.mk (a + rep q)) := by
          rintro ⟨c, hc, hce⟩
          apply hq
          refine ⟨c - a, A.sub_mem hc ha, ?_⟩
          rw [Submodule.Quotient.mk_sub, hce, ← Submodule.Quotient.mk_sub, add_sub_cancel_left, hrep]
        rw [if_neg hq, if_neg hq']
        simp
    exact LinearMap.congr_fun hext v

end GlobalTheory.SphTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacuStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  first | exact @GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | exact GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum | (intros; apply GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum <;> assumption)
end
end
