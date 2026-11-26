module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem pairwise_commute {θ : InfFam D} {V : HSp D} {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ((Finset.univ : Finset D.what₂.Tau) : Set D.what₂.Tau).Pairwise
      (Function.onFun Commute fun τ => atTau θ V τ (g τ)) :=
  fun τ _ τ' _ hne => GlobalTheory.PointAtPlaceComm.atTau_comm D θ h.1 V τ τ' hne _ (h.2 τ) _ (h.2 τ')

def realProd (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then
    Finset.univ.noncommProd (fun τ => atTau θ V τ (g τ)) (pairwise_commute h)
  else 1

variable {θ : InfFam D} {V : HSp D}

theorem update_mem {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) (τ : D.what₂.Tau) :
    Function.update g τ₀ g' τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  by_cases h : τ = τ₀
  · subst h; rw [Function.update_self]; exact hg'
  · rw [Function.update_of_ne h]; exact hg τ

theorem realProd_update (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    realProd θ V (Function.update g τ₀ g') = atTau θ V τ₀ g' * realProd θ V (Function.update g τ₀ 1) := by
  classical
  have h1 := update_mem hg τ₀ hg'
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h1⟩, dite_eq_left ⟨hθ, h2⟩, ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀),
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀) (fun τ => atTau θ V τ (Function.update g τ₀ 1 τ))]
  simp only [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ, one_mul]
  congr 1
  refine Finset.noncommProd_congr rfl (fun τ hτ => ?_) _
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ), Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem realProd_commute (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    Commute (atTau θ V τ₀ g') (realProd θ V (Function.update g τ₀ 1)) := by
  classical
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h2⟩]
  refine Finset.noncommProd_commute _ _ _ _ fun τ _ => ?_
  by_cases h : τ = τ₀
  · subst h
    rw [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact Commute.one_right _
  · exact GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ₀ τ (Ne.symm h) _ hg' _ (h2 τ)

theorem realProd_one (hθ : IsInfFam θ) : realProd θ V (fun _ => 1) = 1 := by
  unfold realProd
  rw [dite_eq_left ⟨hθ, fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _⟩]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun τ _ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ, one_pow]

theorem isAutFunSm_realProd (hθ : IsInfFam θ) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V (realProd θ V g) φ) := by
  unfold realProd
  split_ifs with h
  · refine Finset.noncommProd_induction _ _ _ (fun x => ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (rTr V x ψ))
      (fun a b ha hb ψ hψ => ?_) (fun ψ hψ => ?_) (fun τ _ ψ hψ => ?_) φ hφ
    · have e : rTr V (a * b) ψ = rTr V a (rTr V b ψ) := funext fun x => by simp only [rTr, mul_assoc]
      rw [e]; exact ha _ (hb _ hψ)
    · have e : rTr V 1 ψ = ψ := funext fun x => by simp only [rTr, mul_one]
      rw [e]; exact hψ
    · exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V ψ hψ τ _ (h.2 τ)
  · have e : rTr V 1 φ = φ := funext fun x => by simp only [rTr, mul_one]
    rw [e]; exact hφ

theorem rep_mul {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  unfold DSModel.rep
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg) _
    (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hh)

theorem rep_one {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem sm_eq_top {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] :
    M.sm τ = ⊤ := by
  rw [GlobalTheory.SmVec.sm_eq]
  refine Submodule.orthogonal_eq_bot_iff.1 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
  exact GlobalTheory.SmVec.eq_zero_of_inner_smooth (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    fun u hu => (Submodule.mem_orthogonal _ _).1 hy u hu

theorem equiv_one {H G : Type} [AddCommGroup H] [Module ℂ H] [Module.Free ℂ H] [Module.Finite ℂ H] [Mul G]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    {m : ℕ} (k : Fin m → G) (hk : ∀ j, k j ∈ K) (B : Fin m → (H →ₗ[ℂ] H))
    (hB : ∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j)
    (f : G → ℂ) (hf : ∀ g ∈ K, f g = ∑ j, f (k j) * LinearMap.trace ℂ H (ρ g ∘ₗ B j))
    (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K) (e : H →ₗ[ℂ] ℂ) (v : H) {h : G} (hh : h ∈ K) :
    ∑ j, e (B j (ρ h v)) * f (k j) = ∑ j, e (B j v) * f (h * k j) := by
  have e1 : ∀ j, f (h * k j) = ∑ i, f (k i) * LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) := by
    intro j
    rw [hf _ (hmul _ hh _ (hk j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ _ hh _ (hk j), LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have e2 : ∀ i, e (B i (ρ h v)) = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) * e (B j v) := by
    intro i
    have := congrArg (fun L : H →ₗ[ℂ] H => e (L v)) (hB i h hh)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul] at this
    exact this
  simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.DefiniteDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.KFinDecomp

variable {D : D7}

def Cls (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) : Set (GA D N.V → ℂ) :=
  {f | GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N f ∧ ∀ k ∈ U, k ∈ GfC N.V → ∀ g, f (g * k) = f g}

structure IsOpAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) (A : (GA D N.V → ℂ) → (GA D N.V → ℂ)) : Prop where

  cont : ∀ f, Continuous f → Continuous (A f)

  add : ∀ f f', Continuous f → Continuous f' → A (f + f') = A f + A f'

  smul : ∀ (c : ℂ) f, Continuous f → A (c • f) = c • A f

  maps : ∀ f ∈ 𝒞, A f ∈ 𝒞

  keep : ∀ τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A f)

  tr : ∀ τ', τ' ≠ τ → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'), ∀ f ∈ 𝒞,
    A (rTr N.V (atTau θ N.V τ' g) f) = rTr N.V (atTau θ N.V τ' g) (A f)

  lie : ∀ τ', τ' ≠ τ → ∀ X ∈ lieAt N.V τ', ∀ f ∈ 𝒞, A (Rder θ N.V τ' X f) = Rder θ N.V τ' X (A f)

def DecompAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : Prop :=
  ∃ (m : ℕ) (a : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ)
    (A : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → (GA D N.V → ℂ) → (GA D N.V → ℂ)),
    (∀ j u, IsOpAt θ N 𝒞 Ty τ (A j u)) ∧
    (∀ j, ∀ f ∈ 𝒞, (∀ u u', A j (u + u') f = A j u f + A j u' f) ∧ (∀ (c : ℂ) u, A j (c • u) f = c • A j u f) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = N.M.rep τ k u → A j w f = rTr N.V (atTau θ N.V τ k) (A j u f)) ∧
      (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = dRep (N.M.rep τ) X u → A j w f = Rder θ N.V τ X (A j u f))) ∧
    ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A j (a j) f

theorem isOpAt_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : IsOpAt θ N 𝒞 Ty τ id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩

end GlobalTheory.KFinDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thF_shift_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : κ' ∈ GfC (Wc D i)) (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = c⁻¹ • R.vP i t)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P :=
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t)
      κ hκ.1 κ' hκ' c⁻¹ hv
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hR.thP.ωP i t)
    (R.ptP i t P) (hR.thP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hR.models.νV i t).1.1 (R.fdV i t)
      (hR.models.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hR.models.HV i t y)
    (fun h => (congrFun ((R.extV i t).map_smul c y').symm h).trans
      (extV_shift R hR.models.cV i t κ hκ.1 c hc0 y y' hy h))
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thG_of_value_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g : G)
    (y y' : (R.HV i t).H) (v : (R.MW i (sg0 D A)).Vec) (hv : ∀ τ, ‖(v τ : (R.MW i (sg0 D A)).H τ)‖ = 1)
    (hact : R.thF i t y' v = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y v)) :
    R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  have hinj := GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).H (R.HW i (sg0 D A)).e _
    (R.νW i) (R.fdW i) (hR.models.HW i (sg0 D A)).2.2 v hv
  have e1 : (R.HW i (sg0 D A)).e (R.thG i t y') v = R.eWf i (sg0 D A) (R.thF i t y' v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y')
  have e2 : (R.HW i (sg0 D A)).e (R.thG i t y) v = R.eWf i (sg0 D A) (R.thF i t y v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y)
  have e3 : (R.HW i (sg0 D A)).e (R.gW i (sg0 D A) g (R.thG i t y)) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i (sg0 D A)).e (R.thG i t y) v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.models.gW i (sg0 D A) g (R.thG i t y))
  have e4 := (GlobalTheory.ProjComm.proj_comm R hR.lev hR.grp.record).2 i (sg0 D A) g _ (thF_type R hR.thP.thF_mem i t y v)
  exact hinj (e1.trans ((congrArg (R.eWf i (sg0 D A)) hact).trans (e4.trans
    ((congrArg (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) e2.symm).trans e3.symm))))

theorem thG_intertwines_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t g κ hκ y y' hy
  refine (Classical.em (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ')).elim
    (fun hl => hl.elim fun κ' hκ' => (hR.thP.ioP i t).2.2.elim fun v hv => hv.elim fun _ hw => ?_)
    (fun hl => (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).trans
      (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).symm)
  exact thG_of_value_core R F hR i t g y y' (fun ρ => v ρ) hw.1 (funext fun x =>
    (thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)
      (levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ)
      (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (thF_type R hR.thP.thF_mem i t y _) x).symm)

end GlobalTheory.ThetaProjEquiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLiftsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaProjection_intertwines_levelLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  first | exact @GlobalTheory.ThetaProjEquiv.thG_intertwines_core | exact GlobalTheory.ThetaProjEquiv.thG_intertwines_core | (intros; apply GlobalTheory.ThetaProjEquiv.thG_intertwines_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}


open Classical in
def cutPart (a : AE D) (V : HSp D) (g : GA D V) : GA D V :=
  if h : a * a = a ∧ cA D a = a then ⟨piece h.1 g.1, piece_mem _ _ h.1 h.2 g.2⟩ else g

theorem mt_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) = a • Formalism.L2.Theta.mt V g + (1 - a) • (1 : Matrix _ _ (AE D)) := by
  have e : cutPart a V g = ⟨piece h g.1, piece_mem _ _ h hc g.2⟩ := dif_pos ⟨h, hc⟩
  rw [e]
  rfl

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

theorem idem_conj_sum {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  have h1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  refine ⟨by linear_combination he + h1 + 2 * hc, ?_⟩
  rw [RingHom.map_add (f := _), GlobalTheory.SplitOnto.cA_cA, add_comm]

theorem idem_compl {f : AE D} (hf : f * f = f ∧ cA D f = f) : (1 - f) * (1 - f) = 1 - f ∧ cA D (1 - f) = 1 - f := by
  refine ⟨by linear_combination hf.1, ?_⟩
  rw [RingHom.map_sub, RingHom.map_one, hf.2]

theorem cutPart_mul {f : AE D} (hf : f * f = f ∧ cA D f = f) (V : HSp D) (g : GA D V) :
    g = cutPart f V g * cutPart (1 - f) V g := by
  have h2 := idem_compl hf
  refine GlobalTheory.IdemSupport.mt_inj V ?_
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutPart hf.1 hf.2, mt_cutPart h2.1 h2.2, sub_sub_cancel]
  exact (mix_split hf.1 rfl rfl).symm

theorem suppAt_cutPart {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    SuppAt e V (cutPart (e + cA D e) V g) := by
  have hf := idem_conj_sum he hc
  exact (supp_iff _ _).2 (smul_mix hf.1 (mt_cutPart hf.1 hf.2 V g))

theorem smul_mt_cutPart_compl {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    e • Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hf := idem_conj_sum he hc
  have h2 := idem_compl hf
  rw [mt_cutPart h2.1 h2.2, sub_sub_cancel, smul_add, smul_smul, smul_smul]
  have k1 : e * (1 - (e + cA D e)) = 0 := by linear_combination -he - hc
  have k2 : e * (e + cA D e) = e := by linear_combination he + hc
  rw [k1, k2, zero_smul, zero_add]

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem actO_cutPart_compl {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (g : GA D S) {z : WO S T}
    (hz : IsHalf e z) : actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹ z = z := by
  have hz' : e • z = z := Matrix.ext fun i j => hz i j
  unfold actO
  rw [inv_inv, inv_one, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
  conv_lhs => rw [← hz']
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_mt_cutPart_compl he hc, Matrix.mul_smul, Matrix.mul_one, hz']

theorem halfInd_cutPart {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (g : GA D S) (x : WO S T) :
    halfInd e Λ (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) = halfInd e Λ (actO S T g⁻¹ 1⁻¹ x) := by
  have hf := idem_conj_sum he hc
  have hg : g = cutPart (e + cA D e) S g * cutPart (1 - (e + cA D e)) S g := cutPart_mul hf S g
  have key : actO S T g⁻¹ 1⁻¹ x = actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹
      (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, ← mul_inv_rev, ← hg, inv_one, mul_one]
  rw [key]
  by_cases hy : IsHalf e (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x)
  · rw [actO_cutPart_compl he hc g hy]
  · unfold halfInd
    rw [if_neg fun h => hy h.2, if_neg fun h => hy (GlobalTheory.ThetaMove.isHalf_of_act _ _ h.2)]

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCommutation

theorem exists_fin_part {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = q := by
  obtain ⟨h, rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
  refine ⟨k, hk, Subtype.ext ?_⟩
  show finHom V k = finHom V (a * k)
  rw [map_mul, show finHom V a = 1 from ha, one_mul]

theorem finiteGroupLevelAction_eq_inv_smul_translate {H W : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup H} (ch : Q →* ℂˣ)
    (q : Q) (k : H) (hk : k = q) (c : ℂ) (hc : c = ch q) (f : H → W) (h : H) :
    Bridge.g0Act ch q f h = c⁻¹ • f (h * k) := by
  rw [hk, hc, Bridge.g0Act, Units.val_inv_eq_inv_val]

theorem ch_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem exists_adelic_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) (g0 : G0 L.Pg L.r) (hq : rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) = g0)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    ∃ k, IsLevelLift V β L g0 k ∧ ∀ (f : Bridge.Gf V → W) h,
      Bridge.g0Act (levEnv V β L).ch q f h = (levChi V β (flagL L) k)⁻¹ • f (h * (finHom V).rangeRestrict k) := by
  obtain ⟨k, hk, e⟩ := exists_fin_part V q.1
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) :=
    congrArg (fun x : Bridge.Gf V => Formalism.UG.bc (swapAE D) x.1) e
  refine ⟨k, ⟨hk, ?_, ?_⟩, finiteGroupLevelAction_eq_inv_smul_translate _ q _ e _ ?_⟩
  · rw [e1]; exact q.2.1
  · rw [e1]; exact hq
  · exact congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq V β L q).symm)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem algW_apply (i : Fin D.R.m) (c : G → ℂ) (U : MMap (R.MW i (sg0 D A))) :
    algW R i c U = ∑ g, c g • FWT.actW R i (sg0 D A) g U := by
  refine MultilinearMap.ext fun v => ?_
  show (∑ g, c g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (U v) = _
  rw [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem map_comb {G H X Y : Type} [Fintype G] [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (Θ : H →ₗ[ℂ] Y) (c : G → ℂ) (a : G → X) (b : G → Y) (y : H)
    (hy : e y = ∑ g, c g • a g) (h1 : ∀ g, ∃ z, e z = a g) (h2 : ∀ g z, e z = a g → Θ z = b g) :
    Θ y = ∑ g, c g • b g := by
  choose z hz using h1
  have h3 : y = ∑ g, c g • z g := he (by simp only [hy, map_sum, map_smul, hz])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h3, map_sum, map_smul, h2 _ _ (hz _)]

end GlobalTheory.ThetaCommutation

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRows
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows.Good

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem princGL_le_princAt (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {I : Ideal (𝓞 E)} {PP : Pl E} (h : I ≤ PP.asIdeal) :
    GlobalTheory.Grid.princGL β I ≤ princAt β PP := by
  intro x hx
  obtain ⟨y, rfl, hy⟩ := GlobalTheory.Grid.mem_princGL.1 (GlobalTheory.Grid.princGL_mono β h hx)
  refine mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  have h0 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hy i j), map_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem congLev_le_Kg [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ) {I : Ideal (𝓞 E)} {T : Finset (Pl E)}
    (h : ∀ PP ∈ T, I ≤ PP.asIdeal) : congLev hc J Λ I ≤ Kg hc J β T := by
  rw [← GlobalTheory.ColMeas.princ_eq_congLev hc J hfr I]
  rintro x ⟨h1, h2⟩
  refine ⟨⟨h1, ?_⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => princGL_le_princAt β (h PP hP) h2⟩
  obtain ⟨y, e, -⟩ := GlobalTheory.Grid.mem_princGL.1 h2
  exact ⟨y, e⟩

end General

variable {D : D7} {T : Type}

theorem g_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem levRow_sub {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) :
    (levRow L : Set (GA D (Yc D 0))) ⊆ levS _ (L.βY 0) (L.dat0 L.triv) := by
  rintro k ⟨hk1, hk2⟩
  obtain ⟨c, hfr, -⟩ := hL.βY 0 (by have := D.R.two_le_m; omega)
  refine ⟨hk1, Kg_le_lev (T := L.Pg) (D := L.dat0 L.triv) subset_rfl (Finset.empty_subset _)
    (congLev_le_Kg _ _ hfr (fun PP hP => ?_) hk2)⟩
  obtain ⟨l, hl⟩ := (hL.Pg PP).1 hP
  have hg := g_mem hl
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
  fin_cases l
  · exact Ideal.mul_mem_right _ _ hg
  · exact Ideal.mul_mem_left _ _ hg

theorem principalRowLevelCharacter_trivial (L : LevCh D T) (k : GA D (Yc D 0)) : Lev.levChi _ (L.βY 0) (L.dat0 L.triv) k = 1 := by
  have h : levFn (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k) = 1 := by
    have h1 : ext1 (L.dat0 L.triv).P.H (L.dat0 L.triv).P.chi (rTup (L.βY 0) (L.dat0 L.triv) (Lev.finE (Yc D 0) k)) = 1 :=
      Lev.subgroupCharExtension_one_apply _ _
    unfold levFn
    rw [h1]
    simp [LevCh.dat0, Lev.datY]
  unfold Lev.levChi
  rw [h, Units.val_one]

end GlobalTheory.SepRows.Good

theorem GlobalTheory.SepRows.goodRows : GoodRows := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R hL t ht
  rw [mem_multT, LinearEquiv.symm_apply_apply]
  refine Submodule.span_mono (fun U hU => ?_) (goodPart_le _ _ _ _ _ ht)
  exact ⟨hU.aut, hU.cusp, fun v k hk g => by
    rw [hU.lev v k (Good.levRow_sub hL hk) g, Good.principalRowLevelCharacter_trivial]; rfl, hU.equiv, hU.cont⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodRows_principalLevel_are_rows : GoodRows := by
  first | exact @GlobalTheory.SepRows.goodRows | exact GlobalTheory.SepRows.goodRows | (intros; apply GlobalTheory.SepRows.goodRows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemCuspFormsIffAutomorphicCompact
noncomputable section

namespace GlobalTheory.Core.Rk.DownCompare

open scoped ComplexConjugate Matrix ComplexOrder Pointwise TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff)
open GlobalTheory.Core.Rk.IP (WRep up wcoef rcoef)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattices

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Lattices

variable {D : D7}

def latIn (V : HSp D) (L : Lat V) : Submodule (𝓞 D.host.E) V.V :=
  L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latIn {V : HSp D} {L : Lat V} {x : V.V} : x ∈ latIn V L ↔ V.frame.equivFun x ∈ L :=
  ⟨by rintro ⟨y, hy, rfl⟩; exact (V.frame.equivFun.apply_symm_apply y).symm ▸ hy, fun h => ⟨_, h, V.frame.equivFun.symm_apply_apply x⟩⟩

theorem hT_eq (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.equivFun x i) * V.gram i j * V.frame.equivFun y j := by
  conv_lhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, HSpace.gram,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latIn_lat {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Submodule.IsLattice D.host.E (latIn V L) :=
  Submodule.IsLattice.of_fg D.host.E (h.1.fg.map _)

theorem latIn_unimod {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (latIn V L) := by
  ext y
  rw [mem_latIn, h.2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]
  constructor
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.2 (by rwa [LinearEquiv.apply_symm_apply] : V.frame.equivFun (V.frame.equivFun.symm x) ∈ L))
    exact ⟨b, by rw [hT_eq, LinearEquiv.apply_symm_apply] at hb; exact hb⟩
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.1 hx)
    exact ⟨b, by rw [hT_eq]; exact hb⟩

def reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D :=
  { V with sig := s, L0 := latIn V L, standardTuple_isLattice := latIn_lat h, baseLattice_isUnimodular := latIn_unimod h }

theorem frameLat_reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) :
    frameLat (reset V L h s) = L := by
  ext x
  exact (mem_latIn (V := V) (L := L) (x := V.frame.equivFun.symm x)).trans (by rw [V.frame.equivFun.apply_symm_apply x]; rfl)

section Transport

variable {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {LA : Lat A} {LW : Lat W} (hA : IsSelfDualC A LA) (hW : IsSelfDualC W LW)
  (sA sW : (D.host.E →+* ℂ) → ℕ × ℕ)

end Transport

end GlobalTheory.Core.Rk.DownCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.ReLatPf

variable {D : D7}

theorem theta_relat (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B) (f : WO A B → ℂ) :
    IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f := ⟨fun h => ⟨h.1,h.2,h.3,h.4⟩, fun h => ⟨h.1,h.2,h.3,h.4⟩⟩

theorem aut_relat (V : HSp D) (r : ReLat V) (θ : InfFam D) (φ : GA D V → ℂ) : IsAutFunSm θ r.sp φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem reLatLaw_holds : ∀ D : D7, ReLatLaw D := by
  intro D
  refine ⟨fun V Λ h => ⟨⟨_, GlobalTheory.Core.Rk.DownCompare.latIn_lat h, GlobalTheory.Core.Rk.DownCompare.latIn_unimod h⟩,
      GlobalTheory.Core.Rk.DownCompare.frameLat_reset V Λ h V.sig⟩,
    fun V r θ S M J => ⟨?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩, fun ψ A B r r' => ⟨theta_relat ψ A B r r', fun χS χT ω => ?_⟩⟩
  · have e : (Mult θ (r.mod M) J 1 : Submodule ℂ (MMap M)) = Mult θ M J 1 := by
      unfold Mult
      congr 1
      ext T
      exact ⟨fun h => ⟨fun v => (aut_relat V r θ _).1 (h.1 v), h.2, h.3, h.4, h.5⟩,
        fun h => ⟨fun v => (aut_relat V r θ _).2 (h.1 v), h.2, h.3, h.4, h.5⟩⟩
    exact congrArg (Submodule.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] _).toLinearMap) e
  · have t := theta_relat ψ A B r r'
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).1 (h.6 p f ((t _).2 hf)),
        fun g k w f hf => h.7 g k w f ((t _).2 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).2 hf),
        fun f hf => h.9 f ((t _).2 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).2 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).1 hf)) f ((t _).2 hf)⟩⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).2 (h.6 p f ((t _).1 hf)),
        fun g k w f hf => h.7 g k w f ((t _).1 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).1 hf),
        fun f hf => h.9 f ((t _).1 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).1 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).2 hf)) f ((t _).1 hf)⟩⟩⟩

end GlobalTheory.ReLatPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_changeOfLattice_laws : ∀ D : D7, ReLatLaw D := by
  first | exact @GlobalTheory.ReLatPf.reLatLaw_holds | exact GlobalTheory.ReLatPf.reLatLaw_holds | (intros; apply GlobalTheory.ReLatPf.reLatLaw_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPolyInj

open GlobalTheory.FockVecInj GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem pureTensorO_injective_of_on (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sV BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pV pW : D.what₂.Tau → ℕ)
    (hBV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ))
    (hBW : ∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f)
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (s τ)) f) (hf0 : f ≠ 0) :
    Function.Injective (pureTensorO ψ θ V W sV s BV BW f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  choose ε hε hG hs using hBV
  choose ε' hε' hG' hs' using hBW
  have sq : ∀ τ a, (ε τ a : ℂ) * ε τ a = 1 := fun τ a => by
    rcases hε τ a with h | h <;> simp [h.1]
  have sq' : ∀ τ a, (ε' τ a : ℂ) * ε' τ a = 1 := fun τ a => by
    rcases hε' τ a with h | h <;> simp [h.1]
  have hdet : ∀ τ, IsUnit (BV τ).det := fun τ => by
    have e : (diagonal (fun a => (ε τ a : ℂ)) * ((BV τ)ᴴ * gramAt D V τ)) * BV τ = 1 := by
      rw [Matrix.mul_assoc, hG, Matrix.diagonal_mul_diagonal]
      simp only [sq, Matrix.diagonal_one]
    exact Matrix.isUnit_det_of_left_inverse e
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g = hD (iotaW σ W V) (piW θ W V) (omO V W)
      (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) g := fun τ z g => by
    rw [← pi_lineAt hθ]
    exact dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  let M : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {g | Sm (iotaW σ W V) g}
      add_mem' := fun ha hb w => (ha w).add (hb w)
      zero_mem' := fun w => contDiff_const
      smul_mem' := fun c g hg w => contDiff_const.mul (hg w) }
  have hform := fun g hg u w => hD_eq_fderiv (iotaW σ W V) (piW θ W V) (omO V W) g hg u w
  obtain ⟨Dop, hD1, -⟩ := exists_heisenberg_operators _ _ (iotaW σ W V) (piW θ W V) (omO V W) (h.pi_iota W V) hform M
    (fun _ hg => hg) fun u g hg => (hD_formula_smooth _ _ _ _ _ (h.pi_iota W V) g hg u).2
  have sk : ∀ u v, omO V W v u = -omO V W u v := fun u v => by
    have h1 := omO_self h (S := V) (T := W) (u + v)
    simp only [LinearMap.map_add (f := _), LinearMap.add_apply, omO_self h] at h1
    linarith
  have hcomm : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + (-(2 * Real.pi * I) * (omO V W u v : ℝ)) • g :=
    fun u v g => by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hD1, hD1, hD1, hD1]
    exact eq_add_of_sub_eq' (heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota W V) hform sk g g.2 u v)
  let η : FVar D W.rank V.rank → ℝ := fun k => ε' k.1 k.2.1 * ε k.1 k.2.2
  have hη : ∀ k, η k = 1 ∨ η k = -1 := fun k => by
    rcases hε k.1 k.2.2 with h | h <;> rcases hε' k.1 k.2.1 with h' | h' <;> simp [η, h.1, h'.1]
  let u : ℂ → FVar D W.rank V.rank → RW W V := fun c k =>
    (Pi.single k.1 (c • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)
  have hom : ∀ c c' k l, omO V W (u c k) (u c' l) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * conj c' * η k)).re else 0 := by
    rintro c c' ⟨τ, i, j⟩ ⟨τ', k, l⟩
    refine (omO_single V W τ τ' _ _).trans ?_
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, trace_unitMap (sq τ) (hG τ) (hG' τ)]
      by_cases hk : i = k ∧ j = l
      · rw [if_pos hk, if_pos (by rw [hk.1, hk.2])]
        simp only [η, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
        rfl
      · rw [if_neg hk, if_neg (by simpa using hk)]
        simp
    · rw [if_neg hτ, if_neg fun hh => hτ (congrArg Prod.fst hh)]
  have hJ : ∀ k : FVar D W.rank V.rank, cplxO (sV k.1) (s k.1) (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) =
      (I * η k) • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2 := fun k => by
    rw [cplxO_unitMap (hdet _) (hs _) (hs' _)]
    simp only [η, Complex.ofReal_mul]
  have h1 : ∀ k : FVar D W.rank V.rank, u 1 k = (Pi.single k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) :
      D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := fun k => congrArg (Pi.single k.1) (one_smul _ _)
  have hξ : ∀ τ, tauE D τ D.host.xi0 ≠ 0 := fun τ => (_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hre := fun τ => GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) τ
  have him : ∀ τ, (tauE D τ D.host.xi0).im ≠ 0 := fun τ hh => hξ τ (Complex.ext (hre τ) hh)
  have hsc : ∀ τ, (fockScale D τ : ℂ) ≠ 0 := fun τ => by
    have := norm_pos_iff.2 (hξ τ)
    have h2 : 0 < fockScale D τ := by unfold fockScale; positivity
    exact Complex.ofReal_ne_zero.2 h2.ne'
  refine injective_of_canonicalCommutation M _ (fun k => (fockScale D k.1 : ℂ)⁻¹ • (Dop (u 1 k) - I • Dop (u (I * η k) k)))
    (fun k => Dop (u 1 k) + I • Dop (u (I * η k) k))
    (fun k => (fockScale D k.1 : ℂ)⁻¹ * (-8 * Real.pi * (tauE D k.1 D.host.xi0).im)) (fun k g => ?_) (fun k l g => ?_)
    (fun k l g => ?_) (fun k => ?_) ⟨f, theta_sm h hf⟩ (fun k => ?_) (fun hh => hf0 (congrArg Subtype.val hh))
  · simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      hD1, hE, hJ]
    rw [h1]
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ _ _ g).1]
    refine add_eq_left.2 (smul_eq_zero.2 (Or.inl ?_))
    simp only [hom]
    split_ifs with hh
    · subst hh
      rcases hη k with e | e <;> simp [e, hre]
    · simp
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ 0 _ g).2]
    refine congrArg (fun c : ℂ => _ + c • g) ?_
    by_cases hh : k = l
    · subst hh
      simp only [hom, if_true]
      refine congrArg _ ?_
      rcases hη k with e | e <;> simp [e, hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [hom, hh]
  · exact mul_ne_zero (inv_ne_zero (hsc _)) (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) (Complex.ofReal_ne_zero.2 (him _)))
  · apply Subtype.ext
    have := hvac k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2)
    simp only [annih, hE, hJ] at this
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hD1]
    rw [h1]
    exact this

theorem isONBasis_one {V : HSp D} (hV : V.gram = 1) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) 1 1 V.rank := by
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.isLt⟩, ?_, ?_⟩ <;>
    simp [hg, Matrix.diagonal_one]

theorem fvec_injective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  intro D S T C B hB f hf hvac hf0
  have hT := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.1
  exact pureTensorO_injective_of_on C.ψ C.θ S T C.std C.inf (fun _ => 1) (fun _ => 1) (C.sB B) B
    (fun _ => S.rank) (fun _ => C.X.p0) (isONBasis_one C.m.gS) (fun τ => (hT τ).2) f hf hvac hf0

end GlobalTheory.FockPolyInj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_injective_nonzeroVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  first | exact @GlobalTheory.FockPolyInj.fvec_injective | exact GlobalTheory.FockPolyInj.fvec_injective | (intros; apply GlobalTheory.FockPolyInj.fvec_injective <;> assumption)
end
end
