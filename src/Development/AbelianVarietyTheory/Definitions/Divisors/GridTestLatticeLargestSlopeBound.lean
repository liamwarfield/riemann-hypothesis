module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.IsCyclotomicExtensionFourSlopeModelField
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder Kronecker MatrixOrder

noncomputable section

namespace GlobalTheory.TestLat.SlopeModel

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.SlopeModel.sumGram_posDef (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) [Finite C]
    (G : ι → Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ) (hG : ∀ τ, ((G τ).map φ).PosDef) :
    ((_root_.GlobalTheory.TestLat.sumGram lam e G).map φ).PosDef := by
  classical
  choose B hB hBT using fun τ => _root_.Formalism.L2.DIV.ps_factor (hG τ).transpose
  obtain ⟨D, hD⟩ : ∃ D : ℂ, D = ∏ τ, ((G τ).map φ).det ^ (lam τ).detShift := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    exact Finset.prod_pos fun τ _ => zpow_pos (hG τ).det_pos _
  have hDstar : star D = D := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hDpos).2.symm
  obtain ⟨w, hw⟩ : ∃ w : _root_.Formalism.L2.DIV.VVIdx lam → MvPolynomial (ι × Fin n × Fin n) ℂ,
      w = fun i => _root_.Formalism.GradedWeylDivisibility.blockAct ℂ B (MvPolynomial.map φ (_root_.Formalism.L2.DIV.bVVfun K lam i)) := ⟨_, rfl⟩
  have hcoef : ∀ i (m : ι × Fin n × Fin n →₀ ℕ),
      φ (star (AddMonoidAlgebra.coeff (_root_.Formalism.L2.DIV.bVVfun K lam i) m)) =
        star (φ (AddMonoidAlgebra.coeff (_root_.Formalism.L2.DIV.bVVfun K lam i) m)) := by
    intro i m
    obtain ⟨P, hP⟩ := _root_.Formalism.L2.DIV.bVVfun_int K lam i
    rw [hP, MvPolynomial.coeff_map]
    simp
  have hentry : ∀ a b, (_root_.GlobalTheory.TestLat.sumGram lam e G).map φ a b =
      if (e a).1 = (e b).1 then D * _root_.Formalism.L2.Col.nfL lam (w (e a).2) (w (e b).2) else 0 := by
    intro a b
    simp only [Matrix.map_apply, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply]
    split_ifs
    · rw [_root_.Formalism.L2.DIV.pairK_apply, _root_.Formalism.L2.DIV.bVV_coe, _root_.Formalism.L2.DIV.bVV_coe, _root_.Formalism.L2.Col.map_pairP φ lam G B hBT _ _ (hcoef _), _root_.Formalism.L2.Col.nfL_apply, hD, hw]
    · exact map_zero φ
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro a b
    rw [hentry, hentry]
    by_cases h : (e a).1 = (e b).1
    · rw [if_pos h.symm, if_pos h, star_mul', hDstar, _root_.Formalism.L2.DIV.ps_nfL_symm]
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  intro x hx
  rcases isEmpty_or_nonempty C with hC | hC
  · exact absurd (funext fun a => (hC.false (e a).1).elim) hx
  obtain ⟨c0⟩ := hC
  haveI : Finite (_root_.Formalism.L2.DIV.VVIdx lam) :=
    Finite.of_injective (fun i => e.symm (c0, i)) (fun i j h => by simpa using h)
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite (_root_.Formalism.L2.DIV.VVIdx lam)
  have hinv : (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (B τ)⁻¹)).comp (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) := by
    rw [_root_.Formalism.L2.DIV.blockAct_comp]
    have h1 : (fun τ => B τ * (B τ)⁻¹) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) :=
      funext fun τ => Matrix.mul_nonsing_inv _ (hB τ)
    rw [h1, _root_.Formalism.L2.DIV.blockAct_one]
  have hUinj : Function.Injective (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B :
      MvPolynomial (ι × Fin n × Fin n) ℂ → MvPolynomial (ι × Fin n × Fin n) ℂ) := by
    intro p q hpq
    have h2 := congrArg (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (B τ)⁻¹)) hpq
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at h2
    simpa using h2
  have hli : LinearIndependent ℂ w := by
    have h3 := _root_.Formalism.L2.Col.linearIndependent_map φ (_root_.Formalism.L2.DIV.bVVfun K lam) (_root_.Formalism.L2.DIV.bVVfun_spec K lam).1
    rw [hw]
    exact h3.map' (_root_.Formalism.GradedWeylDivisibility.blockAct ℂ B).toLinearMap (LinearMap.ker_eq_bot.mpr hUinj)
  obtain ⟨W, hW⟩ : ∃ W : C → MvPolynomial (ι × Fin n × Fin n) ℂ,
      W = fun c => ∑ i, x (e.symm (c, i)) • w i := ⟨_, rfl⟩
  have key : star x ⬝ᵥ ((_root_.GlobalTheory.TestLat.sumGram lam e G).map φ) *ᵥ x =
      D * ∑ c, _root_.Formalism.L2.Col.nfL lam (W c) (W c) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, hentry]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply]
    conv_lhs =>
      enter [2, c, 2, i, 2]
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (γ := _root_.Formalism.L2.DIV.VVIdx lam) (f := fun i j => D * _)]
    simp only [Complex.star_def, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  refine mul_pos hDpos (Finset.sum_pos' (fun c _ => ?_) ?_)
  · by_cases hc : W c = 0
    · rw [hc]
      simp
    · exact (_root_.Formalism.L2.DIV.ps_nfL_pos lam _ hc).le
  · obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    refine ⟨(e a).1, Finset.mem_univ _, _root_.Formalism.L2.DIV.ps_nfL_pos lam _ ?_⟩
    intro h0
    rw [hW] at h0
    have h4 := Fintype.linearIndependent_iff.mp hli _ h0 (e a).2
    simp at h4
    exact ha h4

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in
private lemma exists_isMetric_of_posDef_map (H : Matrix (Fin N) (Fin N) K)
    (hH : ∀ φ : K →+* ℂ, (H.map φ).PosDef) : ∃ X, _root_.GlobalTheory.TestLat.IsMetric H X := by
  choose B hB hT using fun v : InfinitePlace K => _root_.Formalism.L2.DIV.ps_factor (hH v.embedding)
  have hu : ∀ v, IsUnit ((B v)ᴴ).det := fun v => by
    rw [Matrix.det_conjTranspose]
    exact (hB v).star
  refine ⟨fun v => ((B v)ᴴ)⁻¹, fun v => ⟨Matrix.isUnit_nonsing_inv_det _ (hu v), ?_⟩⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ (hu v), Matrix.conjTranspose_conjTranspose, ← hT]

open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in
theorem _root_.GlobalTheory.TestLat.SlopeModel.exists_isMetric (H : Matrix (Fin N) (Fin N) K)
    (hH : ∀ φ : K →+* ℂ, (H.map φ).PosDef) :
    (∃ X, _root_.GlobalTheory.TestLat.IsMetric H X) ∧ ∃ X, _root_.GlobalTheory.TestLat.IsMetric (H⁻¹)ᵀ X := by
  refine ⟨exists_isMetric_of_posDef_map H hH, exists_isMetric_of_posDef_map _ fun φ => ?_⟩
  rw [Matrix.transpose_map, _root_.Formalism.L2.Col.map_inv_matrix]
  exact (hH φ).inv.transpose


open NumberField in
open scoped Matrix ComplexOrder in
open scoped Kronecker MatrixOrder in
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ}
  {C : Type} in
omit [StarRing K] in
theorem _root_.GlobalTheory.TestLat.SlopeModel.nonempty_idx (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have h := _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (K := ℚ) (fun _ : ι => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ)
    lam (Rat.castHom ℂ) ⟨fun _ => 1, fun _ => by simp⟩
  have hne : _root_.Formalism.L2.Col.extV ℚ lam ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  haveI : Nontrivial ↥(_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

end GlobalTheory.TestLat.SlopeModel
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG
open GlobalTheory.ChiGrid GlobalTheory.TestLat
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Delta

variable {Γ A K M : Type} [Group Γ] [Group A] [Field K] [AddCommGroup M] [Module K M]
  (ι : Γ →* A) (U : Subgroup A) (ρ : Γ →* Module.End K M)


open Classical in
def deltaForm (x : A) (v : M) (g : A) : M := ∑ᶠ γ : Γ, if x⁻¹ * ((ι γ)⁻¹ * g) ∈ U then ρ γ v else 0

theorem deltaForm_left (x : A) (v : M) (δ : Γ) (g : A) :
    deltaForm ι U ρ x v (ι δ * g) = ρ δ (deltaForm ι U ρ x v g) := by
  classical
  have hinj : Function.Injective (ρ δ) := Function.LeftInverse.injective (g := ρ δ⁻¹) fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  unfold deltaForm
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  refine Eq.trans (finsum_congr fun γ => ?_) ((ρ δ).toAddMonoidHom.map_finsum_of_injective hinj _).symm
  simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, LinearMap.toAddMonoidHom_coe]
  split_ifs <;> simp

theorem deltaForm_right (x : A) (v : M) (g : A) {u : A} (hu : u ∈ U) :
    deltaForm ι U ρ x v (g * u) = deltaForm ι U ρ x v g := by
  unfold deltaForm
  refine finsum_congr fun γ => ?_
  have : x⁻¹ * ((ι γ)⁻¹ * (g * u)) ∈ U ↔ x⁻¹ * ((ι γ)⁻¹ * g) ∈ U := by
    rw [← mul_assoc _ g, ← mul_assoc x⁻¹, U.mul_mem_cancel_right hu]
  exact propext this ▸ rfl

theorem deltaForm_self (x : A) (v : M) (h : ∀ γ, x⁻¹ * ι γ * x ∈ U → γ = 1) : deltaForm ι U ρ x v x = v := by
  unfold deltaForm
  rw [finsum_eq_single _ 1 fun γ hγ => if_neg fun hm => hγ (inv_eq_one.1 (h γ⁻¹ (by rwa [map_inv, mul_assoc])))]
  simp [U.one_mem]

theorem deltaForm_eq_zero (x : A) (v : M) (g : A) (h : ∀ γ, ∀ u ∈ U, g ≠ ι γ * x * u) : deltaForm ι U ρ x v g = 0 := by
  unfold deltaForm
  refine finsum_eq_zero_of_forall_eq_zero fun γ => if_neg fun hm => h γ _ hm ?_
  simp [mul_assoc]

end Delta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GlobalTheory.ChiGrid.GridData L sc)

abbrev Xp : HSp D := G.V (.top 0)

theorem isV_Xp : (G.node (.top 0)).IsV (rankP D D.R.m) 0 := by
  have := G.sp.P_is D.R.m le_rfl
  rwa [Nat.sub_self] at this

theorem rank_Xp : (Xp G).rank = rankP D D.R.m := (isV_Xp G).rank

def LaP (τ : D.what₂.Tau) : DomWeight (Xp G).rank where
  w a := (La D sc.cGap τ).w (Fin.cast (rank_Xp G) a)
  anti _ _ h := (La D sc.cGap τ).anti h


variable (D) in
abbrev emb : D.what₂.Tau → D.host.E →+* D.what₂.LL := labLL D

abbrev WtSp : Type := VV D.what₂.LL (LaP G)

abbrev GLf : Type := GL (Fin (Xp G).rank) (Formalism.IndefR.Lev.EAf D)

abbrev TestIx : Type := G.Datum × G.ClPlus

structure ClassReps where

  x : G.ClPlus → UA D.sp.cm (Xp G).gram

  classRepresentative_mk : ∀ c, (Quotient.mk'' (x c) : G.ClPlus) = c

instance : Inhabited (ClassReps G) := ⟨⟨rep, mk_rep⟩⟩

def latOf (g : GLf G) : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E) := CS.globLat g (G.Λ (.top 0))

abbrev wLat (Λ : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E)) : Submodule (𝓞 D.what₂.LL) (WtSp G) :=
  delAtr (emb D) (LaP G) Λ

def rhoW : UR D.sp.cm (Xp G).gram →* Module.End D.what₂.LL (WtSp G) :=
  (rhoVr (emb D) (LaP G)).comp (UR D.sp.cm (Xp G).gram).subtype

def ratIn : UR D.sp.cm (Xp G).gram →* GLf G :=
  (bc (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))).comp (UR D.sp.cm (Xp G).gram).subtype

variable {G}

def ClassReps.lat (rp : ClassReps G) (c : G.ClPlus) : Submodule (𝓞 D.host.E) (Fin (Xp G).rank → D.host.E) := latOf G (rp.x c)

def ClassReps.Neat (rp : ClassReps G) : Prop :=
  ∀ c γ, ((rp.x c : GLf G))⁻¹ * ratIn G γ * rp.x c ∈ G.Kplus → γ = 1

variable (G)

def formLat (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL) :=
  GlobalTheory.TestLat.sumLat (LaP G) e fun c => wLat G (rp.lat c.2)

def formGram {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : Matrix (Fin n) (Fin n) D.what₂.LL :=
  sumGram (LaP G) e (gramKd (emb D) (Xp G).gram)

def IsTestLat (rp : ClassReps G) (n : ℕ) (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)) : Prop :=
  IsMetric ((formGram G e)⁻¹)ᵀ X' ∧ M = dualFr (formLat G rp e)

variable {G}

def ClassReps.delta (rp : ClassReps G) (c : G.ClPlus) (v : WtSp G) : GLf G → WtSp G :=
  deltaForm (ratIn G) G.Kplus (rhoW G) (rp.x c) v

def datumOf {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) : G.Datum := (e a).1.1

def psi (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) : GLf G → WtSp G :=
  rp.delta (e a).1.2 (bVV D.what₂.LL (LaP G) (e a).2)

def scal (θ : InfFam D) (ξ : Module.Dual ℂ (VV ℂ (LaP G))) (Ψ : GLf G → WtSp G) (h : GA D (Xp G)) : ℂ :=
  ξ (rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹))
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (Formalism.IndefR.Lev.finE (Xp G) h))))

theorem psi_left (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) (γ : UR D.sp.cm (Xp G).gram)
    (g : GLf G) : psi rp e a (ratIn G γ * g) = rhoW G γ (psi rp e a g) := deltaForm_left _ _ _ _ _ _ _

theorem psi_right (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) (g : GLf G) {k : GLf G}
    (hk : k ∈ G.Kplus) : psi rp e a (g * k) = psi rp e a g := deltaForm_right _ _ _ _ _ _ hk


open Classical in
theorem ClassReps.gridClassReps_delta_apply_rep (rp : ClassReps G) (hN : rp.Neat) (c c' : G.ClPlus) (v : WtSp G) :
    rp.delta c v (rp.x c') = if c' = c then v else 0 := by
  split_ifs with h
  · subst h; exact deltaForm_self _ _ _ _ _ (hN c')
  · refine deltaForm_eq_zero _ _ _ _ _ _ fun γ u hu he => h ?_
    have hγ : ratIn G γ ∈ UA D.sp.cm (Xp G).gram := by
      have e : ratIn G γ = rp.x c' * u⁻¹ * (rp.x c : GLf G)⁻¹ := by rw [he]; group
      rw [e]
      exact mul_mem (mul_mem (rp.x c').2 (inv_mem hu.1)) (inv_mem (rp.x c).2)
    rw [← rp.classRepresentative_mk c, ← rp.classRepresentative_mk c']
    symm
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨⟨_, hγ⟩, ⟨γ.1, γ.2, rfl⟩, ⟨u, hu.1⟩, hu, Subtype.ext he⟩

variable (G)

theorem posDef_Xp (φ : D.host.E →+* ℂ) : ((Xp G).gram.map φ).PosDef := by
  have := (isV_Xp G).sigOK φ
  rw [(isV_Xp G).sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem isSelfDualE_latOf (g : UA D.sp.cm (Xp G).gram) :
    IsSelfDualE (D.sp.cm.sig : D.host.E →+* D.host.E) (Xp G).gram (latOf G g) := by
  obtain ⟨h1, h2⟩ := (isV_Xp G).sd
  have hf := Module.Finite.iff_fg.2 h1.fg
  classical
  have hspan : Submodule.span D.host.E ((G.node (.top 0)).lat : Set (Fin (Xp G).rank → D.host.E)) = ⊤ := by
    let W := Submodule.span D.host.E ((G.node (.top 0)).lat : Set (Fin (Xp G).rank → D.host.E))
    change W = ⊤
    by_contra hW
    let g : (Fin (Xp G).rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
      { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * (Xp G).gram i j * y.1 j
                            map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                            map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
        map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin (Xp G).rank → D.host.E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let v : Fin (Xp G).rank → D.host.E := fun i => star (x i)
    have hv0 : v ≠ 0 := by
      intro hv
      apply hx0
      funext i
      have hi := congrFun hv i
      simpa [v] using congrArg star hi
    have hline (r : D.host.E) : r • v ∈ (G.node (.top 0)).lat := by
      apply (h2 _).2
      intro y hy
      have hz : (∑ i, ∑ j, x i * (Xp G).gram i j * y j) = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hzy : (∑ i, ∑ j, star (y i) * (Xp G).gram i j * v j) = 0 := by
        have hg (i j : Fin (Xp G).rank) : star ((Xp G).gram i j) = (Xp G).gram j i := by
          exact (Xp G).herm.eq _ _
        have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * (Xp G).gram i j * y j) = 0 := by rw [hz, map_zero]
        simp only [map_sum, map_mul] at hs
        change (∑ i, ∑ j, star (x i) * star ((Xp G).gram i j) * star (y j)) = 0 at hs
        simp only [hg] at hs
        rw [Finset.sum_comm] at hs
        simpa [mul_comm, mul_left_comm, mul_assoc] using hs
      refine ⟨0, ?_⟩
      simp only [map_zero, Pi.smul_apply, smul_eq_mul]
      calc
        0 = r * (∑ i, ∑ j, star (y i) * (Xp G).gram i j * v j) := by rw [hzy, mul_zero]
        _ = ∑ i, ∑ j, star (y i) * (Xp G).gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      apply hv0
      funext i
      simpa using not_exists.mp hn i
    let coord := (LinearMap.proj i : (Fin (Xp G).rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
    have htop : (G.node (.top 0)).lat.map coord = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ h1.fg.map coord)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact ⟨Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ hf hspan _,
    GlobalTheory.PointLattice.globLat_selfDual D.sp.cm.sig _ _ h2 hf hspan g.1 g.2⟩

theorem star_emb (τ : D.what₂.Tau) (x : D.host.E) :
    star (emb D τ x) = emb D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  apply D.what₂.embLL.injective
  rw [D.starLL_cx]
  exact (D.sp.cm.cmUnram.2.1 (D.what₂.embLL.comp (emb D τ)) x).symm

theorem exists_isTestLat (rp : ClassReps G) (n : ℕ) (e : Fin n ≃ TestIx G × VVIdx (LaP G)) : ∃ X' M, IsTestLat G rp n e X' M := by
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  haveI : Finite (TestIx G) := Finite.of_injective (fun c => e.symm (c, i)) fun _ _ h => congrArg Prod.fst (e.symm.injective h)
  obtain ⟨X, hX⟩ := (SlopeModel.exists_isMetric (formGram G e) fun φ => SlopeModel.sumGram_posDef _ e _ φ fun τ => by
    have hP := posDef_Xp G (φ.comp (emb D τ))
    have hd : IsUnit ((Xp G).gram.map (emb D τ)).det := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
      rw [RingHom.coe_comp, ← Matrix.map_map, ← RingHom.mapMatrix_apply φ, ← RingHom.map_det, isUnit_iff_ne_zero,
        map_ne_zero] at this
      exact isUnit_iff_ne_zero.2 this
    have e : (((Xp G).gram.map (emb D τ))⁻¹).map φ = ((Xp G).gram.map (φ.comp (emb D τ)))⁻¹ := by
      symm
      apply Matrix.inv_eq_left_inv
      rw [RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [gramKd, Matrix.transpose_map, e]
    exact hP.inv.transpose).2
  exact ⟨X, _, hX, rfl⟩

variable {G}

theorem IsTestLat.gridTestLattice_largestSlope_bound (hS : SlopeE) {v₀ : InfinitePlace D.what₂.LL} (hv : Formalism.DivisionValues.IsConjAt v₀) {R : ℝ} (hR : 1 ≤ R)
    (hLa : SpreadLe (LaP G) R) {rp : ClassReps G} {n : ℕ} {e : Fin n ≃ TestIx G × VVIdx (LaP G)}
    {X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ} {M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)}
    (h : IsTestLat G rp n e X' M) :
    Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts.TestLatticeCondition n X' M (bound (Fintype.card D.what₂.Tau) (Xp G).rank R) := by
  haveI : Nonempty (TestIx G) := ⟨⟨fun _ => default, Quotient.mk'' 1⟩⟩
  rw [h.2]
  exact (hS D.host.E D.what₂.LL v₀ hv _ (fun φ x => D.sp.cm.cmUnram.2.1 φ x) _ (emb D) star_emb _ (LaP G) R hR hLa
    _ (posDef_Xp G) (TestIx G) (fun c => rp.lat c.2) (fun c => isSelfDualE_latOf G _) n e X').2.2.1 h.1

end GlobalTheory.FunObj

end
