module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanLPowSIff
open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem mem_span_l_pow_S_iff (n : ℕ) (f : S O K e) :
    f ∈ Ideal.span {(l : S O K e)} ^ n ↔
      ∀ m, ‖coeff m (f : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ m
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow,
      mul_assoc]
    exact mul_le_of_le_one_right hl.le ((mem_S.1 g.2).1 m)
  · intro h
    have hc : ∀ m, ‖coeff m (C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧))‖ * wS K e m =
        (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m (f : K⟦X⟧)‖ * wS K e m) := fun m => by
      rw [coeff_C_mul, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine ⟨⟨C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧), mem_S.2 ⟨fun m => ?_, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [hc, inv_mul_le_iff₀ hl, mul_one]
      exact h m
    · simp only [hc]
      simpa using (mem_S.1 f.2).2.const_mul (‖(l : K)‖ ^ n)⁻¹
    · rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)), map_one, one_mul]

theorem smodEq_l_pow_S_iff (n : ℕ) (f g : S O K e) :
    f ≡ g [SMOD (Ideal.span {(l : S O K e)} ^ n • ⊤ : Submodule (S O K e) (S O K e))] ↔
      ∀ m, ‖coeff m (f : K⟦X⟧) - coeff m (g : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_l_pow_S_iff]
  simp

omit [IsUltrametricDist K] in
include l in
theorem wS_pos_of_padic (m : ℕ) : 0 < wS K e m :=
  norm_pos_iff.2 (natCast_ne_zero' l (Nat.factorial_ne_zero _))

theorem isHausdorff_S : IsHausdorff (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => Subtype.ext ?_⟩
  ext m
  have h := fun n => (smodEq_l_pow_S_iff l e n f 0).1 (hf n) m
  have h0 := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (norm_l_lt_one (K := K) l)) h
  have h1 := nonpos_of_mul_nonpos_left h0 (wS_pos_of_padic l e m)
  simpa using h1

theorem isPrecomplete_S [CompleteSpace K] :
    IsPrecomplete (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => ?_⟩
  have hf' : ∀ {a b : ℕ}, a ≤ b → ∀ m, ‖coeff m (f a : K⟦X⟧) - coeff m (f b : K⟦X⟧)‖ * wS K e m ≤
      ‖(l : K)‖ ^ a := fun h => (smodEq_l_pow_S_iff l e _ _ _).1 (hf h)
  have hl0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)
  have hcau : ∀ m, CauchySeq fun n => coeff m (f n : K⟦X⟧) := fun m => by
    refine cauchySeq_of_le_tendsto_0' (fun n => ‖(l : K)‖ ^ n / wS K e m) (fun a b h => ?_)
      (by simpa using hl0.div_const (wS K e m))
    rw [dist_eq_norm, le_div_iff₀ (wS_pos_of_padic l e m)]
    exact hf' h m
  choose c hc using fun m => cauchySeq_tendsto_of_complete (hcau m)
  have hb : ∀ n m, ‖coeff m (f n : K⟦X⟧) - c m‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun n m =>
    le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm.mul_const _)
      ((eventually_ge_atTop n).mono fun b h => hf' h m)
  have hu : ∀ n m, ‖c m‖ * wS K e m ≤
      max (‖coeff m (f n : K⟦X⟧)‖ * wS K e m) (‖(l : K)‖ ^ n) := fun n m => by
    refine le_trans ?_ (max_le_max le_rfl (hb n m))
    rw [← max_mul_of_nonneg _ _ (wS_nonneg e m)]
    refine mul_le_mul_of_nonneg_right ?_ (wS_nonneg e m)
    have := IsUltrametricDist.norm_add_le_max (coeff m (f n : K⟦X⟧))
      (-(coeff m (f n : K⟦X⟧) - c m))
    rw [norm_neg] at this
    simpa using this
  have hmem : PowerSeries.mk c ∈ S O K e := by
    refine mem_S.2 ⟨fun m => ?_, ?_⟩
    · rw [coeff_mk]
      exact (hu 0 m).trans (max_le ((mem_S.1 (f 0).2).1 m) (by simp))
    · simp only [coeff_mk]
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
        ha.trans_le (mul_nonneg (norm_nonneg _) (wS_nonneg e m)), fun a ha => ?_⟩
      obtain ⟨n, hn⟩ := (hl0.eventually (gt_mem_nhds ha)).exists
      filter_upwards [(mem_S.1 (f n).2).2.eventually (gt_mem_nhds ha)] with m hm
      exact (hu n m).trans_lt (max_lt hm hn)
  refine ⟨⟨_, hmem⟩, fun n => (smodEq_l_pow_S_iff l e _ _ _).2 fun m => ?_⟩
  simpa using hb n m

end GlobalTheory.BK

namespace GlobalTheory.BK

theorem isAdicComplete_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : IsAdicComplete (Ideal.span {(l : S O K e)}) (S O K e) :=
  { toIsHausdorff := isHausdorff_S l e, toIsPrecomplete := isPrecomplete_S l e }

end GlobalTheory.BK
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

theorem act_mem_Man (g : TameGal K l e a) {v : Vec K a ι} (hv : v ∈ P.Man) : Δ.act g v ∈ P.Man :=
  Δ.act_mem_Mext g (A_le_Rpi l e) (rot_R _) hv

omit [NeZero e] in
theorem act_mem_EM (g : TameGal K l e a) {η : ℕ} {v : Vec K a ι} (hv : v ∈ P.EM η) :
    Δ.act g v ∈ P.EM η := by
  rw [mem_divE, ← act_E_pow_smul]
  exact Δ.act_mem_M g _ hv

omit [NeZero e] in
theorem act_EN (g : TameGal K l e a) (v : Vec K a ι) : Δ.act g (P.EN v) = P.EN (Δ.act g v) := by
  rw [PhiMod.EN_apply, act_E_smul, act_conn, PhiMod.EN_apply]

def actPol : Representation K (TameGal K l e a) P.Pol :=
  Δ.act.quotient P.Man fun g _ => Δ.act_mem_Man g

@[simp] theorem actPol_cls (g : TameGal K l e a) (v : Vec K a ι) :
    Δ.actPol g (P.cls v) = P.cls (Δ.act g v) := rfl

theorem actPol_Mon (g : TameGal K l e a) (y : Vec K a ι) :
    Δ.actPol g (P.Mon y) = P.Mon (Δ.act g y) := by
  rw [PhiMod.Mon_apply, actPol_cls, map_sub, act_EN, act_E_smul, act_zeta, PhiMod.Mon_apply]

theorem cls_mem_invariants {v : Vec K a ι} (hv : v ∈ Δ.inv) : P.cls v ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_cls, hv g]

theorem Mon_mem_invariants {y : Vec K a ι} (hy : y ∈ Δ.inv) : P.Mon y ∈ Δ.actPol.invariants :=
  fun g => by rw [actPol_Mon, hy g]

def invOf {B : Subalgebra O K⟦X⟧} (W : Submodule B (Vec K a ι)) : Submodule O (Vec K a ι) :=
  W.restrictScalars O ⊓ Δ.inv.restrictScalars O

omit [NeZero e] in
theorem mem_invOf {B : Subalgebra O K⟦X⟧} {W : Submodule B (Vec K a ι)} {v : Vec K a ι} :
    v ∈ Δ.invOf W ↔ v ∈ W ∧ ∀ g, Δ.act g v = v := Iff.rfl

abbrev Minv : Submodule O (Vec K a ι) := Δ.invOf P.M

abbrev Y (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (P.EM η)

def Y' (η : ℕ) : Submodule O (Vec K a ι) := (Δ.Y η).map ((mulV K a ι (X ^ e)).restrictScalars O)

abbrev Yl (η : ℕ) : Submodule O (Vec K a ι) := Δ.invOf (divE l e η (P.Mext (invL l (A O K))))

omit [NeZero e] in
theorem mem_Y' {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Y' η ↔ ∃ y₀ ∈ Δ.Y η, (X : K⟦X⟧) ^ e • y₀ = y :=
  Iff.rfl

omit [NeZero e] in
theorem Y'_le_Y (η : ℕ) : Δ.Y' η ≤ Δ.Y η := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(P.EM η).smul_mem (uIn (A O K) ^ e) hy.1,
    fun g => (Δ.act_X_pow_smul g y).trans (congrArg _ (hy.2 g))⟩

omit [NeZero e] in
theorem mem_Yl_iff {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Yl η ↔ ∃ n : ℕ, (l : K) ^ n • y ∈ Δ.Y η := by
  have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
    simp [smul_eq_C_mul]
  constructor
  · rintro ⟨h1, h2⟩
    choose n hn using fun p : ZMod a × ι => mem_tot.1 h1 p.1 p.2
    refine ⟨Finset.univ.sup n, mem_tot.2 fun τ i => ?_, Δ.inv.smul_mem _ h2⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
    rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
  · rintro ⟨n, h1, h2⟩
    refine ⟨mem_tot.2 fun τ i => ⟨n, ?_⟩, fun g => ?_⟩
    · have := mem_tot.1 h1 τ i
      rwa [smul_comm, Pi.smul_apply, Pi.smul_apply, hl] at this
    · exact smul_right_injective _ (pow_ne_zero n (l_ne_zero l)) ((map_smul _ _ _).symm.trans (h2 g))

def Z (η : ℕ) : Submodule O P.Pol :=
  ((P.EM η).restrictScalars O).map (P.cls.restrictScalars O) ⊓ Δ.actPol.invariants.restrictScalars O

theorem mem_Z {η : ℕ} {w : P.Pol} :
    w ∈ Δ.Z η ↔ (∃ y ∈ P.EM η, P.cls y = w) ∧ ∀ g, Δ.actPol g w = w := Iff.rfl

def Zl (η : ℕ) : Submodule K P.Pol := P.PolEta η ⊓ Δ.actPol.invariants

theorem mem_Zl_of_mem_Z {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : w ∈ Δ.Zl η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := hw
  exact ⟨P.cls_mem_PolEta hy, h⟩

theorem cls_mem_Z {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ.Y η) : P.cls y ∈ Δ.Z η :=
  ⟨⟨y, hy.1, rfl⟩, Δ.cls_mem_invariants hy.2⟩

def actO : Representation O (TameGal K l e a) (Vec K a ι) where
  toFun g := (Δ.act g).restrictScalars O
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp

omit [NeZero e] in
@[simp] theorem actO_apply (g : TameGal K l e a) (v : Vec K a ι) : Δ.actO g v = Δ.act g v := rfl

def actEM (η : ℕ) : Representation O (TameGal K l e a) ((P.EM η).restrictScalars O) :=
  Δ.actO.subrepresentation _ fun g v hv => by
    rw [Submodule.mem_comap, actO_apply]
    exact Δ.act_mem_EM g hv

omit [NeZero e] in
theorem coe_actEM (η : ℕ) (g : TameGal K l e a) (v : (P.EM η).restrictScalars O) :
    (Δ.actEM η g v : Vec K a ι) = Δ.act g v := rfl

def actQuot (η : ℕ) : Representation O (TameGal K l e a)
    ((P.EM η).restrictScalars O ⧸ (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) :=
  (Δ.actEM η).quotient _ fun g v hv => by
    have h : Δ.act g v ∈ P.M := Δ.act_mem_M g _ hv
    rw [← coe_actEM] at h
    exact h


variable (P) in
def quotToPol (η : ℕ) : ((P.EM η).restrictScalars O ⧸
    (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) →ₗ[O] P.Pol :=
  Submodule.liftQ _ (P.cls.restrictScalars O ∘ₗ Submodule.subtype _)
    fun _ hv => P.cls_eq_zero_iff.2 (P.M_le_Man hv)

theorem quotToPol_act (η : ℕ) (g : TameGal K l e a) (w) :
    quotToPol P η (Δ.actQuot η g w) = Δ.actPol g (quotToPol P η w) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

variable [CompleteSpace K]

omit [NeZero a] [TameDescentExponentData K l e a] in
theorem quotToPol_injective (η : ℕ) : Function.Injective (quotToPol P η) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _
    fun y hy => P.mem_M_of_mem_Man y.2 (P.cls_eq_zero_iff.1 hy))

theorem map_invariants_actQuot (η : ℕ) :
    (Δ.actQuot η).invariants.map (quotToPol P η) = Δ.Z η := by
  ext w
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun g => by rw [← quotToPol_act, hw g]⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, fun g => quotToPol_injective η
      ((Δ.quotToPol_act η g _).trans (h g)), rfl⟩

def quotInvEquiv (η : ℕ) : (Δ.actQuot η).invariants ≃ₗ[O] Δ.Z η :=
  (Submodule.equivMapOfInjective _ (quotToPol_injective η) _).trans
    (LinearEquiv.ofEq _ _ (Δ.map_invariants_actQuot η))

end Descent

namespace Descent

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

structure Hom (Δ₁ : Descent P) (Δ₂ : Descent Q) extends BK.Hom P Q where
  app_act : ∀ g v, toHom.app (Δ₁.act g v) = Δ₂.act g (toHom.app v)

namespace Hom

variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)


omit [NeZero e] in
theorem app_mem_inv {v : Vec K a ι} (hv : v ∈ Δ₁.inv) : F.app v ∈ Δ₂.inv :=
  fun g => by rw [← F.app_act, hv g]


omit [NeZero e] in
theorem app_mem_Y {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y η) : F.app y ∈ Δ₂.Y η :=
  ⟨F.app_mem_EM hy.1, F.app_mem_inv hy.2⟩

omit [NeZero e] in
theorem app_mem_Y' {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y' η) : F.app y ∈ Δ₂.Y' η := by
  obtain ⟨y₀, h₀, rfl⟩ := Δ₁.mem_Y'.1 hy
  exact Δ₂.mem_Y'.2 ⟨_, F.app_mem_Y h₀, (map_smul _ _ _).symm⟩

theorem onPol_act (g : TameGal K l e a) (w : P.Pol) :
    F.onPol (Δ₁.actPol g w) = Δ₂.actPol g (F.onPol w) := by
  obtain ⟨y, rfl⟩ := P.Man.mkQ_surjective w
  rw [actPol_cls, BK.Hom.onPol_cls, BK.Hom.onPol_cls, actPol_cls, F.app_act]

end Hom

variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)

def plusInl : Hom Δ (Δ.plus hy hinv) where
  toHom := P.plusInl hy
  app_act g v := by rw [P.plusInl_app, P.plusInl_app, plus_act_join, map_zero]

theorem tameDescent_extended_action_extraVector (g : TameGal K l e a) : (Δ.plus hy hinv).act g xVec = xVec := by
  rw [xVec, plus_act_join, map_zero, map_one]

end Descent


omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
structure IsExactTriple {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
    (F : Hom P Q) (G : Hom Q T) : Prop where
  inj : ∀ v ∈ P.M, F.app v = 0 → v = 0
  exact : ∀ v ∈ Q.M, G.app v = 0 ↔ v ∈ F.imM
  finiteLength : IsFiniteLength (A O K) G.coker

namespace PhiMod

omit [NeZero a] [TameDescentExponentData K l e a]

variable (P : PhiMod O K l e a ι)

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem nabla_mem_MM_of_basis (h : ∀ i, P.nabla (P.phi (bas i)) ∈ P.MM)
    (h' : ∀ i, P.phi (bas i) ∈ P.MM) {m : Vec K a ι} (hm : m ∈ P.MM) : P.nabla m ∈ P.MM := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.eq_sum_phi_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) := P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  rw [nabla_smul_tot]
  exact add_mem (P.smul_tot_mem_ext (fun τ => derivative_mem_S (hc τ)) (h' i))
    (P.smul_tot_mem_ext hc (h i))

theorem EN_mem_Man_of_basis (h : ∀ i, P.EN (bas i) ∈ P.Man) {m : Vec K a ι} (hm : m ∈ P.Man) :
    P.EN m ∈ P.Man := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) : m τ i ∈ Rpi O K l e := mem_tot.1 hm τ i
  rw [EN_apply, conn_smul_tot, smul_add, smul_comm (E K l e) (fun τ => m τ i)]
  exact add_mem (P.smul_mem_Man (E_mem l e _) (P.smul_tot_mem_Mext
    (fun τ => N_mem (derivative_mem_R l (hc τ))) (P.M_le_Man (P.bas_mem_M i))))
    (P.smul_tot_mem_Mext hc (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [Fact l.Prime] in
theorem smul_mem_ext_of_basis {c : K⟦X⟧} (h : ∀ i, c • bas i ∈ P.L) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.Mext B) : c • m ∈ P.ext B := by
  rw [eq_sum_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_ext (fun τ => mem_tot.1 hm τ i) (P.ext_mono hB (h i))

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem smul_mem_Mext_of_basis {c : K⟦X⟧} (h : ∀ i, c • P.phi (bas i) ∈ P.M) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.ext B) : c • m ∈ P.Mext B := by
  rw [P.eq_sum_phi_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_Mext (fun τ => P.mem_extc_iff.1 (mem_tot.1 hm τ) i) (P.Mext_mono hB (h i))

variable {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

omit [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem bas_inl (i : ι) : bas (Sum.inl i) = (P.plusInl hy).app (bas i) := by
  rw [plusInl_app]
  ext τ (j | j) : 2 <;> simp [bas, join, Pi.single_apply]

omit [IsUltrametricDist K] [Fintype ι] in
theorem bas_inr : (bas (Sum.inr ()) : Vec K a (ι ⊕ Unit)) = xVec := by
  ext τ (j | j) : 2 <;> simp [bas, join, xVec]

theorem plus_upper {η : ℕ} (h : ∀ v ∈ P.L, E K l e ^ η • v ∈ P.M) (hη : y ∈ P.EM η) :
    ∀ v ∈ (P.plus hy).L, E K l e ^ η • v ∈ (P.plus hy).M := fun _ =>
  (P.plus hy).smul_mem_Mext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← Hom.app_phi, ← map_smul]
      exact Hom.app_mem_M _ (h _ (P.phi_mem_L (P.bas_mem_M i)))
    · rw [bas_inr, phi_extension_generator_eq_add, smul_add, ← map_smul, ← bas_inr]
      exact add_mem ((P.plus hy).M.smul_mem (EIn l e (A O K) ^ η) ((P.plus hy).bas_mem_M _))
        (Hom.app_mem_M _ hη)) le_rfl

theorem plus_lower {n : ℕ} (h : ∀ v ∈ P.M, E K l e ^ n • v ∈ P.L) (hn : E K l e ^ n • y ∈ P.L) :
    ∀ v ∈ (P.plus hy).M, E K l e ^ n • v ∈ (P.plus hy).L := fun _ =>
  (P.plus hy).smul_mem_ext_of_basis (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [P.bas_inl hy, ← map_smul]
      exact Hom.app_mem_ext _ le_rfl (h _ (P.bas_mem_M i))
    · rw [bas_inr, eq_sub_of_add_eq (P.phi_extension_generator_eq_add hy).symm, smul_sub,
        ← map_smul (P.plusInl hy).app, ← bas_inr]
      exact sub_mem ((P.plus hy).L.smul_mem (EIn l e (A O K) ^ n)
        ((P.plus hy).phi_mem_L ((P.plus hy).bas_mem_M _))) (Hom.app_mem_ext _ le_rfl hn)) le_rfl

end PhiMod

end GlobalTheory.BK
end
end

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

theorem exists_eq_mul_add_of_isAdicComplete {R : Type} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (T : R →+ R) (hT : ∀ x, T (t * x) = t * T x) (w : R) :
    ∃ x, x = t * T x + w := by
  have hS (n : ℕ) (x y : R) : x ≡ y [SMOD (Ideal.span {t} ^ n • ⊤ : Ideal R)] ↔ t ^ n ∣ x - y := by
    simp [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd (n : ℕ) (x : R) (h : t ^ n ∣ x) : t ^ (n + 1) ∣ t * T x := by
    obtain ⟨y, rfl⟩ := h
    have : T (t ^ n * y) = t ^ n * T y := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', mul_assoc, hT, ih, mul_assoc]
    exact ⟨T y, by rw [this]; ring⟩
  let f : ℕ → R := fun n => (fun x => t * T x + w)^[n] 0
  have hf (n : ℕ) : f (n + 1) = t * T (f n) + w := Function.iterate_succ_apply' _ _ _
  have h1 (n : ℕ) : t ^ n ∣ f (n + 1) - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hf (n + 1), hf n, add_sub_add_right_eq_sub, ← mul_sub, ← map_sub, ← hf]
      exact hd _ _ ih
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) f (fun {m n} hmn => by
    rw [hS]
    induction hmn with
    | refl => simp
    | step h ih =>
      have := dvd_sub ih ((pow_dvd_pow t h).trans (h1 _))
      convert this using 1
      simp)
  refine ⟨x, sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)⟩
  rw [hS, sub_zero]
  have := dvd_sub (hd n _ ((hS _ _ _).1 (hx n))) ((hS _ _ _).1 (hx (n + 1)))
  refine (pow_dvd_pow t n.le_succ).trans ?_
  convert this using 1
  rw [hf, map_sub]
  ring

theorem pow_mul_factorial_dvd (l k : ℕ) (hl : 0 < l) : l ^ k * k.factorial ∣ (l * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, l * (k + 1) = m + 1 := ⟨l * (k + 1) - 1, by
      have : 0 < l * (k + 1) := by positivity
      omega⟩
    have h : (l * k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by nlinarith)
    rw [hm, Nat.factorial_succ m, ← hm, Nat.factorial_succ, pow_succ]
    refine Dvd.dvd.trans (dvd_of_eq ?_) (mul_dvd_mul_left (l * (k + 1)) (ih.trans h))
    ring

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem exists_mul_frob_E : ∃ c ∈ S O K e, c * frob K l (E K l e) = l := by
  have hl := (Fact.out : l.Prime).pos
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  have hc (n : ℕ) : ‖coeff n c‖ * wS K e n ≤ wS K (e * l) n := by
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [wS, wS, Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), mul_assoc e l,
        Nat.mul_div_cancel_left _ (NeZero.pos e), coeff_rescale, coeff_mk, Pi.one_apply, mul_one,
        norm_pow, norm_neg, norm_inv, inv_pow, inv_mul_le_iff₀ (pow_pos (norm_pos_iff.2 hl0) k),
        ← norm_pow, ← norm_mul]
      exact_mod_cast norm_natCast_le_of_dvd (K := K) (pow_mul_factorial_dvd l k hl)
    · simpa using wS_nonneg _ _
  refine ⟨c, ⟨fun n => (hc n).trans (wS_le_one _ _), squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) hc (tendsto_wS l (e * l))⟩, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add (f := _), map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  linear_combination (l : K⟦X⟧) * h - c * X ^ (e * l) * h2

omit [IsUltrametricDist K] in
theorem E_mul_N_Ezpow (j : ℤ) :
    E K l e * N K (Ezpow (K := K) l e j) =
      (j : K⟦X⟧) * N K (E K l e) * Ezpow (K := K) l e j := by
  have h1 (i : ℤ) : Ezpow (K := K) l e (i + 1) = Ezpow (K := K) l e i * E K l e := by
    simp [Ezpow, _root_.zpow_add]
  have key (i : ℤ) : N K (Ezpow (K := K) l e (i + 1)) =
      Ezpow (K := K) l e i * N K (E K l e) + E K l e * N K (Ezpow (K := K) l e i) := by
    rw [h1, Derivation.leibniz]
    rfl
  induction j using Int.induction_on with
  | zero => simp [Ezpow]
  | succ i ih =>
    rw [key, ih, h1]
    push_cast
    ring
  | pred i ih =>
    have h := key (-i - 1)
    have h' := h1 (-i - 1)
    rw [sub_add_cancel] at h h'
    rw [h, h'] at ih
    refine (isUnit_E (K := K) l e).mul_left_cancel ?_
    push_cast at ih ⊢
    linear_combination ih

omit [IsUltrametricDist K] in
theorem map_Ezpow (f : K⟦X⟧ →+* K⟦X⟧) (hf : f (E K l e) = E K l e) (j : ℤ) :
    f (Ezpow (K := K) l e j) = Ezpow (K := K) l e j := by
  have h : Units.map (f : K⟦X⟧ →* K⟦X⟧) (isUnit_E (K := K) l e).unit = (isUnit_E l e).unit :=
    Units.ext hf
  conv_rhs => rw [Ezpow, ← h, ← map_zpow]
  rfl

omit [IsUltrametricDist K] in
theorem Ezpow_neg_mul (j : ℤ) : Ezpow (K := K) l e (-j) * Ezpow (K := K) l e j = 1 := by
  rw [Ezpow, Ezpow, ← Units.val_mul, ← _root_.zpow_add]
  simp

variable {l e}

theorem mx_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mx τ i k = Ezpow (K := K) l e (j τ) := by
  have h : Units.map ((invE l e (A O K)).val : invE l e (A O K) →* K⟦X⟧) (Eunit O K l e) =
      (isUnit_E l e).unit := Units.ext rfl
  rw [Ezpow, ← h, ← map_zpow]
  rw [PhiMod.mx, rankOne]
  dsimp only
  generalize Eunit O K l e ^ j τ = u
  simp

theorem mxInv_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mxInv τ i k = Ezpow (K := K) l e (-j τ) := by
  have h := congrFun (congrFun ((rankOne O K l e j).mxInv_mul_mx τ) ()) ()
  rw [Matrix.mul_apply, Fintype.sum_unique, mx_rankOne_eq, Matrix.one_apply_eq,
    ← Ezpow_neg_mul l e (j τ)] at h
  exact mul_right_cancel₀ (Units.ne_zero _) h

theorem phi_bas_rankOne (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).phi (bas ()) =
    Ezpow (K := K) l e j • bas () := by
  ext τ i : 2
  simp [PhiMod.phi_bas, mx_rankOne_eq, bas]

theorem mem_ext_rankOne (j : ℤ) {B : Subalgebra O K⟦X⟧} {v : Vec K a Unit} :
    v ∈ (rankOne O K l e fun _ : ZMod a => j).ext B ↔ ∀ τ, Ezpow (K := K) l e (-j) * v τ () ∈ B := by
  rw [PhiMod.ext, mem_tot]
  refine forall_congr' fun τ => ?_
  rw [PhiMod.extc, Set.range_unique, Submodule.mem_span_singleton]
  have h (c : B) : c • ((rankOne O K l e fun _ : ZMod a => j).mx τ).col () = v τ ↔
      (c : K⟦X⟧) = Ezpow (K := K) l e (-j) * v τ () := by
    simp only [funext_iff, Unique.forall_iff, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul,
      Matrix.col_apply, mx_rankOne_eq]
    constructor <;> intro hc
    · rw [← hc, mul_left_comm, Ezpow_neg_mul, mul_one]
    · rw [hc, mul_right_comm, Ezpow_neg_mul, one_mul]
  exact ⟨fun ⟨c, hc⟩ => (h c).1 hc ▸ c.2, fun hv => ⟨⟨_, hv⟩, (h ⟨_, hv⟩).2 rfl⟩⟩

variable [CompleteSpace K]

theorem exists_nabla_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).nabla (Ezpow (K := K) l e j • bas ()) =
      γ • Ezpow (K := K) l e j • bas () := by
  set P := rankOne O K l e fun _ : ZMod a => j
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : l.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n, l * e = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (mul_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e))
  have := isAdicComplete_S O K l e
  obtain ⟨γ, hγ⟩ := exists_eq_mul_add_of_isAdicComplete (l : S O K e)
    { toFun := fun x => uIn _ ^ m * ⟨_, frob_mem_S l x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    (fun x => Subtype.ext (by simp [mul_left_comm])) (-((j : S O K e) * (e : S O K e) * uIn (S O K e) ^ n * (⟨c, hc⟩ : S O K e)))
  have hγ' : (γ : K⟦X⟧) = (l : K⟦X⟧) * (X ^ m * frob K l γ) +
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ n * c) := by
    simpa using congrArg Subtype.val hγ
  refine ⟨γ, γ.2, smul_right_injective _ (X_ne_zero (R := K)) ?_⟩
  have hq : (l : K⟦X⟧) * frob K l (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) =
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ (n + 1) * c) := by
    have h1 : E K l e * (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) =
        -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ e) := by
      rw [← mul_assoc, E_mul_N_Ezpow, mul_assoc, Ezpow_neg_mul, N_E]
      push_cast
      ring
    have h2 := congrArg (frob K l) h1
    simp only [map_mul, map_neg, map_pow, frob_X, map_natCast, map_intCast, ← pow_mul, hn] at h2 ⊢
    rw [← hcE]
    linear_combination c * h2
  have hb : (bas () : Vec K a Unit) = Ezpow (K := K) l e (-j) • Ezpow (K := K) l e j • bas () := by
    rw [smul_smul, Ezpow_neg_mul, one_smul]
  have hl (v : Vec K a Unit) : (l : K) • v = (l : K⟦X⟧) • v := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hR : Raises (P.lphi * mulV K a Unit (Ezpow (K := K) l e (-j))) := fun k v hv =>
    P.raises_lphi k _ ((uPow K a Unit _).smul_mem _ hv)
  change P.conn _ = (X : K⟦X⟧) • (γ : K⟦X⟧) • Ezpow (K := K) l e j • bas ()
  rw [← sub_eq_zero, smul_smul X]
  refine hR.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ =>
      P.conn (Ezpow (K := K) l e j • bas ()) -
        (X * (γ : K⟦X⟧)) • Ezpow (K := K) l e j • bas ())
    (fun _ => sub_mem (P.conn_mem_uPow _) (by rw [mul_smul]; exact X_smul_mem_uPow _))
    (fun _ => ?_) ()
  have h3 : Ezpow (K := K) l e (-j) • P.conn (Ezpow (K := K) l e j • bas ()) =
      P.conn (bas ()) - (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) • bas () := by
    conv_rhs => rw [hb, P.conn_smul, ← hb, mul_smul, add_sub_cancel_left]
  have hmulV (v : Vec K a Unit) :
      mulV K a Unit (Ezpow (K := K) l e (-j)) v = Ezpow (K := K) l e (-j) • v := rfl
  rw [mul_apply_eq_comp, hmulV, smul_sub, h3, smul_comm _ (X * (γ : K⟦X⟧)), ← hb, map_sub,
    map_sub, P.lphi_apply, ← P.conn_phi, P.lphi_apply, P.lphi_apply, P.phi_smul, P.phi_smul,
    phi_bas_rankOne, hl, hl, smul_smul (l : K⟦X⟧), smul_smul (l : K⟦X⟧), hq, sub_sub, ← add_smul,
    map_mul, frob_X]
  congr 2
  have hX : (X : K⟦X⟧) ^ l = X ^ (m + 1) := by rw [← hm]
  linear_combination X * hγ' - l * frob K l γ * hX

end GlobalTheory.BK
