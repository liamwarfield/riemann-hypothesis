module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TiltAbs

variable {l : ℕ} [Fact l.Prime]

lemma rootT_pow (x : Per.Fl l) (n : ℕ) : rootT x n ^ l ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

lemma untilt_add (x y : Per.Fl l) :
    ∃ t : Per.OC l, (x + y).untilt = x.untilt + y.untilt + (l : Per.OC l) * t := by
  have h : Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x + y).untilt =
      Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x.untilt + y.untilt) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_add (f := _), map_add (f := _), PreTilt.mk_untilt_eq_coeff_zero,
      PreTilt.mk_untilt_eq_coeff_zero]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← ht]; ring⟩

lemma rootT_add (x y : Per.Fl l) (n : ℕ) :
    ∃ t : Per.OC l, rootT (x + y) n = rootT x n + rootT y n + (l : Per.OC l) * t := by
  unfold rootT
  rw [iterate_map_add]
  exact untilt_add _ _

lemma norm_le_one (t : Per.OC l) : ‖(t : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 t.2

lemma norm_l_lt : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt

lemma bound (x y : Per.Fl l) (n : ℕ) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖)
        (‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) := by
  obtain ⟨t, ht⟩ := rootT_add x y n
  rw [← rootT_pow (x + y) n, ← rootT_pow x n, ← rootT_pow y n]
  have h1 : ‖((rootT (x + y) n : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
        ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [ht]
    push_cast
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      (IsUltrametricDist.norm_add_le_max _ _) ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one t)
  push_cast
  simp only [norm_pow]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 (l ^ n)
  refine h2.trans ?_
  rcases max_choice (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
    ‖((l : ℕ) : ℂ_[l])‖ with h | h <;> rw [h]
  · refine le_trans ?_ (le_max_left _ _)
    rcases max_choice ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖
      with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact le_max_right _ _

lemma eq_zero_of_untilt (x : Per.Fl l) (hx : x.untilt = 0) : x = 0 := by
  apply Perfection.ext
  intro n
  have h1 : (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x).untilt = 0 := by
    have h := rootT_pow x n
    rw [hx] at h
    exact pow_eq_zero_iff (pow_ne_zero n (Fact.out : l.Prime).ne_zero) |>.1 h
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x)
  rw [h1, map_zero] at h2
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at h3
  have hc : PreTilt.coeff n x = PreTilt.coeff n 0 := by rw [map_zero, ← h3, ← h2]
  simpa only [PreTilt.coeff_def] using hc

theorem untilt_ultrametric_definite (l : ℕ) [Fact l.Prime] (x y : Per.Fl l) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧
    (x.untilt = 0 → x = 0) := by
  refine ⟨?_, eq_zero_of_untilt x⟩
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt).comp
      (tendsto_pow_atTop_atTop_of_one_lt hl)
  have h2 := (tendsto_const_nhds (x := max ‖((x.untilt : Per.OC l) : ℂ_[l])‖
    ‖((y.untilt : Per.OC l) : ℂ_[l])‖)).max ht
  have h3 := ge_of_tendsto' h2 (bound x y)
  rwa [max_eq_left (le_max_of_le_left (norm_nonneg _))] at h3

end GlobalTheory.TiltAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untilt_norm_ultrametric_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Per.Fl l), ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤ max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧ (x.untilt = 0 → x = 0) := by
  first | exact @GlobalTheory.TiltAbs.untilt_ultrametric_definite | exact GlobalTheory.TiltAbs.untilt_ultrametric_definite | (intros; apply GlobalTheory.TiltAbs.untilt_ultrametric_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top {k Γ : Type} [Field k] [Group Γ] {L : Type}
    [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : _root_.Formalism.MainNotions.N.Stable (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ)) W) (hne : W ≠ ⊥)
    (hsp : Submodule.span k (Set.range fun g =>
      (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤) :
    _root_.Formalism.MainNotions.N.IsIrrSub (_root_.Formalism.MainNotions.N.mapRep f ρ)
      (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  classical
  have hmul : ∀ (g : Γ) (w : Fin a → k),
      ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec (f ∘ w) =
        f ∘ ((ρ g : Matrix (Fin a) (Fin a) k).mulVec w) := by
    intro g w
    funext i
    exact (RingHom.map_mulVec f _ w i).symm
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.toLin' ((_root_.Formalism.MainNotions.N.mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  let A := Submodule.span L (Set.range T)
  let P : Submodule k (Module.End k W) :=
    { carrier := {E | ∃ M ∈ A, ∀ w : W, M (f ∘ (w : Fin a → k)) = f ∘ ((E w : W) : Fin a → k)}
      add_mem' := by
        rintro E₁ E₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
        refine ⟨M₁ + M₂, A.add_mem hM₁ hM₂, fun w => ?_⟩
        rw [LinearMap.add_apply, h₁, h₂]
        funext i
        simp
      zero_mem' := ⟨0, A.zero_mem, fun w => by funext i; simp⟩
      smul_mem' := by
        rintro c E ⟨M, hM, h⟩
        refine ⟨f c • M, A.smul_mem _ hM, fun w => ?_⟩
        rw [LinearMap.smul_apply, h]
        funext i
        simp }
  have hP : ∀ E, E ∈ P := by
    have hle : Submodule.span k (Set.range fun g =>
        (_root_.Formalism.MainNotions.N.matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      refine ⟨T g, Submodule.subset_span ⟨g, rfl⟩, fun w => ?_⟩
      rw [LinearMap.restrict_coe_apply]
      exact hmul g w
    intro E
    apply hle
    rw [hsp]
    exact Submodule.mem_top
  have hA : ∀ W' : Submodule L (Fin a → L), _root_.Formalism.MainNotions.N.IsInv (_root_.Formalism.MainNotions.N.mapRep f ρ) W' →
      ∀ M ∈ A, ∀ v ∈ W', M v ∈ W' := by
    intro W' hW' M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hW' g v hv
    | zero => intro v _; simpa using W'.zero_mem
    | add x y _ _ hx hy => intro v hv; exact W'.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; exact W'.smul_mem c (hx v hv)
  unfold _root_.Formalism.MainNotions.N.IsIrrSub
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    apply hw0
    have hfw : f ∘ w ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) :=
      Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at hfw
    funext i
    simpa using congrFun hfw i
  · intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro W' hle hst
    by_cases h0 : W' = ⊥
    · exact Or.inl h0
    right
    apply le_antisymm hle
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    rw [Submodule.span_le]
    rintro _ ⟨w₀, hw₀, rfl⟩
    show f ∘ w₀ ∈ W'
    let φ : W →ₗ[k] k := (LinearMap.proj i : (Fin a → k) →ₗ[k] k).comp W.subtype
    let E : Module.End k W := φ.smulRight ⟨w₀, hw₀⟩
    obtain ⟨M, hMA, hM⟩ := hP E
    have key : ∀ y ∈ Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))),
        M y = y i • (f ∘ w₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hM ⟨w, hw⟩]
        funext j
        simp [E, φ]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, Pi.add_apply, add_smul]
      | smul c y _ hy => rw [map_smul, hy, Pi.smul_apply, smul_eq_mul, mul_smul]
    have hmem : M x ∈ W' := hA W' hst M hMA x hx
    rw [key x (hle hx)] at hmem
    have hsm := W'.smul_mem (x i)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hsm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVector
open PowerSeries GlobalTheory.BK

noncomputable section

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

theorem PhiMod.eq_xi_red_of_conn_eq_zero (P : PhiMod O K l e a ι) {v : Vec K a ι}
    (h : P.conn v = 0) : v = P.xi (red v) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [PhiMod.conn_xiExt] at h
  have hN : ∀ τ i, N K (w τ i) = 0 := fun τ i => by
    have := congrFun (congrFun (P.xiExt.injective (h.trans (map_zero _).symm)) τ) i
    simpa using this
  have hw : w = cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | n
    · simp
    · have := congrArg (coeff (n + 1)) (hN τ i)
      rw [coeff_N, map_zero] at this
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  rw [PhiMod.xi_apply, PhiMod.red_xiExt, ← hw]

theorem PhiMod.mem_ext_of_plusInl (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    (h : (P.plusInl hy).app v ∈ (P.plus hy).ext B) : v ∈ P.ext B := by
  rw [PhiMod.plusInl_app] at h
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, hmv⟩ := (P.plus hy).mem_extc.1 (mem_tot.1 h τ)
  refine P.mem_extc.2 ⟨fun i => m (Sum.inl i), fun i => hm (Sum.inl i), ?_⟩
  have h0 : m (Sum.inr ()) = 0 := by
    have := congrFun hmv (Sum.inr ())
    simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this.symm
  funext i
  have := congrFun hmv (Sum.inl i)
  simpa [join, PhiMod.plus, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using this

end GlobalTheory.BK

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

theorem exists_conn_eq_zeta_of_mem_Y (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Y) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  have hy' := mem_invE_of_mem_Y hy
  set P := D.toPhiMod.plus hy'
  set F := D.toPhiMod.plusInl hy'
  set G := D.toPhiMod.plusProj hy'
  set t := P.phi xVec - P.xi (red (P.phi xVec)) with ht
  have inj : ∀ v w, F.app v = F.app w → v = w := fun v w h => by
    rw [PhiMod.plusInl_app, PhiMod.plusInl_app] at h
    funext τ i
    exact congrFun (congrFun h τ) (Sum.inl i)
  have hct : P.conn t = F.app (D.zeta y) := by
    rw [ht, map_sub, PhiMod.conn_xi, sub_zero]
    exact D.conn_phi_extension_generator_eq_zeta hy'
  have hrt : red t = 0 := by
    rw [ht, map_sub, PhiMod.red_xi, sub_self]
  have hx : G.app t = 0 := by
    have h1 : (rankOne O K l e fun _ : ZMod a => 0).conn (G.app t) = 0 := by
      rw [← Hom.app_conn, hct, PhiMod.plusInl_app, PhiMod.plusProj_app]
      rfl
    rw [PhiMod.eq_xi_red_of_conn_eq_zero _ h1, Hom.red_app, hrt, map_zero, map_zero]
  have key : ∀ τ, t τ (Sum.inr ()) = 0 := fun τ => by
    rw [← join_eta t, PhiMod.plusProj_app] at hx
    have := congrFun (congrFun hx τ) ()
    simpa using this
  set s : Vec K a ι := fun τ i => t τ (Sum.inl i)
  have hts : t = F.app s := by
    rw [PhiMod.plusInl_app]
    conv_lhs => rw [← join_eta t]
    congr 1
    funext τ
    exact key τ
  have hxM : (xVec : Vec K a (ι ⊕ Unit)) ∈ P.M := by
    rw [← PhiMod.bas_inr]
    exact P.bas_mem_M _
  have htM : t ∈ P.MMl := by
    refine sub_mem (P.ext_mono ((A_le_S l e).trans (le_away _ _)) (P.phi_mem_L hxM)) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a (ι ⊕ Unit) P).2 _).2 (mem_tot.2 fun τ i => ?_)
    rw [cst_apply]
    exact HasK.C_mem _
  refine ⟨s, D.toPhiMod.mem_ext_of_plusInl hy' (hts ▸ htM), fun g => ?_, inj _ _ ?_⟩
  · have hΔ : (D.desc.plus hy' hy.2).act g t = t := by
      rw [ht, map_sub, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g, Descent.act_xi,
        ← Descent.red_act, Descent.act_phi, Descent.tameDescent_extended_action_extraVector D.desc hy' hy.2 g]
    apply inj
    have h2 : (D.desc.plus hy' hy.2).act g (F.app s) = F.app s := by rw [← hts]; exact hΔ
    exact ((Descent.plusInl D.desc hy' hy.2).app_act g s).trans h2
  · rw [Hom.app_conn, ← hts, hct]

end BKDat

end GlobalTheory.BK

namespace GlobalTheory.BK

namespace BKDat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem exists_conn_eq_zeta (D : BKDat O K l e a ι η H) {y : Vec K a ι} (hy : y ∈ D.Yl) :
    ∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y := by
  obtain ⟨n, hn⟩ := D.desc.mem_Yl_iff.1 hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta_of_mem_Y hn
  have hl : ((l : K) ^ n) ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ n)⁻¹ • s, ?_, D.desc.inv.smul_mem _ hsi, ?_⟩
  · have : ((l : K) ^ n)⁻¹ • s = (fun _ : ZMod a => C ((l : K) ^ n)⁻¹) • s := by
      funext τ i
      simp [smul_eq_C_mul]
    rw [this]
    exact D.smul_tot_mem_ext (fun _ => HasK.C_mem _) hsM
  · rw [map_smul, hsc, map_smul, smul_smul, inv_mul_cancel₀ hl, one_smul]

theorem Mon_mem_range_Lc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl,
    (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧
      D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  obtain ⟨s, hsM, hsi, hsc⟩ := D.exists_conn_eq_zeta hy
  have hyi : ∀ g, D.desc.act g y = y := hy.2
  have hsi' : ∀ g, D.desc.act g s = s := hsi
  refine ⟨⟨s, hsM, hsi, hsc, ?_⟩, D.cls (y - s), ⟨⟨y - s, ?_, rfl⟩, fun g => ?_⟩, ?_⟩
  · set v := D.phi s - s - D.phi y with hv
    have hcv : D.conn v = 0 := by
      have hz := D.zeta_eq y
      rw [PhiMod.lphi_apply, map_sub, smul_sub] at hz
      rw [hv, map_sub, map_sub, PhiMod.conn_phi, PhiMod.conn_phi, hsc, sub_right_comm]
      exact sub_eq_zero.2 hz.symm
    refine ⟨red v, fun g => ?_, D.eq_xi_red_of_conn_eq_zero hcv⟩
    rw [← Descent.red_act, hv]
    congr 1
    rw [(D.desc.act g).map_sub, (D.desc.act g).map_sub, Descent.act_phi, Descent.act_phi, hsi' g,
      hyi g]
  · rw [SetLike.mem_coe, mem_divE, smul_sub]
    refine sub_mem ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_A_le_Rpi l e) (mem_divE.1 hy.1)))
      ((PhiMod.mem_Man _).2 (D.Mext_mono (invL_S_le_Rpi l e)
        (D.smul_mem_Mext ((A_le_S l e).trans (le_away _ _)) hsM)))
  · rw [Descent.actPol_cls, map_sub, hyi g, hsi' g]
  · rw [Lc_cls, PhiMod.Mon_apply, map_sub, PhiMod.EN_apply D.toPhiMod s, hsc]

end BKDat

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVectorStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_mem_range_of_invariant_vector : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Yl, (∃ s ∈ D.MMl, s ∈ D.desc.inv ∧ D.conn s = D.zeta y ∧ ∃ d : D.D, (∀ g, D.desc.actD g d = d) ∧ D.phi s - s - D.phi y = D.xi d) ∧ ∃ w ∈ D.Zl, D.Lc w = D.Mon y := by
  first | exact @GlobalTheory.BK.BKDat.Mon_mem_range_Lc | exact GlobalTheory.BK.BKDat.Mon_mem_range_Lc | (intros; apply GlobalTheory.BK.BKDat.Mon_mem_range_Lc <;> assumption)
end
end
