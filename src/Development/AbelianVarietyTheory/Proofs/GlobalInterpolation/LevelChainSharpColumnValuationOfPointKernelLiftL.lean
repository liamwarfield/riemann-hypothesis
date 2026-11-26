module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtension
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem PtModel.mem_Fi_iff_exists_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i)
    (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  intro D u X i M φ
  rw [M.mem_Fi]
  constructor
  · intro h
    choose y hy hfix using h
    choose cl gp hp using M.rep_surj
    have key : ∀ (c c' : X.C.cls i) (g g' : M.G), g • M.rep c = g' • M.rep c' →
        M.act g (y c) = M.act g' (y c') := by
      intro c c' g g' hgg
      have h1 : (g'⁻¹ * g) • M.rep c = M.rep c' := by
        rw [mul_smul, hgg, inv_smul_smul]
      have hc := M.rep_inj c c' _ h1
      subst hc
      have h2 := hfix c _ h1
      have h3 : g = g' * (g'⁻¹ * g) := by group
      conv_lhs => rw [h3, map_mul, Module.End.mul_apply, h2]
    refine ⟨fun p => M.act (gp p) (y (cl p)), fun c => ?_, fun g p => ?_⟩
    · have := key (cl (M.rep c)) c (gp (M.rep c)) 1 (by rw [hp, one_smul])
      rw [hy c]
      simp only [this, map_one, Module.End.one_apply]
    · have := key (cl (g • p)) (cl p) (gp (g • p)) (g * gp p) (by rw [hp, mul_smul, hp])
      simp only [this, map_mul, Module.End.mul_apply]
  · rintro ⟨Φ, h1, h2⟩ c
    refine ⟨Φ (M.rep c), h1 c, fun g hg => ?_⟩
    rw [← h2, hg]

end GlobalTheory.LvT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtensionStatement
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_forms_iff_exists_equivariant_extension : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  first | exact @GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | exact GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | (intros; apply GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSum
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSum
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem isExt_KT : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  intro D u X i M M' K φ Φ hK hΦ
  refine ⟨fun c' => ?_, fun g' p' => ?_⟩
  · show Formalism.ThetaLiftIndependence.kerOpM (X.C.wt i) (X.C.Kmap i) φ c' = _
    unfold Formalism.ThetaLiftIndependence.kerOpM
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hΦ.1 c, K.Kmap_eq, Submodule.coe_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hK g']

end GlobalTheory.LvT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSumStatement
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChainTransition_isExt_kernel_sum : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (M' : PtModel X (i + 1)) (K : KerPt M M') (φ : Fn X i) (Φ : M.Pt → M.Val), K.TgtEq → M.IsExt φ Φ → M'.IsExt (KT X i φ) (fun p' => ∑ c, X.C.wt i c • K.k (M.rep c) p' (Φ (M.rep c))) := by
  first | exact @GlobalTheory.LvT.isExt_KT | exact GlobalTheory.LvT.isExt_KT | (intros; apply GlobalTheory.LvT.isExt_KT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValBOfInc
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
end

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT.UKS

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

theorem emb_mem_Fi (X : Ch D u) (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem inv_natCast_mem (w : D.what₂.places.Pl) (n : ℕ) (hn : ¬ D.what₂.places.resChar w ∣ n) :
    ((n : D.what₂.LL))⁻¹ ∈ Ow D w := by
  set p := D.what₂.places.resChar w with hp
  have hpr : p.Prime := D.what₂.places.resChar_prime w
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hpr).2 hn
  have hint : ∀ z : ℤ, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) := fun z => intCast_mem (Ow D w) z
  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hbez' : (p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL) + (n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : D.what₂.LL)) hbez
  have hvp : 0 < D.what₂.places.val w (p : D.what₂.LL) := by
    rw [hp, D.what₂.places.val_resChar w]
    have := D.what₂.places.ramIdx_pos w
    exact_mod_cast this
  have hvn : D.what₂.places.val w (n : D.what₂.LL) = 0 := by
    have h0 : 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by exact_mod_cast hint n
    by_contra hne
    have hpos : 0 < D.what₂.places.val w (n : D.what₂.LL) := lt_of_le_of_ne h0 (Ne.symm hne)
    have h1 : 0 < D.what₂.places.val w ((p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hvp (hint _)
    have h2 : 0 < D.what₂.places.val w ((n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hpos (hint _)
    have h3 := (D.what₂.places.val w).map_lt_add h1 h2
    rw [hbez', AddValuation.map_one] at h3
    exact lt_irrefl _ h3
  show 0 ≤ D.what₂.places.val w ((n : D.what₂.LL))⁻¹
  rw [AddValuation.map_inv, hvn]
  simp

section
variable {i : ℕ} {M : PtModel X i} (Co : M.Coord)

def ExtIn (w : D.what₂.places.Pl) (V : Finset X.A.vT) (φ : Fn X i) : Prop :=
  ∃ Φ, M.IsExt φ Φ ∧ ∀ p, Φ p ∈ Co.valB w V p

variable {Co}

theorem extIn_of_valIn (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i)
    (h : M.ValIn (Co.valB w V) φ) : ExtIn Co w V φ := by
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  refine ⟨Φ, hΦ, fun p => ?_⟩
  obtain ⟨c, g, rfl⟩ := M.rep_surj p
  obtain ⟨y, hy, hyc⟩ := h c
  have : Φ (M.rep c) = y := Subtype.ext ((hΦ.1 c).symm.trans hyc)
  rw [hΦ.2, this]
  exact (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V _).2.2.2 g y hy

theorem ExtIn.mem_Fi {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : φ ∈ X.fm.Fi i := by
  obtain ⟨Φ, hΦ, -⟩ := h
  exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).2 ⟨Φ, hΦ⟩

theorem ExtIn.valIn {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : M.ValIn (Co.valB w V) φ := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact fun c => ⟨_, h _, hΦ.1 c⟩

theorem isExt_smul {φ : Fn X i} {Φ} (h : M.IsExt φ Φ) (a : ℂ) : M.IsExt (a • φ) (fun p => a • Φ p) := by
  refine ⟨fun c => ?_, fun g p => ?_⟩
  · show a • φ c = _
    rw [h.1 c]; rfl
  · simp only [h.2, map_smul]

theorem pow_smul_mem (hC : Co.Ok) {w} (hw : OverT X w) {V p y} (hy : y ∈ Co.valB w V p) (n : ℕ) :
    ((X.A.T : ℂ) ^ n) • y ∈ Co.valB w V p := by
  have := (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V p).2.2.1 ((X.A.T : D.what₂.LL) ^ n)
    (pow_mem (natCast_mem _ _) n) y hy
  simpa using this

theorem ExtIn.pow_smul (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (h : ExtIn Co w V φ) (n : ℕ) :
    ExtIn Co w V (((X.A.T : ℂ) ^ n) • φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact ⟨_, isExt_smul hΦ _, fun p => pow_smul_mem hC hw (h p) n⟩

theorem ExtIn.uop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V v} (hv : v ∈ V)
    {φ : Fn X i} (h : ExtIn Co w V φ) : ExtIn Co w (V.erase v) (Uop X i v φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ, fun p => ?_⟩
  have hv' := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw (V.erase v) p
  refine finsum_mem_induction (fun y => y ∈ Co.valB w (V.erase v) p) hv'.1
    (fun y y' hy hy' => hv'.2.1 y hy y' hy') fun p₁ hp₁ => ?_
  rw [← GlobalTheory.LvT.valB_of_inc D u X i M Co w V v p p₁ hs hv hp₁]
  exact h p₁

theorem ExtIn.uops (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (l : List X.A.vT) (hl : l.Nodup) (hV : ∀ v ∈ l, v ∈ V) :
    ExtIn Co w (V \ l.toFinset) (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id φ) := by
  induction l with
  | nil => simpa using h
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    have h1 := ih hl.2 (fun v' hv' => hV v' (List.mem_cons_of_mem _ hv'))
    have h2 := h1.uop hC hw hs (v := v) (by simp [hl.1, hV v List.mem_cons_self])
    have e : (V \ l.toFinset).erase v = V \ (v :: l).toFinset := by
      ext x; simp; tauto
    rw [e] at h2
    exact h2

theorem ExtIn.drop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (A : Finset X.A.vT) (hA : A ⊆ V) :
    ExtIn Co w (V \ A)
      (((X.A.T : ℂ) ^ (∑ v ∈ A, (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩)) • φ) := by
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  induction A using Finset.induction_on with
  | empty => simpa using h
  | insert v A hv ih =>
    obtain ⟨Φ, hΦ, h1⟩ := ih ((Finset.subset_insert _ _).trans hA)
    have e : (V \ A).erase v = V \ insert v A := by
      ext x; simp; tauto
    rw [Finset.sum_insert hv, zpow_add₀ hT, mul_smul, ← e]
    exact ⟨_, isExt_smul hΦ _, fun p => GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase D u X i M Co hC w hw hs _ v
      (by simp [hv, hA (Finset.mem_insert_self _ _)]) p _ (h1 p)⟩

end

theorem extIn_K {i : ℕ} {M : PtModel X i} {M' : PtModel X (i + 1)} {Co : M.Coord} {Co' : M'.Coord}
    (hC' : Co'.Ok) (K : KerPt M M') (hK : K.TgtEq) {w} (hw : OverT X w)
    (hst : ∀ c, ¬ X.A.T ∣ Nat.card (X.C.stab i c)) (a : ℂ) {V}
    (ha : ∀ p p', ∀ y ∈ Co.valB w ∅ p, a • K.k p p' y ∈ Co'.valB w V p')
    {φ : Fn X i} (h : ExtIn Co w ∅ φ) : ExtIn Co' w V (a • KT X i φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, isExt_smul (GlobalTheory.LvT.isExt_KT D u X i M M' K φ Φ hK hΦ) a, fun p' => ?_⟩
  have hv := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X (i + 1) M' Co' hC' w hw V p'
  simp only [Finset.smul_sum]
  refine Finset.sum_induction _ (fun y => y ∈ Co'.valB w V p') (fun y y' hy hy' => hv.2.1 y hy y' hy') hv.1
    fun c _ => ?_
  rw [smul_comm]
  have := hv.2.2.1 _ (inv_natCast_mem w (Nat.card (X.C.stab i c)) (by rw [show _ = _ from hw]; exact hst c)) _
    (ha _ p' _ (h (M.rep c)))
  simpa [ColumnChain.wt] using this

theorem ukSharp (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv)
    (hK : KerLaws Vt Kt) (hst : StabUnit X) (hW : WtBounds X) : UKSharp X := by
  intro w hw i hi x hx
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  have hC := (Vt i hi.le).2
  have hC' := (Vt (i + 1) hi).2
  have h0 : ExtIn (Vt i hi.le).1 w ∅ (X.fm.emb i x) :=
    extIn_of_valIn hC hw (emb_mem_Fi X i x) ((hC.S_on w hw _ (emb_mem_Fi X i x)).1 ⟨x, hx, rfl⟩)
  suffices h : ExtIn (Vt (i + 1) hi).1 w ∅
      (tpow X (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) •
        Uprod X (i + 1) w (KT X i (X.fm.emb i x))) from (hC'.S_on w hw _ h.mem_Fi).2 h.valIn
  by_cases hs : X.fm.seenP w = true
  · have h1 := extIn_K hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) _ (hK.intP i hi w hw hs) h0
    have h2 := h1.uops hC' hw hs (VVT X w).toList (Finset.nodup_toList _) (fun v _ => Finset.mem_univ v)
    have h3 := h2.drop hC' hw hs _ (Finset.Subset.refl _)
    rw [Finset.sdiff_self, Finset.toList_toFinset, map_smul, smul_smul, ← zpow_add₀ hT] at h3
    set e : ℤ := ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ +
      (((D.R.f * D.R.N i : ℕ) : ℤ) + ∑ τ, X.C.sDiv i τ) with he
    have hle : e ≤ ((2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by
      have a1 : ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ ≤
          ∑ τ, (Wt X τ : ℤ) := by
        rw [← Equiv.sum_comp (X.fm.tauOf w)]
        refine le_trans (Finset.sum_le_sum fun v hv => (hW.2 i hi _).2.2.2 ?_)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Int.natCast_nonneg _)
        simpa [VVT, hs] using hv
      have a2 : ∑ τ, X.C.sDiv i τ ≤ ∑ τ, (Wt X τ : ℤ) := Finset.sum_le_sum fun τ _ => (hW.2 i hi τ).2.1
      have a3 : D.R.f * D.R.N i ≤ D.R.f * D.R.N D.R.m :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _)
      have a3' : ((D.R.f * D.R.N i : ℕ) : ℤ) ≤ ((D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by exact_mod_cast a3
      rw [he, Nat.cast_add, Nat.cast_mul 2, Nat.cast_sum]
      simp only [Nat.cast_ofNat]
      linarith
    obtain ⟨n, hn⟩ := Int.le.dest hle
    have h4 := h3.pow_smul hC' hw n
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ hT, add_comm (n : ℤ), hn, zpow_natCast] at h4
    rw [if_pos hs]
    exact h4
  · have hs' : X.fm.seenP w = false := by simpa using hs
    have h1 := extIn_K (V := ∅) hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) 1 (fun p p' y hy => by
      obtain ⟨y', hy', e⟩ := hK.bar i hi w hw hs' p p' y hy
      rw [one_smul, e]
      exact pow_smul_mem hC' hw hy' _) h0
    rw [if_neg hs]
    simpa [tpow, Uprod, VVT, hs'] using h1

end GlobalTheory.LvT.UKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ}

namespace PtModel

variable (M : PtModel X i)

theorem inc_eq_image (v : X.A.vT) (p : M.Pt) :
    {p₁ | M.Inc v p p₁} =
      (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) '' {q | (p.2 v).Inc q} := by
  ext p₁
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p₁.2 v, h3, ?_⟩
    refine Prod.ext h1.symm ?_
    funext v'
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Function.update_of_ne hv, h2 v' hv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩
    simpa using hq

theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

theorem finsum_inc_comm (v v' : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v' p₁ p₂}, F p₂) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v' p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v p₁ p₂}, F p₂ := by
  by_cases hv : v = v'
  · subst hv; rfl
  have hv' : v' ≠ v := fun h => hv h.symm
  rw [finsum_inc_eq, finsum_inc_eq]
  simp only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']
  rw [finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]
  simp only [Function.update_comm hv]

end PtModel

theorem formsStable_of_tgtEq : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → FormsStable X := by
  intro D u X Lv Kt hK
  refine ⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) _).2 ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' φ Φ hΦ)
    have h2 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ)
    funext c
    rw [h1.1 c, h2.1 c]
    simp only []
    rw [(Lv i hi).finsum_inc_comm v v']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi.le) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X (i + 1) (Lv (i + 1) hi) _).2
      ⟨_, GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩

end GlobalTheory.LvT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT

theorem count_incidence {G P C V : Type} [Group G] [MulAction G P] [Fintype C] [AddCommGroup V] [Module ℂ V]
    (rep : C → P) (hsurj : ∀ p, ∃ (c : C) (g : G), g • rep c = p)
    (hinj : ∀ (c c' : C) (g : G), g • rep c = rep c' → c = c')
    (hfin : ∀ c, Finite (MulAction.stabilizer G (rep c)))
    (I : P → P → Prop) (hup : ∀ p, {q | I p q}.Finite) (hdn : ∀ p, {q | I q p}.Finite)
    (hI : ∀ (g : G) p q, I p q → I (g • p) (g • q))
    (F : P → P → V) (hF : ∀ (g : G) p q, F (g • p) (g • q) = F p q) :
    ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ q ∈ {q | I (rep c) q}, F (rep c) q =
      ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ p ∈ {p | I p (rep c)}, F p (rep c) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  have hfin' : ∀ p : P, Finite (MulAction.stabilizer G p) := by
    intro p
    obtain ⟨c, g, rfl⟩ := hsurj p
    haveI := hfin c
    exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv
  have hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a := by
    intro a
    obtain ⟨c, g, rfl⟩ := hsurj a
    refine ⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩
    rintro r ⟨hr, γ, hγ⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c = c' := hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)
    rw [this]
  have hrinj : Function.Injective rep := fun c c' h => hinj c c' 1 (by rw [one_smul, h])
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F
    (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp)
    (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢; exact hI γ a b h)
    (fun γ a b _ => hF γ a b) hfin' hfin' hR hR
  rw [Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)] at key
  have hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x := by
    intro n x
    change (algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _
    simp
  simp only [hq] at key
  simp only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]
  exact key

theorem levelChainUOperatorCommutation_of_pointPairLaw : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → (∀ i h, (Kt i h).UKLaw) → LevelChainUOperatorCommutation X := by
  intro D u X Lv Kt htgt huk i hi v φ hφ
  set M := Lv i hi.le with hM
  set M' := Lv (i + 1) hi with hM'
  let K : KerPt M M' := Kt i hi
  have hT : K.TgtEq := htgt i hi
  have hU : K.UKLaw := huk i hi
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  obtain ⟨hfinI, hstab, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  obtain ⟨hfinI', -, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X (i + 1) M' v
  have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X (i + 1) M' v _ _ (GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K φ Φ hT hΦ)
  have h2 := GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K _ _ hT (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ)
  have hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2) := by
    obtain ⟨k, hk⟩ := D.R.t_odd
    have e1 : (D.R.t + 1) / 2 = k + 1 := by omega
    have e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [e1, e2, Real.rpow_natCast]
    push_cast; rfl
  have hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹ := by
    intro c
    rw [← M.card_stab]; rfl
  have hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c)) := by
    intro c
    apply Nat.finite_of_card_ne_zero
    rw [← M.card_stab]
    haveI := X.C.stabFin i c
    letI := X.C.stabGrp i c
    exact Nat.card_pos.ne'
  funext c'
  rw [hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]
  congr 1
  have key := count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2)
    (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q))
    (fun g p q => by rw [hΦ.2, K.src])
  have hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]
  simp only [hL, hwt]
  rw [key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]

end GlobalTheory.LvT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace ColSharp

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

noncomputable def colUp (i : ℕ) : Fn X 0 →ₗ[ℂ] Fn X i :=
  Nat.rec (motive := fun i => Fn X 0 →ₗ[ℂ] Fn X i) LinearMap.id (fun i g => KT X i ∘ₗ g) i

theorem colUp_eq (i : ℕ) (φ : Fn X 0) : colUp X i φ = Formalism.ThetaLiftIndependence.chainOpM X.C.wt X.C.Kmap i φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show KT X i (colUp X i φ) = _
    rw [ih]; rfl

theorem colT_eq (φ : Fn X 0) : colT X φ = colUp X D.R.m φ := (colUp_eq X _ φ).symm

theorem emb_mem (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem fold_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (l : List X.A.vT) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ ∈ X.fm.Fi i := by
  induction l with
  | nil => exact hφ
  | cons v l ih => exact hF.1 i hi v _ ih

theorem Uprod_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) : Uprod X i w φ ∈ X.fm.Fi i := fold_mem hF hi _ hφ

theorem Upow_mem (hF : FormsStable X) (w : D.what₂.places.Pl) (n : ℕ) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : (Uprod X 0 w ^ n) φ ∈ X.fm.Fi 0 := by
  induction n with
  | zero => exact hφ
  | succ n ih => rw [pow_succ']; exact Uprod_mem hF (Nat.zero_le _) w ih

theorem colUp_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : colUp X i φ ∈ X.fm.Fi i := by
  induction i with
  | zero => exact hφ
  | succ i ih => exact hF.2.2 i hi _ (ih (Nat.le_of_succ_le hi))

theorem scalar_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) :
    ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ s := by
  have h : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) := by
    have : ((D.R.t + 1 : ℕ) : ℝ) = ((2 * s : ℕ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  rw [h, Real.rpow_natCast]; push_cast; rfl

theorem fold_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (l : List X.A.vT) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X (i + 1) v).comp g) LinearMap.id : Fn X (i + 1) →ₗ[ℂ] Fn X (i + 1)) (KT X i φ) =
      (X.A.T : ℂ) ^ (s * l.length) •
        KT X i ((l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.foldr_cons, LinearMap.comp_apply, LinearMap.comp_apply, ih, map_smul,
      h4 i hi v _ (fold_mem hF hi.le l hφ), scalar_eq hs, smul_smul, ← pow_add, List.length_cons, Nat.mul_succ]

theorem Uprod_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    Uprod X (i + 1) w (KT X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card) • KT X i (Uprod X i w φ) := by
  rw [← Finset.length_toList]; exact fold_comm hF h4 hs hi _ hφ

theorem Uprod_colUp (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    Uprod X i w (colUp X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card * i) • colUp X i (Uprod X 0 w φ) := by
  induction i with
  | zero => simp [colUp]
  | succ i ih =>
    have hi' : i < D.R.m := hi
    show Uprod X (i + 1) w (KT X i (colUp X i φ)) = _ • KT X i (colUp X i (Uprod X 0 w φ))
    rw [Uprod_comm hF h4 hs hi' w (colUp_mem hF hi'.le hφ), ih hi'.le, map_smul, smul_smul, ← pow_add,
      Nat.mul_succ, Nat.add_comm (s * _)]

theorem chain_into (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s)
    (w : D.what₂.places.Pl) (e : ℕ)
    (hU : ∀ i, i < D.R.m → Into X w (fun φ => tpow X e • Uprod X (i + 1) w (KT X i φ))
      (X.fm.S i w) (X.fm.S (i + 1) w)) {i : ℕ} (hi : i ≤ D.R.m) :
    Into X w (fun φ => (X.A.T : ℂ) ^ (i * e + s * (VVT X w).card * ∑ j ∈ Finset.range (i + 1), j) •
      colUp X i ((Uprod X 0 w ^ i) φ)) (X.fm.S 0 w) (X.fm.S i w) := by
  induction i with
  | zero => intro x hx; exact ⟨x, hx, by simp [colUp]⟩
  | succ i ih =>
    have hi' : i < D.R.m := hi
    intro x hx
    obtain ⟨y, hy, hy'⟩ := ih hi'.le x hx
    obtain ⟨z, hz, hz'⟩ := hU i hi' y hy
    refine ⟨z, hz, ?_⟩
    have hm := Upow_mem hF w i (emb_mem X 0 x)
    have key := Uprod_colUp hF h4 hs hi w hm
    have e1 : colUp X (i + 1) ((Uprod X 0 w ^ i) (X.fm.emb 0 x)) =
      KT X i (colUp X i ((Uprod X 0 w ^ i) (X.fm.emb 0 x))) := rfl
    rw [hz']
    beta_reduce at hy' ⊢
    rw [hy', map_smul, map_smul, ← e1, key, pow_succ' (Uprod X 0 w) i, Module.End.mul_apply, tpow,
      smul_smul, smul_smul, ← pow_add, ← pow_add, Finset.sum_range_succ _ (i + 1)]
    congr 2
    ring

theorem card_VVT {w : D.what₂.places.Pl} (h : X.fm.seenP w = true) : (VVT X w).card = (tops D).card := by
  unfold VVT
  rw [if_pos h]
  refine Finset.card_bij (fun v _ => X.fm.tauOf w v) (fun v hv => (Finset.mem_filter.1 hv).2)
    (fun a _ b _ hab => (X.fm.tauOf w).injective hab) (fun τ hτ => ?_)
  exact ⟨(X.fm.tauOf w).symm τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hτ⟩, by simp⟩

theorem expT_nonneg (hW : WtBounds X) (w : D.what₂.places.Pl) : 0 ≤ expT X w := by
  refine mul_nonneg (Int.natCast_nonneg _) (Finset.sum_nonneg fun v hv => hW.1 _ ?_)
  unfold VVT at hv
  split_ifs at hv
  · exact (Finset.mem_filter.1 hv).2
  · simp at hv

theorem val_pow {w : D.what₂.places.Pl} (hw : OverT X w) (k : ℕ) :
    D.what₂.places.val w ((X.A.T : D.what₂.LL) ^ k) = (((D.what₂.places.ramIdx w * k : ℕ) : ℤ) : WithTop ℤ) := by
  have h := D.what₂.places.val_resChar w
  rw [show D.what₂.places.resChar w = X.A.T from hw] at h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1

theorem quot_mem {w : D.what₂.places.Pl} (hw : OverT X w) {c : D.what₂.LL} {n : ℤ}
    (hc : D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ)) (a b : ℕ)
    (h : ((D.what₂.places.ramIdx w * b : ℕ) : ℤ) ≤ n) :
    c * (X.A.T : D.what₂.LL) ^ a * ((X.A.T : D.what₂.LL) ^ b)⁻¹ ∈ Ow D w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hc, val_pow hw, val_pow hw]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  have : (0 : ℤ) ≤ ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) := Int.natCast_nonneg _
  exact_mod_cast (by omega : (0 : ℤ) ≤ n + ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) + -((D.what₂.places.ramIdx w * b : ℕ) : ℤ))

theorem loss_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) (w : D.what₂.places.Pl) :
    ((D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      s * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) = (D.R.m : ℝ) * ET X w := by
  unfold ET
  by_cases h : X.fm.seenP w = true
  · rw [if_pos h, if_pos h, card_VVT h]
    unfold ETpi
    have h1 : ((D.R.t : ℝ) + 1) = 2 * s := by exact_mod_cast hs
    have h2 : ((∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) * 2 = ((D.R.m : ℝ) + 1) * D.R.m := by
      have := Finset.sum_range_id_mul_two (D.R.m + 1)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    rw [h1]
    generalize (∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) = S at h2 ⊢
    push_cast
    linear_combination ((s : ℝ) * ((tops D).card : ℝ) / 2) * h2
  · have : VVT X w = ∅ := by unfold VVT; rw [if_neg h]
    rw [if_neg h, if_neg h, this]
    simp

end ColSharp


open ColSharp in
theorem levelChainSharpColumnValuation_of_stability : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u),
    FormsStable X → LevelChainUOperatorCommutation X → UKSharp X → WtBounds X → Conclusion5Sharp X := by
  intro D u X hF h4 hU hW w hw c n hc hn x' hx'
  obtain ⟨x, hx, hxx⟩ := hx'
  obtain ⟨s0, hs0⟩ := D.R.t_odd
  have hs : D.R.t + 1 = 2 * (s0 + 1) := by omega
  obtain ⟨y, hy, hy'⟩ := chain_into hF h4 hs w _ (hU w hw) (le_refl D.R.m) x hx.1
  rw [← loss_eq (X := X) hs w] at hn
  set b := D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      (s0 + 1) * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j with hb
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (expT_nonneg hW w)
  have hmem := quot_mem hw hc a b (by exact_mod_cast hn)
  refine ⟨(⟨_, hmem⟩ : Ow D w) • y, (X.fm.S D.R.m w).smul_mem _ hy, ?_⟩
  have hT : (X.A.T : ℂ) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast X.A.T_prime.ne_zero)
  beta_reduce at hy' ⊢
  rw [Subring.smul_def, LinearMap.map_smulₛₗ, hy', hxx, colT_eq, ha, LinearMap.smul_apply, map_smul,
    smul_smul, smul_smul, zpow_natCast]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  field_simp

end GlobalTheory.LvT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dite_eq_right hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dite_eq_left hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

end GlobalTheory.LvT.TwColumn
