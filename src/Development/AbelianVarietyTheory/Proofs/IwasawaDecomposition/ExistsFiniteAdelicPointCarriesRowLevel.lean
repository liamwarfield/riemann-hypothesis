module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem cong_zsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℤ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  rw [← Finset.sum_sub_distrib]
  refine W.sum_mem fun l _ => ?_
  have h1 : ((a l - a' l : ℤ) : ZMod g) = 0 := by push_cast; rw [h l, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]
  exact W.zsmul_mem (hu l) t

theorem cong_nsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℕ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  have := cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)
  simpa only [natCast_zsmul] using this

theorem sum_nsmul_sum {V : Type*} [AddCommGroup V] {r : ℕ} (u : Fin r → V) (a : Fin r → ℕ)
    (b : Fin r → Fin r → ℕ) :
    ∑ j, a j • ∑ l, b l j • u l = ∑ l, (∑ j, a j * b l j) • u l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rebase_rel {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (F : V →+ V) (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (M c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1)
    (h : ∀ i, F (u i) - ∑ j, (M j i).val • u j ∈ W) (i : Fin r) :
    F (∑ j, (c j i).val • u j) - ∑ m, ((d * M * c) m i).val • ∑ l, (c l m).val • u l ∈ W := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_nsmul]
  have e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) +
      ∑ j, (c j i).val • ∑ l, (M l j).val • u l := by
    rw [← Finset.sum_add_distrib]; congr 1; funext j; rw [← smul_add, sub_add_cancel]
  rw [e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]
  refine W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)
  have e2 : c * (d * M * c) = M * c := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]
  have e3 := congrFun (congrFun e2 l) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at e3
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem rebase_span {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1) (a : Fin r → ℤ) :
    ∃ e : Fin r → ℤ, ∑ j, a j • u j - ∑ m, e m • ∑ j, (c j m).val • u j ∈ W := by
  refine ⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩
  have e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j =
      ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j := by
    simp only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  refine cong_zsmul W u hu _ _ fun j => ?_
  have e2 := congrFun (congrFun hcd j) j
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hcd]
  simp [Matrix.one_apply]

variable {D : D7}

theorem incl_sum_nsmul (X : HidaSetting D) {r : ℕ} (a : Fin r → ℕ) (x : Fin r → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j, a j • x j) = ∑ j, a j • incl X.B.I (x j) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp [incl, map_sum, map_nsmul, Finset.sum_apply]

theorem incl_nsmul (X : HidaSetting D) (a : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (a • x) = a • incl X.B.I x := by
  funext t
  simp [incl, map_nsmul]

theorem nsmul_mem_wLat (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    g • y ∈ wLat X w := by
  apply Submodule.subset_span
  refine ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩

theorem incl_mem_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {y : Fin X.B.I.n → X.B.I.E}
    (hy : y ∈ wLat X w) : incl X.B.I y ∈ wLf X w :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem fixRed_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  intro D X red b c hg hf
  classical
  refine ⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨⟨hbL, hbspan⟩, hrel⟩ := hf kv
  have hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.mul_inv (c kv)
  have hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup :=
    fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)
  refine ⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _
  · obtain ⟨a, ha⟩ := hbspan y hy
    obtain ⟨e, he⟩ := rebase_span _ (b kv) hgL _ _ hcd a
    refine ⟨e, ?_⟩
    have h2 := Submodule.add_mem _ ha he
    simp only [Int.cast_smul_eq_zsmul] at h2 ⊢
    rwa [sub_add_sub_cancel] at h2
  · have hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun j => by
      rw [← incl_nsmul]; exact incl_mem_wLf X _ (hgL j)
    have hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) -
        ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈
        (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun i => by
      have := hrel k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this
    have key := rebase_rel _ _ _ hu _ _ _ hcd hM i
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key
    simp only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
    exact key

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFixedBasisReductionMap_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  first | exact @GlobalTheory.Mem.SRe.fixRed_conj | exact GlobalTheory.Mem.SRe.fixRed_conj | (intros; apply GlobalTheory.Mem.SRe.fixRed_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_baseLevel_iff_finiteGroup_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ↔ g0 ∈ P.H := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
    rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H) ↔ _
  rw [e]
  exact ⟨fun hk => hk.2.2, fun hg => ⟨hl.1, hl.2.1, hg⟩⟩

theorem baseLevelCharacter_eq_blockCharacter_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hg : g0 ∈ P.H) :
    levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = ((P.chi ⟨g0, hg⟩ : ℂˣ) : ℂ) := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  have e2 : levFn (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) := by
    show ext1 P.H P.chi _ * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ = _
    simp
  unfold levChi
  rw [e2, e, extendOne_of_mem _ hg]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_triv (R : RealDat D A Ks) (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ = 1 := by
  unfold levChi
  show ((ext1 (⊤ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊤ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
    (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
  unfold ext1
  split_ifs <;> simp

theorem hasType_flag1 (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (F : GA D (Yc D 0) → ℂ)
    (hF : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P), ∀ g, F (g * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k * F g) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F := by
  intro κ hκ g
  have h1 : κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))) := hκ
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h1.2.2
  have hJ : κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) := by
    show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H)
    rw [e]
    exact ⟨h1.1, h1.2.1, P.H.one_mem⟩
  have c1 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = 1 := by
    unfold levChi
    show ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    rw [e]
    have h2 : ext1 P.H (⇑P.chi) (1 : G0 R.Pg D.R.r) = 1 := blockDiagonalExtendByOnePrimeField_one P.H P.chi
    erw [h2]
    simp
  have c2 : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) κ = 1 := by
    unfold levChi
    show ((ext1 (⊥ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊥ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    unfold ext1
    split_ifs <;> simp
  rw [hF κ hJ g, c1, c2]

theorem mult_act_of_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)),
      ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
        (T : MMap (MP R)) v (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 ((T : MMap (MP R)) v) g := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    intro v g
    have hF := hasType_flag1 R P (T v) (fun k hk g' => hT.lev v k hk g')
    have := level_action_spec hF ⟨κ, hl⟩ κ hl g
    show T v (g * κ) = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T v) g
    rw [this, levChi_flag_triv, inv_one, one_mul]
  | zero =>
    intro v g
    show (0 : GA D (Yc D 0) → ℂ) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (0 : GA D (Yc D 0) → ℂ) g
    rw [map_zero]
    rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro v g
    show (T₁ v + T₂ v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T₁ v + T₂ v) g
    rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h₁ v g, h₂ v g]
  | smul a T _ hT =>
    intro v g
    show (a • T v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (a • T v) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hT v g]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem isRedHom_conj {D : D7} {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (c : G0g D.nd) (hred : IsRedHom X red)
    (hf : FixRed X (fun k => c⁻¹ * red k * c) b') : IsRedHom X (fun k => c⁻¹ * red k * c) := by
  refine ⟨goodAt_of_fixRed hf, fun k hk k' hk' => ?_, fun γ => ?_, fun k hk => ?_⟩
  · simp only [hred.2.1 k hk k' hk', mul_assoc, mul_inv_cancel_left]
  · obtain ⟨k, hk, e⟩ := hred.2.2.1 (c * γ * c⁻¹)
    exact ⟨k, hk, by simp only [e]; group⟩
  · rw [← hred.2.2.2 k hk]
    show c⁻¹ * red k * c = 1 ↔ red k = 1
    constructor
    · intro e
      calc red k = c * (c⁻¹ * red k * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e; rw [e]; group

theorem seeAt_exists : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h hι hL hlev hpin hE
  obtain ⟨eR, plg, iso, hpl, he, hdiv, heG⟩ := hpin
  obtain ⟨ψ0, hgen, -, π, hπ, hmem, hchi⟩ := hlev
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    intro kv
    have := D.naut.plGw_over kv.1 kv.2
    simp [placesOver] at this
    exact this
  obtain ⟨t₀, ht₀, red, b, hred, hfix, hlift, hcover⟩ := GlobalTheory.Mem.SRe.TrPt.exists_trans D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG
  obtain ⟨c, hc⟩ := GlobalTheory.T.conj_level_conjCharacter_symmetricLevel D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG ψ0 hgen π hπ red b hred hfix hgw
  obtain ⟨b', hfix'⟩ := GlobalTheory.T.isFixedBasisReductionMap_conj D X red b c hgw hfix
  obtain ⟨kc, hkc, hkcv⟩ := hred.2.2.1 c
  have hK : ∀ x, x ∈ X.B.I.Kset ↔ x ∈ GlobalTheory.RowLev.Inhab.Ksub X.B.I := fun x => Iff.rfl
  have hmul := hred.2.1
  have red_one : red 1 = 1 := by
    have e := hmul 1 ((hK 1).2 (Subgroup.one_mem _)) 1 ((hK 1).2 (Subgroup.one_mem _))
    rw [mul_one] at e
    exact left_eq_mul.mp e
  have red_inv : ∀ x ∈ X.B.I.Kset, red x⁻¹ = (red x)⁻¹ := by
    intro x hx
    have hx' : x⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK x).1 hx))
    have e := hmul x⁻¹ hx' x hx
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have memK : ∀ k ∈ X.B.I.Kset, kc⁻¹ * k * kc ∈ X.B.I.Kset := fun k hk =>
    (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hK _).1 hkc)) ((hK _).1 hk)) ((hK _).1 hkc))
  have red_conj : ∀ k ∈ X.B.I.Kset, red (kc⁻¹ * k * kc) = c⁻¹ * red k * c := by
    intro k hk
    have hkc' : kc⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK _).1 hkc))
    have h1 : kc⁻¹ * k ∈ X.B.I.Kset := (hK _).2 (Subgroup.mul_mem _ ((hK _).1 hkc') ((hK _).1 hk))
    rw [hmul _ h1 _ hkc, hmul _ hkc' _ hk, red_inv _ hkc, hkcv]
  obtain ⟨t, ht⟩ : ∃ t : GA D (D.sp.Y 0), t = (iotaX X h).symm (1, kc) * t₀ := ⟨_, rfl⟩
  have hkap : ∀ k, kap X h t k = kap X h t₀ (kc⁻¹ * k * kc) := by
    intro k
    have e : ((1 : X.B.I.Ginf), kc⁻¹ * k * kc) = ((1, kc) : X.B.I.GA)⁻¹ * (1, k) * (1, kc) := by
      ext <;> simp
    show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) =
      t₀⁻¹ * (iotaX X h).symm (1, kc⁻¹ * k * kc) * t₀
    rw [e, map_mul, map_mul, map_inv, ht]
    group
  set red' : X.B.I.Gf → G0g D.nd := fun k => c⁻¹ * red k * c with hred'def
  have hred' : IsRedHom X red' := isRedHom_conj c hred hfix'
  have hliftT : ∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red' k))) (kap X h t k) := by
    intro k hk
    rw [hkap, hred'def]
    simp only
    rw [← red_conj k hk]
    exact hlift _ (memK k hk)
  have key : ∀ k ∈ X.B.I.Kset, (kap X h t k ∈ JR R F ↔ k ∈ X.K2) ∧
      ∀ hJ : kap X h t k ∈ JR R F, chiR R F (kap X h t k) = star (X.chi2 k) := by
    intro k hk
    have hl := hliftT k hk
    have hiff := mem_baseLevel_iff_finiteGroup_lift R (R.levR F true) hl
    have hc1 := (hc k hk).1
    refine ⟨?_, fun hJ => ?_⟩
    · rw [show kap X h t k ∈ JR R F ↔ _ from hiff, hmem, hc1]
    · have hg : R.eG (eR.symm (red' k)) ∈ (R.levR F true).H := hiff.1 hJ
      have hg' : reord π (R.eG (eR.symm (red' k))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H := (hmem _).1 hg
      show levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = _
      rw [baseLevelCharacter_eq_blockCharacter_lift R (R.levR F true) hl hg, hchi _ hg hg']
      exact (hc k hk).2 hg'
  have hio : ∀ k, iotaX X h ((iotaX X h).symm (1, k)) = (1, k) := fun k => (iotaX X h).apply_symm_apply _
  have hconjEq : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ = (iotaX X h).symm (1, k) := by
    intro k
    group
  have hK2K : ∀ k ∈ X.K2, k ∈ X.B.I.Kset := fun k hk => hk.1
  refine ⟨t, ⟨?_, ?_, eR.symm, red', ?_, ⟨hred', ?_⟩, ?_⟩⟩
  · have e : t = t₀ * (t₀⁻¹ * (iotaX X h).symm (1, kc) * t₀) := by rw [ht]; group
    rw [e]
    exact Subgroup.mul_mem _ ht₀ (hlift kc hkc).1
  · intro y
    have hJ' : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X ↔ k ∈ X.K2 := by
      intro k
      rw [hconjEq, Set.mem_preimage, hio]
      exact ⟨fun hh => hh.2, fun hh => ⟨rfl, hh⟩⟩
    have hy : y ∈ JR R F ∨ (t⁻¹)⁻¹ * y * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X → ∃ k ∈ X.B.I.Kset, y = kap X h t k := by
      rintro (hy | hy)
      · have hyF : y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := ⟨hy.1, hy.2.1, Subgroup.mem_top _⟩
        obtain ⟨k', hk', e⟩ := hcover y hyF
        refine ⟨kc * k' * kc⁻¹, (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hK _).1 hkc) ((hK _).1 hk'))
          (Subgroup.inv_mem _ ((hK _).1 hkc))), ?_⟩
        rw [hkap, e]
        congr 1
        group
      · have h2 : (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).1 = 1 ∧ (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2 ∈ X.K2 := hy
        refine ⟨(iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2, h2.2.1, ?_⟩
        have e : (iotaX X h).symm (1, (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2) = (t⁻¹)⁻¹ * y * t⁻¹ := by
          rw [← h2.1]
          exact (iotaX X h).symm_apply_apply _
        show y = (t⁻¹ * (iotaX X h).symm (1, _) * t : GA D (D.sp.Y 0))
        rw [e]
        group
    refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      exact (hJ' k).2 ((key k hk).1.1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inr h1)
      exact (key k hk).1.2 ((hJ' k).1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      rw [(key k hk).2 h1]
      show adelicCharacterOfHidaSetting X (iotaX X h ((t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹)) = _
      rw [hconjEq, hio]
      rfl
  · intro k hk
    have hkK := hK2K k hk
    have hJ := (key k hkK).1.2 hk
    exact ⟨hJ, (key k hkK).2 hJ⟩
  · intro k hk T hT v g
    exact mult_act_of_lift R (R.levR F true) (hliftT k hk) T hT v g
  · intro γ
    show star (D.ntypes.e0.coeff γ) = D.what₂.embLL ((idemOf A.X).coeff (eR.symm γ))
    rw [he, MulEquiv.apply_symm_apply, hE γ]

end GlobalTheory.Mem.SRe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdelicPointCarriesRowLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  first | exact @GlobalTheory.Mem.SRe.seeAt_exists | exact GlobalTheory.Mem.SRe.seeAt_exists | (intros; apply GlobalTheory.Mem.SRe.seeAt_exists <;> assumption)
end
