module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeesawDatumEqLatticePairOverVacuumStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSrcSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem col_mem_SB {n n' : Type} {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (hΨ : Ψ ≠ 0) : a ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ x₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hΨ (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun y : n → k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => fun i => x i (Sum.inr 0)) ?_ (by fun_prop) (fun y => rfl)
  · have e : a = (Ψ x₀)⁻¹ • fun y : n → k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j) := by
      funext y
      show a y = (Ψ x₀)⁻¹ * (Ψ x₀ * a y)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_const
    · exact (continuous_apply i)

theorem sb_of_sbHalf (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x => Φ (HalfInd.wr α β x)) ∈ SB (Matrix n n' k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUc, hUo⟩ := HalfInd.compact_open α β hS hT
  set U := {x : Matrix n n' k | HalfInd.wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧
    IsHalf p.e (HalfInd.wr α β x)} with hU
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix n n' k, HalfInd.wr α β (((k0 : ℕ) : k) • z) = k0 • HalfInd.wr α β z := by
    intro z
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      refine ⟨?_, HalfInd.isHalf_wr α β 0⟩
      rw [map_zero]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (HalfInd.wr α β x') = Φ (HalfInd.wr α β x)
      rw [hx'z, map_add (f := _), hwr]
      exact hinv _ hx'.1 hx'.2 _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      refine ⟨?_, HalfInd.isHalf_wr α β _⟩
      rw [hwr]; exact h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem extFun_wr (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {Φ : WO S T → ℂ} (hΦ : ∀ t, Φ t ≠ 0 → IsHalf p.e t) :
    extFun α β (fun x => Φ (HalfInd.wr α β x)) = Φ := by
  classical
  funext t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    beta_reduce
    rw [HalfInd.wr_rd α β ht]
  · rw [if_neg ht]
    by_contra h
    exact ht (hΦ t (Ne.symm h))

end GlobalTheory.LastSrcSlice

namespace GlobalTheory.LastSrcSlice

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ _ α α₀ β hsum Ψ a ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  by_cases hΨ0 : Ψ = 0
  ·
    subst hΨ0
    have hext : extFun α₀ β (tensCol (0 : Matrix n n' k → ℂ) a) = 0 := by
      classical
      funext t
      simp [extFun, tensCol]
    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = 0 := by
      rw [hΞT, hext, map_zero]; rfl
    have hheis0 : ∀ (w : WO A S), heisO ψ A S w (0 : WO A S → ℂ) = 0 := by
      intro w; funext x; simp [heisO]
    refine ⟨0, hLA, hLS, ⟨?_, ?_⟩, Submodule.zero_mem _, ⟨0, ?_⟩, fun T' hT' => ?_⟩
    · exact { quasi := fun γ w => by simp
              level := ⟨⊤, isOpen_univ, fun u _ _ => hheis0 u⟩
              cont := continuous_const
              smooth := fun _ _ _ _ _ => by simpa using contDiff_const }
    · exact ⟨fun u _ => hheis0 _, fun _ _ u _ _ => hheis0 u⟩
    · exact ⟨fun Φ _ x _ => by simp [hheis0], fun Φ _ y' _ => by simp [hheis0], by simp⟩
    · rw [hslice]
      have : extFun α β (0 : Matrix n n' k → ℂ) = 0 := by
        classical
        funext t; simp [extFun]
      beta_reduce
      rw [this, map_zero]
  · have haSB : a ∈ SB (n → k) := col_mem_SB hSB hΨ0
    have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
    set r := o.resS S with hr
    set a' := ExtZero.colFun β ζ a with ha'
    set ΛA := latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛA
    set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
    set T₁ := ExtZero.restrModel r a' T y with hT₁
    set g := T₁ (halfInd p.e ΛA) with hg
    have hbox : ∀ Φ : WO A S → ℂ, (fun t => Φ (r t).1 * a' (r t).2) = o.boxS S Φ a' := fun Φ => rfl

    have hsb : ∀ Φ, IsSBHalf p.e ΛA Φ → IsSBHalf p.e Λ₁ (fun t => Φ (r t).1 * a' (r t).2) := by
      intro Φ hΦ
      have h1 := sb_of_sbHalf p α β hLA hLS hΦ
      have h2 := extFun_wr p α β (Φ := Φ) hΦ.1
      rw [hbox, ← h2, ← GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem h1 haSB)

    have hmodel : IsPlaceModel ψ (symplO A S) (heisO ψ A S) p.e ΛA 1 g T₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * a' (r t).2) =
            fun t => (fun t => Φ (r t).1 * a' (r t).2) (t + r.symm (x, 0)) := by
          funext t
          simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
        rw [hfun, hT.trans _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hx), hr, ExtZero.heisO_resS_symm]
        rfl
      · intro Φ hΦ y' hy'
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => ψ (symplO A S t y') * Φ t) (r t).1 * a' (r t).2) =
            fun t => ψ (symplO V₀ S t (r.symm (y', 0))) * (fun t => Φ (r t).1 * a' (r t).2) t := by
          funext t
          rw [hr, ExtZero.symplO_resS_symm, mul_assoc]
        rw [hfun, hT.modul _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hy'), hr, ExtZero.heisO_resS_symm]
        rfl
      · rw [one_smul]

    have hlat : IsLatVac (heisO ψ A S) ΛA g :=
      Rebase.latVac_image D k p ψ hψ A S LA LA LS LS hLA hLS hLA hLS g T₁ hmodel

    have htheta : IsThetaFunO ψ A S g := by
      obtain ⟨ΨA, hΨA, hΨAe⟩ := HalfInd.exists_SB_extFun_eq_halfInd D k p A S n n' α β LA LS hLA hLS
      have hover := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).1
      obtain ⟨F, hF, -⟩ := hover _ (Comm.tensCol_mem hΨA haSB)
      have hFth := ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).2.1 _ _ hF).1
      have hFT : F = T (extFun α₀ β (tensCol ΨA a)) := hF.2.2.2.2.2 T hT
      rw [GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum, hΨAe] at hFT
      have := GlobalTheory.BoxSlice.isThetaFunO_slice_left o hFth y
      rw [hFT] at this
      exact this
    have hvac : Vac ψ A S LA LS (· = p.v) g := ⟨htheta, hlat⟩

    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = T₁ (extFun α β Ψ) := by
      funext u
      rw [ExtZero.restrModel_apply, hΞT, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      rfl
    refine ⟨g, ?_⟩
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ A S α β LA LS hLA hLS g hvac).1 Ψ hΨSB
    have hfT₁ : f = T₁ (extFun α β Ψ) := hf.2.2.2.2.2 T₁ hmodel
    rw [hslice, ← hfT₁]
    exact hf

end GlobalTheory.LastSrcSlice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  first | exact @GlobalTheory.LastSrcSlice.main | exact GlobalTheory.LastSrcSlice.main | (intros; apply GlobalTheory.LastSrcSlice.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.LastSeeSawDatum

section Helpers

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem comb_apply' {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isThetaFunO_add' {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    funext w
    have h1 := congrFun (hU u hu.1 hi) w
    have h2 := congrFun (hU' u hu.2 hi) w
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem heisO_smul' {S T : HSp D} (u : WO S T) (r : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (r • f) = r • heisO ψ S T u f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_add' {S T : HSp D} (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem heisO_zero' {S T : HSp D} (u : WO S T) : heisO ψ S T u (0 : WO S T → ℂ) = 0 := by
  funext w; simp only [heisO, Pi.zero_apply, mul_zero]

theorem isThetaFunO_zero' (S T : HSp D) : IsThetaFunO ψ S T (0 : WO S T → ℂ) := {
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' u⟩
  cont := continuous_const
  smooth k L hL hfin w := by simp only [Pi.zero_apply]; exact contDiff_const }

theorem isThetaFunO_smul' {S T : HSp D} (r : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (r • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul', hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hf.smooth k L hL hfin w) }

variable {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}

theorem vac_zero : Vac ψ S T LS LT P 0 :=
  ⟨isThetaFunO_zero' S T, fun u _ => heisO_zero' _, fun e _ u _ _ => heisO_zero' _⟩

theorem vac_add {f g : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (hg : Vac ψ S T LS LT P g) :
    Vac ψ S T LS LT P (f + g) :=
  ⟨isThetaFunO_add' hf.1 hg.1, fun u hu => by rw [heisO_add', hf.2.1 u hu, hg.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_add', hf.2.2 e he u hu hu', hg.2.2 e he u hu hu']⟩

theorem vac_smul (r : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (r • f) :=
  ⟨isThetaFunO_smul' r hf.1, fun u hu => by rw [heisO_smul', hf.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_smul', hf.2.2 e he u hu hu']⟩

theorem vac_sum {ι : Type} (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, Vac ψ S T LS LT P (f i)) : Vac ψ S T LS LT P (∑ i ∈ s, r i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (vac_zero : Vac ψ S T LS LT P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vac_add (vac_smul _ (h a (Finset.mem_insert_self a s))) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comb_smul_fun (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext u
  simp only [comb_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem comb_sum_fun {ι : Type} (c : WO S T →₀ ℂ) (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ) :
    comb ψ S T c (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • comb ψ S T c (f i) := by
  funext u
  simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem comb_swap {A S X : HSp D} (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) (G : WO A S → WO S X → ℂ)
    (u : WO A S) (x : WO S X) :
    comb ψ S X c' (fun x' => comb ψ A S c (fun u' => G u' x') u) x =
      comb ψ A S c (fun u' => comb ψ S X c' (G u') x) u := by
  simp only [comb_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Helpers

theorem lastDatum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hIC n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum D k p q ψ hψ hU χ hχ hIC n n' n'' V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LA LS LT LX hLA hLS hLT hLX hβQ hγΛ c c' hc hc' hcv hcv'
  obtain ⟨e, he, heP⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p n n' ψ hψ hU A S α β LA LS hLA hLS Ψ c hc hcv
  obtain ⟨e', he', heP'⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p (n'' ⊕ Fin 1) n ψ hψ hU S X β γ₀ LS LX hLS hLX _ c' hc' hcv'
  refine ⟨e, e', he, he', ?_⟩
  intro L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂
  have ha : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have hev : Q.ev 0 = 0 := by
      unfold Pair.ev
      rw [dite_eq_left Q.lat.zero_mem]
      exact map_zero Q.fn
    have h0 := congrFun h 0
    simp only [charInd, vecInd, hev, neg_zero, AddChar.map_zero_eq_one, Q.lat.zero_mem, if_true, mul_one,
      Pi.zero_apply] at h0
    exact one_ne_zero h0
  have hA : ∀ y : WO L S, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) ∧
      comb ψ A S c (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) = fun u => Ξ ((o.resS S).symm (u, y)) := by
    intro y
    obtain ⟨g, hg⟩ := GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ _ ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
    exact heP g _ hg
  have hcol : ∀ x, (fun u => lastBi o o'' τ Ξ Φ₂ u x) =
      Φ₂ (o''.resT S x).1 • fun u => Ξ ((o.resS S).symm (u, kap τ S (o''.resT S x).2)) := by
    intro x; funext u; rfl
  have hAc : ∀ x, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) ∧
      comb ψ A S c (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) = fun u => lastBi o o'' τ Ξ Φ₂ u x := by
    intro x
    rw [hcol x, comb_smul_fun, comb_smul_fun]
    exact ⟨vac_smul _ (hA _).1, by rw [(hA _).2]⟩
  have hX : ∀ u, Vac ψ S X LS LX (· = p.v) (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) ∧
      comb ψ S X c' (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) = lastBi o o'' τ Ξ Φ₂ u := by
    intro u
    obtain ⟨g, hg⟩ := hε α α₀ β γ γ₀ hα hγ Q Λ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
    exact heP' g _ hg
  generalize lastBi o o'' τ Ξ Φ₂ = C at hAc hX ⊢
  refine ⟨⟨fun x => ?_, fun u => ?_⟩, ?_⟩
  · have e1 : (fun u' => comb ψ S X e' (C u') x) =
        ∑ j ∈ e'.support, (e' j * ψ (symplOH S X x j)) • fun u' => C u' (x + j) := by
      funext u'
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u' => comb ψ S X e' (C u') x))
    rw [e1, comb_sum_fun]
    exact vac_sum _ _ _ fun j _ => (hAc (x + j)).1
  · have e2 : (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u) =
        ∑ i ∈ e.support, (e i * ψ (symplOH A S u i)) • comb ψ S X e' (C (u + i)) := by
      funext x
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ S X LS LX (· = p.v) (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u)
    rw [e2]
    exact vac_sum _ _ _ fun i _ => (hX (u + i)).1
  · funext u x
    have hsw : ∀ u', comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x =
        comb ψ A S e (fun u'' => C u'' x) u' := by
      intro u'
      have h1 := comb_swap (ψ := ψ) e c' (fun u'' x' => comb ψ S X e' (C u'') x') u' x
      beta_reduce at h1
      rw [h1]
      congr 1
      funext u''
      exact congrFun (hX u'').2 x
    show C u x = comb ψ A S c (fun u' => comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x) u
    simp only [hsw]
    exact (congrFun (hAc x).2 u).symm

end GlobalTheory.LastSeeSawDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.LastSeeSawDatum (comb_apply' comb_smul_fun comb_sum_fun comb_swap vac_smul vac_sum) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  exact @_root_.GlobalTheory.LastSeeSawDatum.lastDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastTAllPf

variable {D : D7}

theorem vac_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {κ : Type*}
    (s : Finset κ) (a : κ → ℂ) (F : κ → WO S T → ℂ) (hF : ∀ i ∈ s, Vac ψ S T LS LT P (F i)) :
    Vac ψ S T LS LT P (fun w => ∑ i ∈ s, a i * F i w) := by
  refine ⟨GlobalTheory.SeeSawFold.theta_sum' s _ fun i hi => GlobalTheory.SeeSawFold.theta_const_mul' (a i) (hF i hi).1, ?_, ?_⟩
  · intro u hu
    funext w
    simp only [heisO, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := congrFun ((hF i hi).2.1 u hu) w
    simp only [heisO] at h
    rw [mul_left_comm, h]
  · intro e he u hu hh
    funext w
    simp only [heisO, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := congrFun ((hF i hi).2.2 e he u hu hh) w
    simp only [heisO] at h
    rw [mul_left_comm, h]

theorem vac_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} :
    Vac ψ S T LS LT P 0 := by
  have h := vac_sum (ψ := ψ) (LS := LS) (LT := LT) (P := P) (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) (by simp)
  convert h using 1 <;> funext w <;> simp

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem biVac_biComb_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {LA : Lat A}
    {LS : Lat S} {LA' : Lat A'} {Q P' : Pl D → Prop} (hd : ∀ x, Q x → ¬ P' x) {d : WO A S →₀ ℂ} {d' : WO S A' →₀ ℂ}
    (hd1 : CombAt Q d) (hd2 : CombAt Q d') {Y : WO A S → WO S A' → ℂ} (hY : BiVacAt ψ LA LS LA' P' Y) :
    BiVacAt ψ LA LS LA' P' (biComb ψ A S A' d d' Y) := by
  have M1 := GlobalTheory.DisjComb.main D ψ hψ A S Q P' hd
  have M2 := GlobalTheory.DisjComb.main D ψ hψ S A' Q P' hd
  constructor
  · intro v
    have hG : Vac ψ A S LA LS P' (fun u' => comb ψ S A' d' (Y u') v) := by
      have e : (fun u' => comb ψ S A' d' (Y u') v) =
          fun u' => ∑ y ∈ d'.support, (d' y * ψ (symplOH S A' v y)) * Y u' (v + y) := by
        funext u'
        simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [e]
      exact vac_sum d'.support (fun y => d' y * ψ (symplOH S A' v y)) (fun y u'' => Y u'' (v + y))
        fun y _ => hY.1 (v + y)
    exact (M1.2.1 d hd1).2 LA LS _ hG
  · intro u
    have e : biComb ψ A S A' d d' Y u =
        fun v => ∑ x ∈ d.support, (d x * ψ (symplOH A S u x)) * comb ψ S A' d' (Y (u + x)) v := by
      funext v
      simp only [biComb, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    exact vac_sum d.support (fun x => d x * ψ (symplOH A S u x)) (fun x => comb ψ S A' d' (Y (u + x)))
      fun x _ => (M2.2.1 d' hd2).2 LS LA' _ (hY.2 (u + x))

theorem vac_of_list {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ (l : List (Pl D)), l.Nodup → ∀ (P : Pl D → Prop), (∀ x, P x ↔ x ∈ l) →
      (∀ x ∈ l, Vac ψ S T LS LT (· = x) f) → Vac ψ S T LS LT P f := by
  intro l
  induction l with
  | nil =>
    intro _ P hP _
    have hb : latO S T (LS : Set _) (LT : Set _) P = ⊥ := by
      rw [latO, AddSubgroup.closure_eq_bot_iff]
      rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
      have h0 : α = 0 := RestrictedProduct.ext _ _ fun v => hα v fun h => by simpa using (hP v).1 h
      subst h0
      ext i j
      simp only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]
      exact TensorProduct.zero_tmul _ _
    have h0 : ∀ w : WO S T, symplOH S T w 0 = 0 := fun w => by simp [symplOH, symplO, hO]
    refine ⟨hf, fun u hu => ?_, fun e _ u hu _ => ?_⟩
    · rw [hb, AddSubgroup.mem_bot] at hu
      subst hu
      funext w
      simp [heisO, h0]
    · rw [hb, AddSubgroup.mem_bot] at hu
      subst hu
      funext w
      simp [heisO, h0]
  | cons x l ih =>
    intro hnd P hP hv
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hnd
    have e : P = fun y => y = x ∨ y ∈ l := funext fun y => propext ((hP y).trans List.mem_cons)
    subst e
    have M := (GlobalTheory.DisjComb.main D ψ hψ S T (· = x) (· ∈ l) (fun y hy hy' => hx (hy ▸ hy'))).2.2.2.2 LS LT f hLS hLT
    exact M.2 ⟨hv x List.mem_cons_self, ih hl (· ∈ l) (fun _ => Iff.rfl) fun y hy => hv y (List.mem_cons_of_mem _ hy)⟩


open GlobalTheory.SeeSawFold in
theorem biComb_eq_foldr_vac {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'}
    {P : Pl D → Prop} (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ)))
    (hc : ∀ f, Vac ψ A S LA LS P f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f)
    (hc' : ∀ f, Vac ψ S A' LS LA' P f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f)
    (Y : WO A S → WO S A' → ℂ) (hY : BiVacAt ψ LA LS LA' P Y) :
    biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hY.2 u), foldR_apply]
  have vac_opR : ∀ (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ), (∀ v, Vac ψ A S LA LS P (fun u => C u v)) →
      ∀ v, Vac ψ A S LA LS P (fun u => opR ψ A S A' b C u v) := by
    intro b C hC v
    have e : (fun u => opR ψ A S A' b C u v) = fun u => ∑ y ∈ b.support, (b y * ψ (symplOH S A' v y)) * C u (v + y) := by
      funext u
      simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e]
    exact vac_sum b.support (fun y => b y * ψ (symplOH S A' v y)) (fun y u => C u (v + y)) fun y _ => hC (v + y)
  have vac_foldR : ∀ (l' : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) v,
      Vac ψ A S LA LS P (fun u => l'.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
    intro l'
    induction l' with
    | nil => exact fun v => hY.1 v
    | cons p l' ih => exact vac_opR p.2 _ ih
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (vac_foldR l v)) u

section Lists

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_cons' {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem overAll_steps : ∀ (J : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ J f f' →
    ∀ j ∈ J, ∃ g g', Over ψ (α j) (β j) LS LT g (Ψ j) g' := by
  intro J
  induction J with
  | nil => intro _ _ _ j hj; simp at hj
  | cons i J ih =>
    intro f f' h j hj
    obtain ⟨g, hg, h⟩ := overAll_cons'.1 h
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨g, f', h⟩
    · exact ih f g hg j hj

theorem vac_foldr_off (hψ : IsStdChar D ψ (-1)) {x : Pl D} {κ : Type} (r : κ → WO S T →₀ ℂ) (P' : κ → Pl D → Prop)
    (l : List κ) (hr : ∀ j ∈ l, CombAt (P' j) (r j)) (hd : ∀ j ∈ l, ¬ P' j x) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (· = x) f) : Vac ψ S T LS LT (· = x) (l.foldr (fun j f' => comb ψ S T (r j) f') f) := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (P' j) (· = x) (fun y hy hy' => hd j List.mem_cons_self (hy' ▸ hy))
    exact (M.2.1 (r j) (hr j List.mem_cons_self)).2 LS LT _
      (ih (fun j' hj' => hr j' (List.mem_cons_of_mem _ hj')) fun j' hj' => hd j' (List.mem_cons_of_mem _ hj'))

theorem overAll_foldr (hψ : IsStdChar D ψ (-1)) (hinj : Function.Injective fun i => (p i).v) (r : ι → WO S T →₀ ℂ)
    (hr1 : ∀ i, CombAt (· = (p i).v) (r i))
    (hr2 : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Ψ i) (comb ψ S T (r i) f₀)) :
    ∀ (l : List ι), l.Nodup → ∀ f, (∀ i ∈ l, Vac ψ S T LS LT (· = (p i).v) f) →
      OverAll ψ α β LS LT Ψ l f (l.foldr (fun i f' => comb ψ S T (r i) f') f) := by
  intro l
  induction l with
  | nil => intro _ f _; exact rfl
  | cons i l ih =>
    intro hl f hf
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    refine overAll_cons'.2 ⟨_, ih hl' f fun j hj => hf j (List.mem_cons_of_mem _ hj), hr2 i _ ?_⟩
    exact vac_foldr_off hψ r (fun j => (· = (p j).v)) l (fun j _ => hr1 j)
      (fun j hj h => hi (by rw [hinj h]; exact hj)) (hf i List.mem_cons_self)

variable {I : List ι} {P : Pl D → Prop}

theorem comb_eq_foldr (hP : Places p I P) (hψ : IsStdChar D ψ (-1)) (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT)
    {c : WO S T →₀ ℂ} (hc : Reps ψ α β LS LT Ψ I P c) (r : ι → WO S T →₀ ℂ) (hr1 : ∀ i, CombAt (· = (p i).v) (r i))
    (hr2 : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Ψ i) (comb ψ S T (r i) f₀)) :
    ∀ f, Vac ψ S T LS LT P f → comb ψ S T c f = I.foldr (fun i f' => comb ψ S T (r i) f') f := by
  intro f hf
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hP n n' ψ hψ S T α β LS LT hLS hLT Ψ
  exact hAC.2.1 f _ _ (hc.2 f hf) (overAll_foldr hψ hP.inj r hr1 hr2 I hP.nodup f fun i _ =>
    vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) hf)

theorem over_of_overAll (hP : Places p I P) (hψ : IsStdChar D ψ (-1)) {f Ξ : WO S T → ℂ} (hf : Vac ψ S T LS LT P f)
    (hΞ : OverAll ψ α β LS LT Ψ I f Ξ) (i : ι) : ∃ g, Over ψ (α i) (β i) LS LT g (Ψ i) Ξ := by
  classical
  have hstep := overAll_steps I f Ξ hΞ
  obtain ⟨g0, g0', h0⟩ := hstep i (hP.all i)
  have hLS : IsSelfDualC S LS := h0.1
  have hLT : IsSelfDualC T LT := h0.2.1
  have hSB : ∀ j, Ψ j ∈ SB (Matrix n n' k) := fun j => by
    obtain ⟨g, g', h⟩ := hstep j (hP.all j)
    exact h.2.2.2.1
  choose r hr1 hr2 using fun j => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p j) n n' ψ hψ (hP.unit j) S T (α j) (β j) LS LS LT LT hLS hLT hLS hLT).2
    (Ψ j) (hSB j)
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hP n n' ψ hψ S T α β LS LT hLS hLT Ψ
  have hE : Ξ = I.foldr (fun j f' => comb ψ S T (r j) f') f := hAC.2.1 f _ _ hΞ
    (overAll_foldr hψ hP.inj r hr1 hr2 I hP.nodup f fun j _ => vac_mono (fun x hx => (hP.mem x).2 ⟨j, hx⟩) hf)
  have hcomm : ∀ x ∈ I, ∀ y ∈ I, ∀ z : WO S T → ℂ,
      comb ψ S T (r y) (comb ψ S T (r x) z) = comb ψ S T (r x) (comb ψ S T (r y) z) := by
    intro x _ y _ z
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact (GlobalTheory.DisjComb.main D ψ hψ S T (· = (p y).v) (· = (p x).v)
        (fun w h1 h2 => hxy (hP.inj (h2.symm.trans h1)))).1 (r y) (r x) (hr1 y) (hr1 x) z
  have hperm : I.Perm (i :: I.erase i) := List.perm_cons_erase (hP.all i)
  rw [hperm.foldr_eq' hcomm f, List.foldr_cons] at hE
  refine ⟨_, hE ▸ hr2 i _ ?_⟩
  refine vac_foldr_off hψ r (fun j => (· = (p j).v)) (I.erase i) (fun j _ => hr1 j) (fun j hj h => ?_)
    (vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) hf)
  exact ((hP.nodup.mem_erase_iff).1 hj).1 (hP.inj h).symm

end Lists

end GlobalTheory.LastTAllPf

namespace GlobalTheory.LastTAllPf


set_option maxHeartbeats 1000000 in
theorem main : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  intro D k _ _ _ _ ι p I P hP q ψ hψ χ hχ hchar n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hlam
    hunit hτ
  have hloc := fun i => GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace D k (p i) q ψ hψ (hP.unit i) (χ i) (hχ i) (hchar i) n n' n'' V₀ A L S X T L'' o o''
    ζ ζ₀ hζ hζ₀ τ lam hlam (hunit i) hτ
  choose ε hε using hloc
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hfr Q Λ _ Ψ LA LS LT LX L₁ hLA hLS hLT hLX hL₁ hlat c c' hc hc'
  have hdisj : ∀ i j, i ≠ j → ∀ x, x = (p i).v → ¬ x = (p j).v := fun i j h x h1 h2 => h (hP.inj (h1.symm.trans h2))
  have hSB : ∀ i, Ψ i ∈ SB (Matrix n n' k) := fun i => by
    obtain ⟨g, g', h⟩ := overAll_steps I 0 _ (hc.2 0 vac_zero) i (hP.all i)
    exact h.2.2.2.1
  have hSB' : ∀ i, phiOne (ε i • Q i) (lastPair q (Λ i)) ∈ SB _ := fun i => by
    obtain ⟨g, g', h⟩ := overAll_steps I 0 _ (hc'.2 0 vac_zero) i (hP.all i)
    exact h.2.2.2.1
  choose r hr1 hr2 using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hP.unit i) A S (α i) (β i) LA LA LS LS hLA hLS hLA
    hLS).2 (Ψ i) (hSB i)
  choose r' hr1' hr2' using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) (n'' ⊕ Fin 1) n ψ hψ (hP.unit i) S X (β i) (γ₀ i) LS LS LX LX
    hLS hLX hLS hLX).2 _ (hSB' i)
  choose e₁ e₂ he₁ he₂ hE using fun i => hε i (α i) (α₀ i) (β i) (γ i) (γ₀ i) (hfr i).1 (hfr i).2 (Q i) (Λ i) (Ψ i) LA LS
    LT LX hLA hLS hLT hLX (hlat i).1 (hlat i).2 (r i) (r' i) (hr1 i) (hr1' i) (hr2 i) (hr2' i)
  have hbc : ∀ i j, i ≠ j → ∀ (a b : WO A S →₀ ℂ) (a' b' : WO S X →₀ ℂ), CombAt (· = (p i).v) a →
      CombAt (· = (p i).v) a' → CombAt (· = (p j).v) b → CombAt (· = (p j).v) b' → ∀ C,
      biComb ψ A S X a a' (biComb ψ A S X b b' C) = biComb ψ A S X b b' (biComb ψ A S X a a' C) :=
    fun i j h a b a' b' ha ha' hb hb' C => GlobalTheory.ProdLocInv.biComb_comm ψ A S X a b a' b'
      ((GlobalTheory.DisjComb.main D ψ hψ A S _ _ (hdisj i j h)).1 a b ha hb)
      ((GlobalTheory.DisjComb.main D ψ hψ S X _ _ (hdisj i j h)).1 a' b' ha' hb') C
  let Vl : ι → Set (WO A S → WO S X → ℂ) := fun i => {C | BiVacAt ψ LA LS LX (· = (p i).v) C}
  let Cl : ι → Set (WO A S → WO S X → ℂ) := fun i => {C | biComb ψ A S X (e₁ i) (e₂ i) C ∈ Vl i ∧
    C = biComb ψ A S X (r i) (r' i) (biComb ψ A S X (e₁ i) (e₂ i) C)}
  let Dt : ι → Matrix n (n' ⊕ Fin 1) k → ℂ := fun i => tensCol (Ψ i) (charInd (resChar (χ i) (hχ i) q) (Q i))
  let Tp := {t : (WO V₀ S → ℂ) × (WO V₀ S → ℂ) × (WO S T → ℂ) // Vac ψ V₀ S L₁ LS P t.1 ∧
    OverAll ψ α₀ β L₁ LS Dt I t.1 t.2.1 ∧ Vac ψ S T LS LT P t.2.2}
  obtain ⟨e, e', hes, hes', hmain⟩ := GlobalTheory.ProdLocInv.main D ψ A S X ι Tp I
    (fun t => lastBi o o'' τ t.1.2.1 t.1.2.2) e₁ r e₂ r' Cl Vl hP.nodup
    (fun i _ i' _ hne => ⟨fun x hx y hy => GlobalTheory.DisjComb.symplO_disj (hdisj i i' hne) (hx.elim (he₁ i x) (hr1 i x))
      (he₁ i' y hy), fun x hx y hy => GlobalTheory.DisjComb.symplO_disj (hdisj i i' hne) (hx.elim (he₂ i x) (hr1' i x))
      (he₂ i' y hy)⟩)
    (fun i _ t => by
      obtain ⟨g, hg⟩ := over_of_overAll hP hψ t.2.1 t.2.2.1 i
      exact hE i L₁ LS g _ _ hg (vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) t.2.2.2))
    (fun i _ C hC => hC)
    (fun i _ i' _ hne C hC => by
      refine ⟨?_, ?_⟩
      · show BiVacAt ψ LA LS LX (· = (p i).v) (biComb ψ A S X (e₁ i) (e₂ i) (biComb ψ A S X (e₁ i') (e₂ i') C))
        rw [hbc i i' hne _ _ _ _ (he₁ i) (he₂ i) (he₁ i') (he₂ i')]
        exact biVac_biComb_off hψ (hdisj i' i fun h => hne h.symm) (he₁ i') (he₂ i') hC.1
      · show biComb ψ A S X (e₁ i') (e₂ i') C = biComb ψ A S X (r i) (r' i)
          (biComb ψ A S X (e₁ i) (e₂ i) (biComb ψ A S X (e₁ i') (e₂ i') C))
        rw [hbc i i' hne _ _ _ _ (he₁ i) (he₂ i) (he₁ i') (he₂ i'),
          hbc i i' hne _ _ _ _ (hr1 i) (hr1' i) (he₁ i') (he₂ i'), ← hC.2])
  have hcl : ∀ {S' T' : HSp D} (E : ι → WO S' T' →₀ ℂ), (∀ i, CombAt (· = (p i).v) (E i)) → ∀ w,
      w ∈ AddSubmonoid.closure (⋃ i ∈ I, ((E i).support : Set (WO S' T'))) → MxAt P w := by
    intro S' T' E hE' w hw
    induction hw using AddSubmonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, -, hx⟩ := hx
      exact GlobalTheory.DisjComb.mxAt_mono (fun y hy => (hP.mem y).2 ⟨i, hy⟩) (hE' i x hx)
    | zero => intro a b; simp
    | add x y _ _ hx hy => intro a b; exact Ideal.add_mem _ (hx a b) (hy a b)
  refine ⟨e, e', fun w hw => hcl e₁ he₁ w (hes w hw), fun w hw => hcl e₂ he₂ w (hes' w hw),
    fun f₁ Ξ Φ₂ hf₁ hΞ hΦ => ?_⟩
  have hY := hmain ⟨(f₁, Ξ, Φ₂), hf₁, hΞ, hΦ⟩
  have hth : (∀ v, IsThetaFunO ψ A S (fun u => biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂) u v)) ∧
      ∀ u, IsThetaFunO ψ S X (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂) u) := by
    by_cases hne : Nonempty ι
    · obtain ⟨i⟩ := hne
      have hv := hY.1 i (hP.all i)
      exact ⟨fun v => (hv.1 v).1, fun u => (hv.2 u).1⟩
    · have hl : I = [] := List.eq_nil_iff_forall_not_mem.2 fun i _ => hne ⟨i⟩
      have hXY := hY.2
      simp only [hl, List.foldr_nil] at hXY
      rw [← hXY]
      have hΞ' : Ξ = f₁ := by
        have h := hΞ
        rw [hl] at h
        exact h
      subst hΞ'
      have hΞθ := hf₁.1
      have hΦθ := hΦ.1
      exact ⟨fun v => GlobalTheory.LastSeeSaw.isThetaFunO_const_mul (Φ₂ ((o''.resT S v).1))
          (GlobalTheory.BoxSlice.isThetaFunO_slice_left o hΞθ (kap τ S ((o''.resT S v).2))),
        fun w => OrthDec.isThetaFunO_boxT o'' hΦθ
          (GlobalTheory.LastSeeSaw.isThetaFunO_kap τ hτ S (GlobalTheory.BoxSlice.isThetaFunO_slice_right o hΞθ w))⟩
  have hPl : ∀ x, P x ↔ x ∈ I.map fun i => (p i).v := fun x => (hP.mem x).trans
    ⟨fun ⟨i, h⟩ => List.mem_map.2 ⟨i, hP.all i, h.symm⟩, fun h => by
      obtain ⟨i, -, h⟩ := List.mem_map.1 h
      exact ⟨i, h.symm⟩⟩
  have hnd : (I.map fun i => (p i).v).Nodup := hP.nodup.map hP.inj
  have hBV : BiVacAt ψ LA LS LX P (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
    refine ⟨fun v => ?_, fun u => ?_⟩
    · refine vac_of_list hψ hLA hLS (hth.1 v) _ hnd P hPl fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (hY.1 i (hP.all i)).1 v
    · refine vac_of_list hψ hLS hLX (hth.2 u) _ hnd P hPl fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (hY.1 i (hP.all i)).2 u
  refine ⟨hBV, ?_⟩
  have hF := biComb_eq_foldr_vac (P := P) c c' (I.map fun i => (r i, r' i))
    (fun f hf => by rw [List.foldr_map]; exact comb_eq_foldr hP hψ hLA hLS hc r hr1 hr2 f hf)
    (fun f hf => by rw [List.foldr_map]; exact comb_eq_foldr hP hψ hLS hLX hc' r' hr1' hr2' f hf) _ hBV
  rw [hF, List.foldr_map]
  exact hY.2

end GlobalTheory.LastTAllPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  first | exact @GlobalTheory.LastTAllPf.main | exact GlobalTheory.LastTAllPf.main | (intros; apply GlobalTheory.LastTAllPf.main <;> assumption)
end
