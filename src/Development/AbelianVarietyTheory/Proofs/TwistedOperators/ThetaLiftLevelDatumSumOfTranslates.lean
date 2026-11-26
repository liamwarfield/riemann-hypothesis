module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedClassEqPartAddTwoMovedShiftedPoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicators

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.PairTriv

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := by
  ext i j
  rfl

theorem hatA_tens_mono {S T : HSp D} (Λ : Lt D.host.E S.rank) {L L' : Lt D.host.E T.rank} (h : L ≤ L') :
    hatA S T (tens Λ L) ≤ hatA S T (tens Λ L') := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, y, hy, rfl⟩
  refine ⟨α, hα, y, ?_, rfl⟩
  refine (AddSubgroup.closure_mono ?_) hy
  rintro z ⟨v, hv, u, hu, rfl⟩
  exact ⟨v, hv, u, h hu, rfl⟩

theorem actO_back {S T : HSp D} (k : GA D S) (x : WO S T) : actO S T k 1 (actO S T k⁻¹ 1 x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) k⁻¹ (1 : GA D T) x
  simpa using this

theorem pair_trivial : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg hodd e he a k₀ Λ' hab hmov hgen hmv Lv hLv u hu t ht
  have hsd : SelfD C.X (Lv.sh C.X.Λ) :=
    GlobalTheory.SW.Lev.selfD_idq Lv.ne_bot Lv.proper Lv.cop (GlobalTheory.SW.Lev.selfD_of_sympl C.sympl)
  have hV := GlobalTheory.SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmv
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩

  obtain ⟨ht1, ht2, ht3⟩ := ht
  have hh0 : IsHalf (cA D e) (actO S T k₀⁻¹ 1 t) := GlobalTheory.WeilVacMove.isHalf_actO _ _ _ ht1
  have hfr := hmov.2.2 _ hh0
  rw [actO_back] at hfr
  have ht0 : actO S T k₀⁻¹ 1 t ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ)) :=
    ((hgen _ hh0).2).1 ⟨hfr ▸ ht2, fun PP hPP => hfr ▸ ht3 PP hPP⟩
  rw [← hLv] at ht0
  have ht0' := hatA_tens_mono (stdL D.host.E S.rank) (GlobalTheory.SW.Lev.smul_le_idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ) ht0
  have hF := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  set t₀ := actO S T k₀⁻¹ 1 t with ht₀
  set w := actO S T k₀⁻¹ 1 u with hw₀
  have et : t = actO S T k₀ 1 t₀ := (actO_back k₀ t).symm
  have eu : GlobalTheory.LiftLevel.partAt e u = actO S T k₀ 1 (e • w) := by
    rw [partAt_eq_smul, GlobalTheory.OneMapRef.Term.actO_smul, actO_back]
  have hhalf : cA D e • t₀ = t₀ := by
    ext i j
    exact hh0 i j
  have key : symplO S T t (GlobalTheory.LiftLevel.partAt e u) = symplO S T t₀ w := by
    rw [et, eu, hF.2.2.2.2.2.2.1, (hF.2.2.2.2.2.1 t₀ (e • w) 0).2, GlobalTheory.SplitScalar.symplO_smul, hhalf,
      ← (hF.2.2.2.2.2.1 t₀ w 0).2]
  rw [key]
  exact GlobalTheory.OneMapRef.Term.char_hatA C hV hsd t₀ ht0' w hw

end GlobalTheory.LiftLevel.PairTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftGroupPointsPairTrivialShiftedTensorLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  first | exact @GlobalTheory.LiftLevel.PairTriv.pair_trivial | exact GlobalTheory.LiftLevel.PairTriv.pair_trivial | (intros; apply GlobalTheory.LiftLevel.PairTriv.pair_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftMul

variable {D : D7}

theorem exists_den_AA (D : D7) :
    ∃ d : ℕ, 0 < d ∧ ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E) := by
  obtain ⟨b, hb, hbI⟩ := D.host.AA.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, fun a ha => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨o, ho⟩ := hbI a ha
    refine ⟨c * o, ?_⟩
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c * o)
    rw [map_mul, ho, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]

def fA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)

theorem gen_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} {α : Af D.host.F} (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {s : Fin S.rank → D.host.E} (hs : s ∈ stdL D.host.E S.rank) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  obtain ⟨o, ho⟩ := ha
  have hc : toEAf D (incA D (d : D.host.E) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [← map_mul, ho]
    exact GlobalTheory.IdemIntegral.eToEAf_int D o
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hc hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int hβS hs)
    (GlobalTheory.ConjHalfInt.pair_row_int hsd hβT ht)

theorem lat_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} (hd : ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {x : WO S T}
    (hx : x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • x)) := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • u)))
    ?_ ?_ ?_ ?_ hx
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact gen_int S T ΛT hsd βS βT hβS hβT hα' (hd a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem red_nsmul {b a : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ PP.asIdeal) : IsIntM (m • N) ∧ redM PP (m • N) = 0 := by
  have hI : IsIntM (m • N) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul]; exact mul_mem (natCast_mem _ m) (hN i j)
  refine ⟨hI, ?_⟩
  ext i j
  simp only [redM, dif_pos (hI i j), Matrix.zero_apply]
  have e : (⟨(m • N) i j, hI i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (m : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N i j, hN i j⟩ := by
    apply Subtype.ext; simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [e, map_mul, map_natCast]
  have h0 : (m : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal) m]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [h0, zero_mul]

theorem nsmul_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hne h2 e hidem
  obtain ⟨d, hd0, hd⟩ := exists_den_AA D
  set m2 : ℕ := ∏ PP ∈ Pg ∪ Q, Ideal.absNorm PP.asIdeal with hm2
  have hm2pos : 0 < m2 := Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
  have hm2mem : ∀ PP ∈ Pg ∪ Q, (m2 : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => by
    rw [hm2, Nat.cast_prod]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hPP) (Ideal.absNorm_mem _)
  refine ⟨d * m2, Nat.mul_pos hd0 hm2pos, fun x hx hh => ?_⟩
  have hint := lat_int S T ΛT hsd βS βT hβS hβT hd hx
  have heq : frMapAdj S T βS βT ((d * m2) • x) = m2 • frMapAdj S T βS βT (incA D (d : D.host.E) • x) := by
    have hdx : d • x = incA D (d : D.host.E) • x := by rw [map_natCast, Nat.cast_smul_eq_nsmul]
    rw [mul_comm d m2, ← smul_smul, hdx]
    exact (fA S T βS βT).map_nsmul _ _
  show IsHalf (cA D e) ((d * m2) • x) ∧ IsIntM (frMapAdj S T βS βT ((d * m2) • x)) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT ((d * m2) • x)) = 0
  refine ⟨fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh i j]
  · obtain ⟨PP, hPP⟩ := hne
    rw [heq]; exact (red_nsmul PP hint (hm2mem PP (Finset.mem_union_left _ hPP))).1
  · rw [heq]; exact (red_nsmul PP hint (hm2mem PP hPP)).2

end GlobalTheory.LiftMul

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  first | exact @GlobalTheory.LiftMul.nsmul_mem_liftL | exact GlobalTheory.LiftMul.nsmul_mem_liftL | (intros; apply GlobalTheory.LiftMul.nsmul_mem_liftL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClasses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClassesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_levelDatumClasses : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  first | exact @GlobalTheory.LiftLevel.lvCls_finite | exact GlobalTheory.LiftLevel.lvCls_finite | (intros; apply GlobalTheory.LiftLevel.lvCls_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.MoverGlue

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def glue (σ : R →+* R) (ε : R) (P Q : Matrix n n R) : Matrix n n R :=
  ε • P + σ ε • (Q.map σ)ᵀ + (1 - ε - σ ε) • (1 : Matrix n n R)

theorem glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (P Q : Matrix n n R) :
    ((glue σ ε P Q).map σ)ᵀ = σ ε • (P.map σ)ᵀ + ε • Q + (1 - ε - σ ε) • (1 : Matrix n n R) := by
  ext i j
  simp only [glue, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_sub, map_one, hσ]
  by_cases h : i = j
  · subst h; simp <;> ring
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)] <;> ring

theorem scal_facts (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) :
    σ ε * σ ε = σ ε ∧ σ ε * ε = 0 ∧ ε * (1 - ε - σ ε) = 0 ∧ σ ε * (1 - ε - σ ε) = 0 ∧
      (1 - ε - σ ε) * ε = 0 ∧ (1 - ε - σ ε) * σ ε = 0 ∧ (1 - ε - σ ε) * (1 - ε - σ ε) = 1 - ε - σ ε := by
  have hσσ : σ ε * σ ε = σ ε := by rw [← map_mul, hε]
  have hσε : σ ε * ε = 0 := by rw [mul_comm, hεσ]
  have h1 : ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hε - hεσ
  have h2 : σ ε * (1 - ε - σ ε) = 0 := by linear_combination (-1 : R) * hσσ - hσε
  refine ⟨hσσ, hσε, h1, h2, by rw [mul_comm, h1], by rw [mul_comm, h2], ?_⟩
  linear_combination (1 : R) * hε + hσσ + 2 * hεσ

theorem smul_glue (σ : R →+* R) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0) (P Q : Matrix n n R) :
    ε • glue σ ε P Q = ε • P := by
  obtain ⟨-, -, h1, -⟩ := scal_facts σ ε hε hεσ
  simp only [glue, smul_add, smul_smul, hε, hεσ, h1, zero_smul, add_zero]

theorem off_smul_glue_cT (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) :
    (1 - ε - σ ε) • ((glue σ ε P Q).map σ)ᵀ = (1 - ε - σ ε) • (1 : Matrix n n R) := by
  obtain ⟨-, -, -, -, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  rw [glue_cT σ hσ]
  simp only [smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]

theorem glue_unitary (σ : R →+* R) (hσ : ∀ z, σ (σ z) = z) (ε : R) (hε : ε * ε = ε) (hεσ : ε * σ ε = 0)
    (P Q : Matrix n n R) (hPQ : ε • (P * Q) = ε • (1 : Matrix n n R)) (hQP : ε • (Q * P) = ε • (1 : Matrix n n R)) :
    glue σ ε P Q * ((glue σ ε P Q).map σ)ᵀ = 1 ∧ ((glue σ ε P Q).map σ)ᵀ * glue σ ε P Q = 1 := by
  obtain ⟨hσσ, hσε, h1, h2, h3, h4, h5⟩ := scal_facts σ ε hε hεσ
  have hsum : ε • (1 : Matrix n n R) + σ ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [← add_smul, ← add_smul]; simp
  have hsum' : σ ε • (1 : Matrix n n R) + ε • (1 : Matrix n n R) + (1 - ε - σ ε) • (1 : Matrix n n R) = 1 := by
    rw [add_comm (σ ε • (1 : Matrix n n R))]; exact hsum
  have key : ∀ M N : Matrix n n R, ε • (M * N) = ε • (1 : Matrix n n R) →
      σ ε • ((N.map σ)ᵀ * (M.map σ)ᵀ) = σ ε • (1 : Matrix n n R) := by
    intro M N hMN
    ext i j
    have := congrArg σ (congrFun (congrFun hMN j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul] at this
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply, this]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [glue_cT σ hσ]
  constructor
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hPQ, key P Q hPQ]
    first | exact hsum | exact hsum'
  · simp only [glue, add_mul, mul_add, smul_mul_smul_comm, hε, hεσ, hσε, hσσ, h1, h2, h3, h4, h5, zero_smul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
    rw [hQP, key Q P hQP]
    first | exact hsum | exact hsum'

end Alg

variable {D : D7}

theorem exists_mov (S : HSp D) (k : GA D S) :
    ∃ Λ' : Lt D.host.E S.rank, IsMov (fmtC S k⁻¹) Λ' (stdL D.host.E S.rank) := by
  have hmul : ∀ g h : GA D S, fmtC S (g * h) = fmtC S g * fmtC S h := by
    intro g h
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]
  have hone : fmtC S 1 = 1 := by
    simp only [fmtC, cM, Formalism.L2.Theta.mt, map_one, Units.val_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  let G : GL (Fin S.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    ⟨fmtC S k, fmtC S k⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩
  have hfg : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span D.host.E ((stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower]
    have : (Set.range fun a : Fin S.rank => (Pi.single a (1 : D.host.E) : Fin S.rank → D.host.E)) =
        Set.range (Pi.basisFun D.host.E (Fin S.rank)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
  obtain ⟨Λ, -, -, -, hΛ⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E S.rank _ G hfg hsp
  refine ⟨Λ, fun u => ?_⟩
  have hV : ∀ L : Lt D.host.E S.rank, ((hatV L : AddSubgroup _) : Set (Fin S.rank → AfE D)) =
      (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin S.rank → D.host.E)) : Set _) := fun L => rfl
  have hGi : ∀ z, fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec]
  constructor
  · intro hu
    refine ⟨fmtC S k *ᵥ u, ?_, (hGi u).symm⟩
    have : fmtC S k *ᵥ u ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := by
      rw [hV, hΛ]; exact ⟨u, hu, rfl⟩
    exact this
  · rintro ⟨u₀, hu₀, rfl⟩
    have : u₀ ∈ ((hatV Λ : AddSubgroup _) : Set (Fin S.rank → AfE D)) := hu₀
    rw [hV, hΛ] at this
    obtain ⟨w, hw, rfl⟩ := this
    change fmtC S k⁻¹ *ᵥ (fmtC S k *ᵥ w) ∈ hatV (stdL D.host.E S.rank)
    rw [hGi]; exact hw

theorem map_smul_ringHom {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {m p : Type} (c : R) (M : Matrix m p R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp [map_mul]

end GlobalTheory.MoverGlue


open GlobalTheory.MoverGlue in
theorem GlobalTheory.LiftLevel.exists_mover : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a hab
  obtain ⟨b, hab⟩ := hab
  have he2 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
  let ψ : EAf D →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm.toAlgHom.toRingHom
  have hφψ : ∀ z, φ (ψ z) = z := fun z => AlgEquiv.apply_symm_apply _ z
  have htoE : ∀ z : AE D, toEAf D z = φ (finPart D z) := fun z => rfl
  let σ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* (Af D.host.F ⊗[D.host.F] D.host.E) :=
    sigR (Af D.host.F) D.sp.cm.sig
  have hσ : ∀ z, σ (σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      show (Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) ((Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig) (x ⊗ₜ y)) = x ⊗ₜ y
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hfc : ∀ z : AE D, finPart D (cA D z) = σ (finPart D z) := fun z =>
    GlobalTheory.UnitaryGlue.map_sigR (sndA D.host.F) D.sp.cm.sig z
  set ε := finPart D e with hεdef
  have hεε : ε * ε = ε := by rw [← map_mul, he2]
  have hεσ : ε * σ ε = 0 := by rw [← hfc, ← map_mul, hec, map_zero]
  let Bs : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := βS.val.map ψ
  let Bi : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (βS⁻¹).val.map ψ
  have hBB : Bs * Bi = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : Bi * Bs = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  let P := finPart D a • Bs
  let Qm := finPart D b • Bi
  have hPQ : ε • (P * Qm) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB, smul_smul, ← map_mul, ← map_mul, hab, he2]
  have hQP : ε • (Qm * P) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    rw [smul_mul_smul_comm, hBB', smul_smul, ← map_mul, ← map_mul, mul_comm b a, hab, he2]
  obtain ⟨hu1, hu2⟩ := glue_unitary σ hσ ε hεε hεσ P Qm hPQ hQP
  set hf := glue σ ε P Qm with hhf
  let gfGL : GL (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨hf, (hf.map σ)ᵀ, hu1, hu2⟩
  have hJ : JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) = 1 := by
    rw [C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmem : gfGL ∈ HR (Af D.host.F) D.sp.cm.sig (HSpace.gram S) := by
    show Formalism.UG.cT σ hf * JR (F := D.host.F) (Af D.host.F) (HSpace.gram S) * hf = JR (F := D.host.F) (Af D.host.F) (HSpace.gram S)
    rw [hJ, Matrix.mul_one]; exact hu2
  obtain ⟨g, hgC, hgf⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D S).1 gfGL hmem
  obtain ⟨Λ', hΛ'⟩ := exists_mov S g

  have hmt1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
  have hact : ∀ x : WO S T, actO S T g 1 x = HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹) := by
    intro x; show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T 1) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (Formalism.L2.Theta.mt S g⁻¹) = _; rw [hmt1, Matrix.one_mul]
  have hKf : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = (hf.map σ)ᵀ := by
    have h1 : ((finHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) := rfl
    rw [← h1, map_inv, hgf]; rfl
  have hKi : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := by
    have h1 : ((infHom S g⁻¹).val) = (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) := rfl
    have hg1 : infHom S g = 1 := hgC
    rw [← h1, map_inv, hg1, inv_one, Units.val_one]
  refine ⟨g, Λ', ⟨hgC, ?_, ?_⟩, hΛ'⟩
  · intro x hx
    rw [hact]
    have hX : (1 - ε - σ ε) • x.map (finPart D) = x.map (finPart D) := by
      ext i j
      have := congrArg (finPart D) (hx i j)
      rw [map_mul, map_sub, map_sub, map_one, hfc] at this
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using this
    ext i j
    refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (infPart D) = x.map (infPart D) by
        rw [Matrix.map_mul, hKi, Matrix.mul_one]) i) j
      simpa only [Matrix.map_apply] using h
    · have h := congrFun (congrFun (show (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (finPart D) = x.map (finPart D) by
        rw [Matrix.map_mul, hKf]
        conv_lhs => rw [← hX]
        rw [Matrix.smul_mul, ← Matrix.mul_smul, off_smul_glue_cT σ hσ ε hεε hεσ, Matrix.mul_smul, Matrix.mul_one, hX]) i) j
      simpa only [Matrix.map_apply] using h
  · intro x hx
    rw [hact]
    have hcK : ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ.map (toEAf D) = hf.map φ := by
      ext i j
      have hk := congrFun (congrFun hKf j) i
      simp only [Matrix.map_apply, Matrix.transpose_apply] at hk ⊢
      rw [htoE, hfc, hk, hσ]
    have hεhf : (toEAf D e) • hf.map φ = (toEAf D e * toEAf D a) • βS.val := by
      have h1 : ε • hf = ε • P := smul_glue σ ε hεε hεσ P Qm
      ext i j
      have h2 := congrFun (congrFun h1 i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h2 ⊢
      rw [htoE, htoE, ← map_mul, h2]
      simp only [P, Bs, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hφψ, hεdef, mul_assoc]
    set Z := (HMul.hMul ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) with hZdef
    have hxc : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
      ext i j
      have := congrArg (cA D) (hx j i)
      rw [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
      simpa only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul] using this
    have hZ : toEAf D e • Z = Z := by
      rw [hZdef]
      conv_rhs => rw [← hxc]
      rw [Matrix.smul_mul, GlobalTheory.MoverGlue.map_smul_ringHom]
    have hL2 : (HMul.hMul (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) ((HSpace.gram T).map (incA D))).map (toEAf D) =
        HMul.hMul (hf.map φ) Z := by
      have h3 : (((HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g⁻¹)).map (cA D))ᵀ :
          Matrix (Fin S.rank) (Fin T.rank) (AE D)) = HMul.hMul ((Formalism.L2.Theta.mt S g⁻¹).map (cA D))ᵀ
          ((x.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin T.rank) (AE D)) := by
        rw [Matrix.map_mul, Matrix.transpose_mul]
      rw [h3, Matrix.mul_assoc, Matrix.map_mul, hcK]
    have hLHS : HMul.hMul (HMul.hMul (βS⁻¹).val (HMul.hMul (hf.map φ) Z)) βT.val = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      conv_lhs => rw [← hZ]
      rw [Matrix.mul_smul, ← Matrix.smul_mul, hεhf, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hRHS : toEAf D a • HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val Z) βT.val) = (toEAf D e * toEAf D a) • HMul.hMul Z βT.val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      conv_lhs => rw [← hZ]
      rw [Matrix.smul_mul, smul_smul, mul_comm (toEAf D a)]
    unfold GlobalTheory.LiftLevel.adjA frMapAdj
    have hGS : (HSpace.gram S)⁻¹.map (incA D) = 1 := by
      rw [C.m.gS]; simp
    rw [hGS]
    simp only [Matrix.one_mul]
    rw [hL2, hLHS, ← hRHS]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unitary_mover_standard_lattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  first | exact @GlobalTheory.LiftLevel.exists_mover | exact GlobalTheory.LiftLevel.exists_mover | (intros; apply GlobalTheory.LiftLevel.exists_mover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem isLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsLattice E (stdL E n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isFullLattice_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule.IsFullLattice E (stdL E n) := by
  letI := isLattice_stdL E n
  refine ⟨?_⟩
  rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2
  funext i
  exact (Pi.basisFun_apply E (Fin n) i).symm

theorem liftL_nsmul_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO (S := S) (T := T)
    (ΛS := stdL D.host.E S.rank) (ΛT := ΛT) (isFullLattice_stdL D.host.E S.rank) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hΛT)
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  refine ⟨k₄ * k₂, Nat.mul_pos hk₄ hk₂, fun x hx => ?_⟩
  obtain ⟨hhalf, hint, -⟩ := hx
  have hx0 : (k₂ • x).map (infPart D) = 0 := by
    ext i j
    show infPart D ((k₂ • x) i j) = 0
    rw [Matrix.smul_apply, ← hhalf i j, nsmul_eq_mul, RingHom.map_mul, RingHom.map_mul, hinf, zero_mul, mul_zero]
  rw [mul_smul]
  exact h₄ (k₂ • x) hx0 (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ x hint)

end GlobalTheory.LiftLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftNsmulMemCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | exact GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | (intros; apply GlobalTheory.LiftLevel.liftL_nsmul_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLevelDatumSumOfTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

theorem lift_level_datum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨hI1, hI2, hI3, hI4⟩ := GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime D Pg Q e hPg h2 he
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨k₀, Λ', hmov, hM⟩ := GlobalTheory.T.exists_finite_unitary_mover_standard_lattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a ha
  obtain ⟨Lv, h𝔪, hw, hJ, hD2⟩ := GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ ha hmov hgen hI1 hI2 hI3 hI4
  obtain ⟨m1, hm1, hm1'⟩ := GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  obtain ⟨m2, hm2, hm2'⟩ := GlobalTheory.T.nsmul_mem_lift_points_of_completed_hom_lattice_half D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hfin := GlobalTheory.T.finite_levelDatumClasses D S T C Lv
  refine ⟨Lv, k₀, Λ', liftL S T βS βT Pg Q e, hw, ?_, hJ, hmov.1, hM, hfin, fun x hx => hx.1,
    ⟨m1, hm1, hm1'⟩, ⟨m2, hm2, hm2'⟩,
    fun u hu => ⟨GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu, fun t ht => GlobalTheory.T.liftGroupPoints_pair_trivial_shiftedTensorLattice D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu t ht, GlobalTheory.T.scaledTensorLattice_le_completedHomLattice_offPlaces D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 u hu⟩,
    GlobalTheory.T.movedClass_eq_part_add_two_movedShiftedPoint D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪, GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' ha hmov hgen hM Lv h𝔪 hfin hD2⟩
  intro PP hPP
  rw [h𝔪]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hPP))

end GlobalTheory.LiftLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLevelDatumSumOfTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_level_datum_sum_of_translates : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ (Lv : GlobalTheory.SW.Level C.X) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (L : AddSubgroup (WO S T)), IdemTwo Lv.w ∧ (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ k₀ ∈ GfC S ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) ∧ Finite (GlobalTheory.LiftLevel.LvCls C Lv) ∧ (∀ x ∈ L, IsHalf (cA D e) x) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) ∧ (∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), ∃ v ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), actO S T k₀ 1 (finW S T y) = GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) + 2 • v ∧ C.ψ (symplOH S T (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) (2 • v)) = 1) ∧ ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL L (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  first | exact @GlobalTheory.LiftLevel.lift_level_datum | exact GlobalTheory.LiftLevel.lift_level_datum | (intros; apply GlobalTheory.LiftLevel.lift_level_datum <;> assumption)
end
