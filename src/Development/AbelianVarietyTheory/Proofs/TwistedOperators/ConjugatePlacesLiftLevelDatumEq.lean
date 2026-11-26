module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionEqZeroIffMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowReductionSurjectiveLatticeVectorsPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftDat

theorem rowAdj_isIntM_of_mem : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4 v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · intro i j; exact absurd j.2 (by omega)
  have hS : 0 < S.rank := lt_of_lt_of_le hpos hn
  let i0 : Fin S.rank := ⟨0, hS⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := vecMulVec (Pi.single i0 1) v
  have hy : y ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    AddSubgroup.subset_closure ⟨_, Submodule.subset_span ⟨i0, rfl⟩, v, hv, rfl⟩
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hfin : finPart D (cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
  have hA : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    fun o z hz => GlobalTheory.LiftLevel.smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have h0 : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hy
  have hx : cA D e • finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) :=
    GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hfin h0
  have hhalf : IsHalf (cA D e) (cA D e • finW S T y) := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hce]
  have hint := ((hgen _ hhalf).1).2 hx
  have hM : ∀ N : Matrix (Fin S.rank) (Fin T.rank) (EAf D),
      HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val N) βT.val) = HMul.hMul N βT.val := by
    intro N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
  have key : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e v 0 j =
      GlobalTheory.LiftLevel.adjA S T βS βT a (cA D e • finW S T y) i0 j := by
    intro j
    simp only [GlobalTheory.LiftLevel.adjA, frMapAdj]
    rw [hM]
    simp only [GlobalTheory.LiftDat.rowAdj, Matrix.smul_apply, C.m.gS, inv_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, finW, y, vecMulVec_apply, Pi.single_eq_same, one_mul, i0]
  intro i j
  rw [Fin.fin_one_eq_zero i, key]
  exact hint i0 j

end GlobalTheory.LiftDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVector_adjointRow_integral : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  first | exact @GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | exact GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | (intros; apply GlobalTheory.LiftDat.rowAdj_isIntM_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDat

theorem frMapAdj_partAt_actO_finW : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2 e he a k₀ hab hmov hgen h1 h2' h3 h4 y
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hp : ∀ (c : AE D) (z : WO S T), GlobalTheory.LiftLevel.partAt c z = c • z := fun c z => by
    ext i j; simp [GlobalTheory.LiftLevel.partAt, smul_eq_mul]
  have hcomm : GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) =
      actO S T k₀ 1 (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := by
    rw [hp, hp]
    show _ = HMul.hMul (HMul.hMul (mt T 1) ((cA D e • finW S T y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S k₀⁻¹)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hx : IsHalf (cA D e) (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [GlobalTheory.LiftLevel.partAt, Matrix.map_apply, ← mul_assoc, hcc]
  rw [hcomm, hmov.2.2 _ hx]
  unfold GlobalTheory.LiftLevel.adjA frMapAdj
  rw [C.m.gS]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hi : ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)⁻¹).map (incA D) = 1 := by
    rw [inv_one]; exact Matrix.map_one (incA D) (map_zero _) (map_one _)
  rw [hi, Matrix.one_mul]
  ext i j
  simp only [rowAdj, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.LiftLevel.partAt, finW]

end GlobalTheory.LiftDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  first | exact @GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | exact GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW | (intros; apply GlobalTheory.LiftDat.frMapAdj_partAt_actO_finW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDatComb

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem conjI_eq_comap (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMax (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ bar_surj

theorem conjI_inj {P P' : Ideal (𝓞 D.host.E)} (h : conjI P = conjI P') : P = P' := by
  ext a
  have := SetLike.ext_iff.1 h (GlobalTheory.SW.Lev.bar a)
  rwa [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this

theorem mem_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E} :
    x ∈ liftI Pg Q ↔ ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∈ PP.asIdeal := by
  constructor
  · intro hx PP hPP
    exact GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le hPP hx)
  · intro h
    unfold liftI
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Submodule.mem_iInf]
      intro PP hPP
      exact GlobalTheory.SW.Lev.mem_conjI.2 (h PP hPP)
    · intro PP _ PP' _ hne
      have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun e =>
        hne (HeightOneSpectrum.ext (conjI_inj e))
      exact (Ideal.isCoprime_iff_sup_eq).2 ((conjI_isMax PP).coprime_of_ne (conjI_isMax PP') hne')

theorem isUnit_mk_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E}
    (h : ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∉ PP.asIdeal) : IsUnit (Ideal.Quotient.mk (liftI Pg Q) x) := by
  have hc : IsCoprime (Ideal.span {x}) (liftI Pg Q) := by
    unfold liftI
    refine IsCoprime.prod_right fun PP hPP => ?_
    have hx : x ∉ conjI PP.asIdeal := fun hm => h PP hPP (GlobalTheory.SW.Lev.mem_conjI.1 hm)
    obtain ⟨y, i, hi, e⟩ := (conjI_isMax PP).exists_inv hx
    exact Ideal.isCoprime_iff_exists.2 ⟨y * x, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x), i, hi, e⟩
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ a, ?_⟩
  have : Ideal.Quotient.mk (liftI Pg Q) j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
  rw [← map_mul, mul_comm, eq_sub_of_add_eq e, map_sub, this, sub_zero, map_one]

section CongLemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem cong_of_sub_mem {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} (h : u - v ∈ 𝔪 • X.Λ) : GlobalTheory.SW.Cong X 𝔪 u v :=
  ⟨1, by rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq], by rwa [one_smul]⟩

theorem cong_congr_left {𝔪 : Ideal (𝓞 E)} {y u v : Fin r → E} (hy : y - u ∈ 𝔪 • X.Λ)
    (h : GlobalTheory.SW.Cong X 𝔪 y v) : GlobalTheory.SW.Cong X 𝔪 u v := by
  obtain ⟨s, hs, hm⟩ := h
  refine ⟨s, hs, ?_⟩
  have : s • (u - v) = s • (y - v) - s • (y - u) := by
    rw [← smul_sub]; congr 1; abel
  rw [this]
  exact sub_mem hm (Submodule.smul_mem _ s hy)

theorem sum_mem_of_coeff {𝔪 : Ideal (𝓞 E)} {m : ℕ} (β : Fin m → Fin r → E) (hβ : ∀ i, β i ∈ X.Λ)
    (d : Fin m → 𝓞 E) (hd : ∀ j, d j ∈ 𝔪) : ∑ j, d j • β j ∈ 𝔪 • X.Λ :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hd j) (hβ j)

end CongLemmas

section Mat
open GlobalTheory.LiftLevel GlobalTheory.LiftDat
variable {D : D7}

theorem mk_conjI_eq_iff (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) :
    Ideal.Quotient.mk (conjI P) x = Ideal.Quotient.mk (conjI P) y ↔
      Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar x) = Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar y) := by
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq, GlobalTheory.SW.Lev.mem_conjI, map_sub]

theorem mapMat_eq_one_iff {R' : Type*} [CommRing R'] {r : ℕ} (f : 𝓞 D.host.E →+* R')
    (A : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    A.map f = 1 ↔ ∀ a b, f (A a b) = f ((1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) a b) := by
  rw [← Matrix.map_one f (map_zero f) (map_one f), ← Matrix.ext_iff]
  simp only [Matrix.map_apply]

theorem jgrp_iff {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} (κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q))
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (hκ : κ.val = ctᵀ.map (Ideal.Quotient.mk _)) :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP ∈ Pg, ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar) = 1 := by
  rw [mem_Jgrp]
  refine forall₂_congr fun PP hPP => ?_
  rw [Units.ext_iff]
  have e1 : ((Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ hPP)) κ :
      GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = ct.transpose.map (Ideal.Quotient.mk (conjI PP.asIdeal)) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, hκ]
    rfl
  rw [e1, Units.val_one, Matrix.transpose_map, Matrix.transpose_eq_one, mapMat_eq_one_iff, mapMat_eq_one_iff]
  exact forall₂_congr fun a b => mk_conjI_eq_iff _ _ _

theorem conjRes_det {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) {r : ℕ}
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    conjRes Pg Q PP h (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det =
      (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_map, Matrix.transpose_map, Matrix.det_transpose]
  rfl

end Mat

end GlobalTheory.LiftDatComb

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftDatComb GlobalTheory.LiftLevel

theorem dat_mkLevel_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  intro D S T C hn Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 hind y c hyc Y hY
  set ct : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E) := fun a b => c (Fin.castLE hn a) b with hct
  have hTop : ∀ PP ∈ Pg ∪ Q, topL T.rank (Y PP) = ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) := by
    intro PP hPP
    ext a b
    rw [topL, dite_eq_left ⟨lt_of_lt_of_le a.2 hn, b.2⟩, hY PP hPP]
    rfl
  have hcong0 : ∀ i, GlobalTheory.SW.Cong C.X (liftI Pg Q) (y i) 0 ↔ ∀ j, c i j ∈ liftI Pg Q := by
    intro i
    constructor
    · intro hc
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc i) hc
      exact hind (c i) ⟨s, hs, hm⟩
    · intro hc
      refine cong_of_sub_mem C.X ?_
      rw [sub_zero, ← sub_add_cancel (y i) (∑ j, c i j • β j)]
      exact add_mem (hyc i) (sum_mem_of_coeff C.X β hβ _ hc)
  have hrow : ∀ PP ∈ Pg ∪ Q, ∀ i j, (Y PP i j = 0 ↔ Lev.bar (c i j) ∈ PP.asIdeal) := by
    intro PP hPP i j
    rw [hY PP hPP, Ideal.Quotient.eq_zero_iff_mem]
  have hdetU : ∀ PP ∈ Pg ∪ Q, IsUnit (topL T.rank (Y PP)).det → Lev.bar ct.det ∉ PP.asIdeal := by
    intro PP hPP hu hm
    have e : (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar)).det =
        ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) ct.det := (RingHom.map_det _ _).symm
    rw [hTop PP hPP, e, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hm] at hu
    exact not_isUnit_zero hu
  set L := mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 with hL
  unfold Level.dat
  by_cases h : (∃ k : L.J, L.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin S.rank, T.rank ≤ (k : ℕ) → GlobalTheory.SW.Cong C.X L.𝔪 (y k) 0
  · rw [dite_eq_left h]
    obtain ⟨k', hk'm, hk'c⟩ := h.1.choose_spec
    set κ := h.1.choose with hκdef
    have hκval : (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val =
        ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := by
      rw [← hk'm]
      ext a b
      simp only [Matrix.map_apply, Matrix.transpose_apply]
      refine Ideal.Quotient.eq.2 ?_
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc (Fin.castLE hn b)) (hk'c b)
      have := hind (fun j => c (Fin.castLE hn b) j - k' j b)
        ⟨s, hs, by
          convert hm using 2
          simp only [sub_zero, sub_smul, Finset.sum_sub_distrib]
          rfl⟩ a
      rw [← neg_sub]
      exact neg_mem this
    have hJ := (jgrp_iff (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)) ct hκval).1 κ.2
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q :=
      fun i hi => (hcong0 i).1 (h.2 i hi)
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) :=
      fun PP hPP i j hi _ => (hrow PP hPP i j).2 (mem_liftI.1 (hlowc i hi j) PP hPP)
    have hdetQ : ∀ PP (hPP : PP ∈ Pg ∪ Q), conjRes Pg Q PP hPP
        (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val.det = (topL T.rank (Y PP)).det := by
      intro PP hPP
      rw [hκval]
      exact (conjRes_det hPP ct).trans (congrArg Matrix.det (hTop PP hPP).symm)
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := fun PP hPP =>
      ⟨hLow PP (Finset.mem_union_right _ hPP), by
        rw [← hdetQ PP (Finset.mem_union_right _ hPP), ← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Units.isUnit _).map _⟩
    have hK : omegaK Pg Y = 1 := by
      unfold omegaK
      rw [if_pos]
      intro PP hPP
      exact ⟨hLow PP (Finset.mem_union_left _ hPP), by rw [hTop PP (Finset.mem_union_left _ hPP)]; exact hJ PP hPP⟩
    rw [hK, one_mul]
    unfold omegaQ
    rw [dite_eq_left hQc]
    show ((lamHom Pg Q T.rank ξ (⟨κ.1, κ.2⟩ : Jgrp Pg Q T.rank) : ℂˣ) : ℂ) = _
    rw [lamHom_apply, Units.val_inv_eq_inv_val, Units.coe_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q))) =
        (hQc PP.1 PP.2).2.unit := by
      ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact hdetQ _ _
    rw [e, _root_.zpow_neg_one]
  · rw [dite_eq_right h]
    symm
    by_contra hne
    have hK : omegaK Pg Y ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank ξ (-1) Y ≠ 0 := right_ne_zero_of_mul hne
    have hKc : ∀ PP ∈ Pg, LowZero T.rank (Y PP) ∧ topL T.rank (Y PP) = 1 := by
      by_contra hc
      exact hK (by unfold omegaK; rw [if_neg hc])
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := by
      by_contra hc
      exact hQ (by unfold omegaQ; rw [dite_eq_right hc])
    apply h
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) := by
      intro PP hPP
      rcases Finset.mem_union.1 hPP with hP | hP
      exacts [(hKc PP hP).1, (hQc PP hP).1]
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q := fun i hi j =>
      mem_liftI.2 fun PP hPP => (hrow PP hPP i j).1 (hLow PP hPP i j hi j.2)
    have hdet : IsUnit (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
      refine isUnit_mk_liftI fun PP hPP => hdetU PP hPP ?_
      rcases Finset.mem_union.1 hPP with hP | hP
      · rw [(hKc PP hP).2, Matrix.det_one]
        exact isUnit_one
      · exact (hQc PP hP).2
    set κ : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q) :=
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit with hκ
    have hκval : κ.val = ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := IsUnit.unit_spec _
    have hκJ : κ ∈ Jgrp Pg Q T.rank := (jgrp_iff κ ct hκval).2 fun PP hPP => by
      rw [← hTop PP (Finset.mem_union_left _ hPP)]
      exact (hKc PP hPP).2
    exact ⟨⟨⟨κ, hκJ⟩, ctᵀ, hκval.symm, fun i => cong_of_sub_mem C.X (hyc (Fin.castLE hn i))⟩,
      fun k hk => (hcong0 k).2 (hlowc k hk)⟩

end GlobalTheory.LiftDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  first | exact @GlobalTheory.LiftDat.dat_mkLevel_eq | exact GlobalTheory.LiftDat.dat_mkLevel_eq | (intros; apply GlobalTheory.LiftDat.dat_mkLevel_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLin

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (starRingEnd D.host.E x) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem toEAf_incA_bar (c : 𝓞 D.host.E) :
    toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) =
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
  simp [toEAf, finPart, incA, inclR, Formalism.L2.DIV.oToS, Formalism.UG.inclE]
  rfl

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

variable {D : D7}

theorem tmul_smul_add (p : AF D.host.F) (c x y : D.host.E) :
    p ⊗ₜ[D.host.F] (c * x + y) = (p ⊗ₜ[D.host.F] x) * incA D c + p ⊗ₜ[D.host.F] y := by
  rw [TensorProduct.tmul_add]
  congr 1
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm x c]

theorem rowAdj_smul_add (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D)
    (u v : Fin T.rank → D.host.E) (c : D.host.E) :
    GlobalTheory.LiftDat.rowAdj T βT a e (c • u + v) =
      toEAf D (incA D (starRingEnd D.host.E c)) • GlobalTheory.LiftDat.rowAdj T βT a e u + GlobalTheory.LiftDat.rowAdj T βT a e v := by
  have hM : (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c • u + v) k) * incA D (T.gram k l)) =
      incA D (starRingEnd D.host.E c) • (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] u k) * incA D (T.gram k l)) +
      (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      tmul_smul_add, mul_add, map_add, map_mul, cA_incA, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GlobalTheory.LiftDat.rowAdj
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

theorem rowRed_smul_add : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  intro D T βT a e PP u v hu hv c
  have hz := toEAf_incA_bar (D := D) c
  have hrow := rowAdj_smul_add T βT a e u v (c : D.host.E)
  have hzi : toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hz]; exact Subtype.property _
  have hent : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j =
      toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) * GlobalTheory.LiftDat.rowAdj T βT a e u 0 j + GlobalTheory.LiftDat.rowAdj T βT a e v 0 j := by
    intro j; rw [hrow]; simp [Matrix.add_apply, Matrix.smul_apply]
  have hint : IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hent]
    exact Subring.add_mem _ (Subring.mul_mem _ hzi (hu 0 j)) (hv 0 j)
  refine ⟨hint, ?_⟩
  funext j
  simp only [GlobalTheory.LiftDat.rowRed, redM, dif_pos (hint 0 j), dif_pos (hu 0 j), dif_pos (hv 0 j)]
  have hsub : (⟨GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j, hint 0 j⟩ :
      Formalism.L2.Herm.intAf D.host.F D.host.E) =
      Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) * ⟨_, hu 0 j⟩ + ⟨_, hv 0 j⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, ← hz, hent]
  rw [hsub, RingHom.map_add, RingHom.map_mul, Formalism.L2.DIV.resS_oToS]

end GlobalTheory.RowLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  first | exact @GlobalTheory.RowLin.rowRed_smul_add | exact GlobalTheory.RowLin.rowRed_smul_add | (intros; apply GlobalTheory.RowLin.rowRed_smul_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SW.Lev

theorem exists_bar_mk_eq_at_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  intro D P b
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := P) (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal) (fun _ => 1)
    (fun PP _ => PP.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun PP => Classical.choose (Ideal.Quotient.mk_surjective (b PP.1)))
  refine ⟨GlobalTheory.SW.Lev.bar y, fun PP hPP => ?_⟩
  rw [GlobalTheory.SW.Lev.bar_bar]
  have h := hy PP hPP
  rw [pow_one] at h
  have hc := Classical.choose_spec (Ideal.Quotient.mk_surjective (b PP))
  rw [← hc]
  exact Ideal.Quotient.eq.2 h

end GlobalTheory.SW.Lev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_conj_prescribed_residues_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  first | exact @GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | exact GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | (intros; apply GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.InfMem

theorem conjI_eq_comap (D : D7) (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj (D : D7) : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMaximal (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  haveI := PP.isMaximal
  exact Ideal.comap_isMaximal_of_surjective _ (bar_surj D)

theorem conjI_inj (D : D7) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : conjI PP.asIdeal = conjI PP'.asIdeal) : PP = PP' := by
  apply HeightOneSpectrum.ext
  ext a
  have := congrArg (fun I => GlobalTheory.SW.Lev.bar a ∈ I) h
  simp only [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this
  exact Iff.of_eq this

theorem mem_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E)
    (hx : ∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) : x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  unfold GlobalTheory.LiftLevel.liftI
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Submodule.mem_iInf]
    exact hx
  · intro PP _ PP' _ hne
    have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun h => hne (conjI_inj D h)
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (conjI_isMaximal D PP) (conjI_isMaximal D PP') hne'

theorem main : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := fun D Pg Q x hx => mem_liftI D Pg Q x hx

end GlobalTheory.LiftLevel.InfMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  first | exact @GlobalTheory.LiftLevel.InfMem.main | exact GlobalTheory.LiftLevel.InfMem.main | (intros; apply GlobalTheory.LiftLevel.InfMem.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

theorem level_datum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Irow := GlobalTheory.T.frameAdjoint_partAt_movedRationalPoint_row D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iint := GlobalTheory.T.latticeVector_adjointRow_integral D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Iker := GlobalTheory.T.adjointFrameRowReduction_eq_zero_iff_mem D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Isurj := GlobalTheory.T.rowReduction_surjective_latticeVectors_places D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4
  have Ilin := GlobalTheory.T.adjointFrameRowReduction_conjLinear_integers D T βT a e
  set R := GlobalTheory.LiftDat.rowRed T βT a e with hR
  have hz : ∀ PP, R PP 0 = 0 := by
    intro PP
    have hi := Iint 0 (zero_mem _)
    have h := (Ilin PP 0 0 hi hi 1).2
    simp only [smul_zero, add_zero, map_one, one_mul] at h
    funext j
    have h' := congrFun h j
    simp only [Pi.zero_apply]
    linear_combination -h'
  have hsum : ∀ PP (s : Finset (Fin T.rank)) (c : Fin T.rank → 𝓞 D.host.E)
      (u : Fin T.rank → Fin T.rank → D.host.E) (v : Fin T.rank → D.host.E), (∀ j, u j ∈ C.X.Λ) → v ∈ C.X.Λ →
      R PP (∑ j ∈ s, c j • u j + v) = fun l => ∑ j ∈ s, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c j)) *
        R PP (u j) l + R PP v l := by
    intro PP s c u v hu hv
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hm : ∑ j ∈ s, c j • u j + v ∈ C.X.Λ := add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hu j)) hv
      rw [Finset.sum_insert hj, add_assoc]
      rw [show c j • u j = ((c j : D.host.E)) • u j from rfl]
      rw [(Ilin PP (u j) _ (Iint _ (hu j)) (Iint _ hm) (c j)).2, ih]
      funext l
      rw [Finset.sum_insert hj]
      ring
  choose β hβΛ hβred using fun j : Fin T.rank => Isurj (fun PP => Pi.single j 1)
  have hexp : ∀ PP ∈ Pg ∪ Q, ∀ (c : Fin T.rank → 𝓞 D.host.E) (w : Fin T.rank → D.host.E), w ∈ C.X.Λ →
      ∀ l, R PP (∑ j, c j • β j + w) l = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c l)) + R PP w l := by
    intro PP hPP c w hw l
    rw [hsum PP Finset.univ c β w hβΛ hw]
    simp only [hβred _ PP hPP, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
    intro v hv
    choose c hc using fun j => GlobalTheory.T.exists_integer_conj_prescribed_residues_places D (Pg ∪ Q) (fun PP => R PP v j)
    have hw : v - ∑ j, c j • β j ∈ C.X.Λ := sub_mem hv (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have hw0 : v - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      refine (Iker _ hw).1 fun PP hPP => ?_
      funext l
      have h := hexp PP hPP c _ hw l
      rw [add_sub_cancel, hc l PP hPP] at h
      simp only [Pi.zero_apply]
      linear_combination -h
    have e1 : v = ∑ j, c j • β j + (v - ∑ j, c j • β j) := by abel
    rw [e1]
    exact Submodule.add_mem_sup (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) hw0
  obtain ⟨Lv0, hw⟩ := GlobalTheory.Ker.Base.exists_level C.X
  have hle : ∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftLevel.liftI Pg Q ≤ conjI PP.asIdeal := fun PP h => GlobalTheory.LiftDat.liftI_le h
  have hnot : ∀ PP ∈ Pg ∪ Q, ∀ s : 𝓞 D.host.E, IsCoprime (Ideal.span {s}) (GlobalTheory.LiftLevel.liftI Pg Q) →
      GlobalTheory.SW.Lev.bar s ∉ PP.asIdeal := by
    intro PP hPP s hs hmem
    obtain ⟨x, m, hm, hxm⟩ := GlobalTheory.SW.Lev.cop_iff.1 hs
    have h1m : (1 : 𝓞 D.host.E) ∈ conjI PP.asIdeal := by
      rw [← hxm]
      exact add_mem (Ideal.mul_mem_left _ _ (GlobalTheory.SW.Lev.mem_conjI.2 hmem)) (hle PP hPP hm)
    have := GlobalTheory.SW.Lev.mem_conjI.1 h1m
    rw [map_one] at this
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hind : ∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 →
      ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
    intro d ⟨s, hs, hsm⟩ j
    rw [sub_zero, Finset.smul_sum] at hsm
    have e2 : ∑ j, s • d j • β j = ∑ j, (s * d j) • β j + 0 := by
      rw [add_zero]; exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm
    rw [e2] at hsm
    refine GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place D Pg Q _ fun PP hPP => ?_
    have h0 := hexp PP hPP (fun j => s * d j) 0 (zero_mem _) j
    have hmemΛ : ∑ j, (s * d j) • β j + 0 ∈ C.X.Λ :=
      add_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j)) (zero_mem _)
    rw [(Iker _ hmemΛ).2 hsm PP hPP, hz] at h0
    simp only [Pi.zero_apply, add_zero, map_mul] at h0
    have h0' : GlobalTheory.SW.Lev.bar s * GlobalTheory.SW.Lev.bar (d j) ∈ PP.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_mul]; exact h0.symm)
    rcases PP.isPrime.mem_or_mem h0' with h | h
    · exact absurd h (hnot PP hPP s hs)
    · exact GlobalTheory.SW.Lev.mem_conjI.2 h
  refine ⟨GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0, rfl, hw, ?_, ?_⟩
  · intro κ hκ κ' hκ' PP hPP i j
    have hm := GlobalTheory.LiftDat.mem_Jgrp.1 hκ PP hPP
    have hij := congrArg (fun g : GL (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal) => g.val i j) hm
    have hk := congrFun (congrFun hκ' i) j
    change (GlobalTheory.LiftDat.toConj Pg Q PP (Finset.mem_union_left _ hPP)) (κ.val i j) =
      (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j at hij
    simp only [Matrix.map_apply] at hk
    rw [← hk] at hij
    have hij2 : Ideal.Quotient.mk (conjI PP.asIdeal) (κ' i j) =
        (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ conjI PP.asIdeal)) i j := hij
    rw [← Ideal.Quotient.eq, hij2]
    by_cases hij' : i = j
    · subst hij'; simp
    · simp [Matrix.one_apply_ne hij']
  · intro y hy
    have hrow : ∀ i, y i ∈ C.X.Λ := by
      intro i
      have key : ∀ z ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI (GlobalTheory.LiftLevel.liftI Pg Q)) • C.X.Λ),
          z i ∈ C.X.Λ := by
        intro z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨v, hv, u, hu, rfl⟩ := hz
          have hvi : IsIntegral ℤ (v i) := (GlobalTheory.SW.Base.mem_stdL _).1 hv i
          have : vecMulVec v u i = (⟨v i, hvi⟩ : 𝓞 D.host.E) • u := by
            funext k; rw [vecMulVec_apply, Pi.smul_apply, Algebra.smul_def]; rfl
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.smul_le_right hu)
        | zero => exact zero_mem _
        | add x y _ _ hx hy => exact add_mem hx hy
        | neg x _ hx => exact neg_mem hx
      exact key y hy
    have hdec : ∀ i, ∃ c : Fin T.rank → 𝓞 D.host.E, y i - ∑ j, c j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ := by
      intro i
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hsp (hrow i))
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hp
      refine ⟨c, ?_⟩
      rw [hc, ← hpq, add_sub_cancel_left]
      exact hq
    choose c hc using hdec
    refine GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters D S T C hn Pg Q ξ h1 h2 h3 h4 β hβΛ hsp Lv0 hind y c hc _ ?_
    intro PP hPP i j
    rw [Irow]
    have hw : y i - ∑ j, c i j • β j ∈ C.X.Λ := sub_mem (hrow i) (sum_mem fun j _ => Submodule.smul_mem _ _ (hβΛ j))
    have h := hexp PP hPP (c i) _ hw j
    rw [add_sub_cancel, (Iker _ hw).2 (hc i) PP hPP, Pi.zero_apply, add_zero] at h
    exact h

end GlobalTheory.LiftDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  first | exact @GlobalTheory.LiftDat.level_datum_eq | exact GlobalTheory.LiftDat.level_datum_eq | (intros; apply GlobalTheory.LiftDat.level_datum_eq <;> assumption)
end
