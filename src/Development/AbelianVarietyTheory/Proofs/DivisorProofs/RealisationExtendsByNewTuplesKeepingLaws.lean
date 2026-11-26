module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSideV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlaces
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SublevelFinIndex

variable {E : Type} [Field E] [NumberField E]

variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]

theorem parLev_anti (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) (h : D.Q ⊆ Q') :
    parLev hc J β { D with Q := Q', xq := xq } ≤ parLev hc J β D := by
  intro x hx
  have h2 : x ∈ ⨅ PP ∈ Q', parah β PP (blk2 D.r) := hx.2
  have h3 : x ∈ ⨅ PP ∈ D.Q, parah β PP (blk2 D.r) :=
    Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 PP) (h hP)
  exact ⟨hx.1, h3⟩

theorem lev_of_red (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) {x : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)}
    (hx : x ∈ lev hc J β D) (hr : ∀ PP ∈ Q', redFn β PP x = 1) : x ∈ lev hc J β { D with Q := Q', xq := xq } := by
  refine ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨parLev_St hx.1, ?_⟩⟩, hx.2⟩
  rw [hr PP hP]
  exact Subgroup.one_mem _

end GlobalTheory.SublevelFinIndex


open GlobalTheory.SublevelFinIndex in
theorem GlobalTheory.sublevel_finiteIndex : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  intro D V β Λ _ L Q' xq hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flag1L L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L))
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flagL L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL L))
  · refine ⟨Formalism.UG.P.levelv_relIndex_ne_zero _ _
      (fun (g : Bridge.Gf V) (PP : ↥Q') => redFn β PP.1 (Formalism.UG.bc (Lev.swapAE D) g.1)) ?_⟩
    intro a ha b hb hab
    have hab' : Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) :=
      (levEnv V β L).J.mul_mem ((levEnv V β L).J.inv_mem ha) hb
    have ha' : Formalism.UG.bc (Lev.swapAE D) a.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := ha
    have hb' : Formalism.UG.bc (Lev.swapAE D) b.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hb
    show Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq })
    refine lev_of_red D.sp.cm V.gram β (Lev.flag1L L) Q' xq hab' fun PP hP => ?_
    have e := congrFun hab ⟨PP, hP⟩
    have hSa := parLev_St ha'.1
    have hSb := parLev_St hb'.1
    simp only at e
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, redFn_mul ((St β).inv_mem hSa) hSb, redFn_inv hSa, e,
      inv_mul_cancel]
  · intro g hgQ hgJ
    have h1 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hgQ
    have h2 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hgJ
    exact (⟨h1.1, h2.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricSublevel_finiteIndex_more_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  first | exact @GlobalTheory.sublevel_finiteIndex | exact GlobalTheory.sublevel_finiteIndex | (intros; apply GlobalTheory.sublevel_finiteIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocks
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerParahoric

open GlobalTheory.LevelProduct

theorem exists_cut {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : GA D V) (hS : Lev.finE V h ∈ St β)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ k : GA D V, Lev.finE V k ∈ St β ∧ ∀ PP : Pl D.host.E,
      ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S → redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h)) ∧
      ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ S → redFn β PP (Lev.finE V k) = 1) := by
  induction S using Finset.cons_induction_on with
  | empty =>
    refine ⟨1, ?_, fun PP => ⟨fun hh => absurd hh (Finset.notMem_empty _), fun _ => ?_⟩⟩
    · rw [MonoidHom.map_one]; exact Subgroup.one_mem _
    · rw [MonoidHom.map_one]; exact redFn_one PP
  | cons v S hv ih =>
    obtain ⟨k, hk, hr⟩ := ih
    have hc : Lev.finE V (cmp V v h) ∈ St β := by
      rw [finE_cmp]; exact piece_mem_St (phi_idem v) (phi_idem' v) hS
    have hpos : ∀ PP : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = redFn β PP (Lev.finE V h) := fun PP e => by
      rw [finE_cmp]; exact redFn_piece (phi_idem v) (phi_idem' v) hS PP (resS_phi_pos e)
    have hneg : ∀ PP : Pl D.host.E, ¬ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v →
        redFn β PP (Lev.finE V (cmp V v h)) = 1 := fun PP e => by
      rw [finE_cmp] at hc ⊢; exact redFn_piece_eq_one (phi_idem' v) hc PP (resS_phi_neg e)
    refine ⟨cmp V v h * k, ?_, fun PP => ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hc hk
    · rw [MonoidHom.map_mul, redFn_mul hc hk, Finset.mem_cons]
      by_cases e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
      · refine ⟨fun _ => ?_, fun hn => absurd (Or.inl e) hn⟩
        rw [hpos PP e, (hr PP).2 (e ▸ hv), mul_one]
      · rw [hneg PP e, one_mul]
        exact ⟨fun hh => (hr PP).1 (hh.resolve_left e), fun hh => (hr PP).2 fun h' => hh (Or.inr h')⟩


set_option maxHeartbeats 1600000 in
theorem exists_mem_smaller : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  classical
  intro D V β Λ _ L Q' xq hQ hoff g hg
  obtain ⟨_, h, rfl⟩ := g
  have hh : Lev.finE V h ∈ lev D.sp.cm V.gram β (Lev.flagL L) := hg
  obtain ⟨-, hS, hP, hq⟩ := mem_parLev.1 (lev_le_parLev hh)
  obtain ⟨k, hk, hr⟩ := exists_cut V β h hS (L.Pg.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have h1 : ∀ PP ∈ L.Pg, redFn β PP (Lev.finE V k) = redFn β PP (Lev.finE V h) := fun PP hPP =>
    (hr PP).1 (Finset.mem_image_of_mem _ hPP)
  have h2 : ∀ PP ∈ Q', redFn β PP (Lev.finE V k) = 1 := fun PP' hPP' => (hr PP').2 fun hm => by
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨a, b, -⟩ := hoff PP hPP PP' hPP'
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact a e'.symm
    · refine b ?_
      rw [e']
      exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩
  have hS' : Lev.finE V h⁻¹ ∈ St β := by rw [MonoidHom.map_inv]; exact Subgroup.inv_mem _ hS
  have h3 : ∀ PP, redFn β PP (Lev.finE V (h⁻¹ * k)) = (redFn β PP (Lev.finE V h))⁻¹ * redFn β PP (Lev.finE V k) :=
    fun PP => by rw [MonoidHom.map_mul, redFn_mul hS' hk, MonoidHom.map_inv, redFn_inv hS]
  have A : Lev.finE V k ∈ lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V k, hk, fun PP hPP => ?_, fun PP hPP => ?_⟩,
      Subgroup.mem_top _⟩
    · rw [h1 PP hPP]; exact hP PP hPP
    · rw [h2 PP hPP]; exact Subgroup.one_mem _
  have B : Lev.finE V (h⁻¹ * k) ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := by
    refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, ?_, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · rw [MonoidHom.map_mul]; exact Subgroup.mul_mem _ hS' hk
    · rw [h3, h1 PP hPP, inv_mul_cancel]; exact Subgroup.one_mem _
    · rw [h3, h2 PP (hQ hPP), mul_one]; exact Subgroup.inv_mem _ (hq PP hPP)
    · have e : rTup β (Lev.flag1L L) (Lev.finE V (h⁻¹ * k)) = 1 := by
        funext PP
        show upperLeftBlock L.hr (redFn β PP.1 (Lev.finE V (h⁻¹ * k))) = 1
        rw [h3, h1 PP.1 PP.2, inv_mul_cancel]; exact blockDiagonalExtendByOnePrimeField_one _ _
      rw [e]; exact Subgroup.one_mem _
  refine ⟨(finHom V).rangeRestrict k, A, ?_⟩
  have e : (⟨finHom V h, h, rfl⟩ : Bridge.Gf V)⁻¹ * (finHom V).rangeRestrict k = (finHom V).rangeRestrict (h⁻¹ * k) := by
    apply Subtype.ext
    exact ((MonoidHom.map_mul (finHom V) _ _).trans (congrArg (· * finHom V k) (MonoidHom.map_inv (finHom V) h))).symm
  rw [e]
  exact B

end GlobalTheory.SmallerParahoric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocksStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → ∀ g ∈ (levEnv V β L).Q, ∃ g' ∈ (levEnv V β { L with Q := Q', xq := xq }).Q, g⁻¹ * g' ∈ (levEnv V β L).J := by
  first | exact @GlobalTheory.SmallerParahoric.exists_mem_smaller | exact GlobalTheory.SmallerParahoric.exists_mem_smaller | (intros; apply GlobalTheory.SmallerParahoric.exists_mem_smaller <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatLevel

theorem hLat_mul_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  intro D V β Λ hΛ L y k hk
  have h : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  have hq : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ St β := parLev_St h.1
  have hf : (1 : Bridge.Gf V).1 = Formalism.UG.bc (inclR (F := D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (1 : GL (Fin V.rank) D.host.E) := by
    rw [map_one]; exact OneMemClass.coe_one _
  have e := GlobalTheory.HLatMove.hLat_mul hΛ 1 y k 1 hf hq
  rw [one_mul] at e
  rw [e]
  ext x
  simp
end GlobalTheory.HLatLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_invariant_under_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  first | exact @GlobalTheory.HLatLevel.hLat_mul_lev | exact GlobalTheory.HLatLevel.hLat_mul_lev | (intros; apply GlobalTheory.HLatLevel.hLat_mul_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isDC_of_smaller_level_same_local {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G)
    (hJJ : J' ≤ J) (hLc : J ⊓ Lc ≤ J')
    (hdec : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y)
    (hx : x ∈ Lc) (hA : ∀ a ∈ A, a ∈ Lc) (hDC : Bridge.IsDC J x A) : Bridge.IsDC J' x A := by
  obtain ⟨h1, h2⟩ := hDC
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := h1 a ha
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k hk
    obtain ⟨k₁', hk₁'J, k₂', hk₂'J, hk₁'L, rfl, -⟩ := hdec k' hk'
    have e : k₁ * k₂ * x * (k₁' * k₂') = k₁ * x * k₁' * (k₂ * k₂') := by
      have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
      have c2 : k₂ * k₁' = k₁' * k₂ := (hk₂c k₁' hk₁'L).eq
      calc k₁ * k₂ * x * (k₁' * k₂') = k₁ * (k₂ * x) * k₁' * k₂' := by group
        _ = k₁ * x * (k₂ * k₁') * k₂' := by rw [c1]; group
        _ = k₁ * x * (k₁' * k₂) * k₂' := by rw [c2]
        _ = k₁ * x * k₁' * (k₂ * k₂') := by group
    have haL := hA _ ha
    have hprodL : k₂ * k₂' ∈ Lc := by
      have : k₂ * k₂' = (k₁ * x * k₁')⁻¹ * (k₁ * k₂ * x * (k₁' * k₂')) := by rw [e]; group
      rw [this]
      exact Lc.mul_mem (Lc.inv_mem (Lc.mul_mem (Lc.mul_mem hk₁L hx) hk₁'L)) haL
    have hprod : k₂ * k₂' ∈ J' := hLc ⟨J.mul_mem hk₂J hk₂'J, hprodL⟩
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₁' : k₁' ∈ J' := hLc ⟨hk₁'J, hk₁'L⟩
    refine ⟨⟨k₁, hk₁⟩, ⟨k₁' * (k₂ * k₂'), J'.mul_mem hk₁' hprod⟩, ?_⟩
    simp only
    rw [e]; group
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := hg
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k (hJJ hk)
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₂ : k₂ ∈ J' := by
      have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [this]; exact J'.mul_mem (J'.inv_mem hk₁) hk
    obtain ⟨a, ⟨haA, haJ⟩, -⟩ := h2 (k₁ * x) ⟨⟨k₁, hk₁J⟩, 1, by simp⟩
    have haL : a⁻¹ * (k₁ * x) ∈ Lc := Lc.mul_mem (Lc.inv_mem (hA a haA)) (Lc.mul_mem hk₁L hx)
    have haJ' : a⁻¹ * (k₁ * x) ∈ J' := hLc ⟨haJ, haL⟩
    have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
    refine ⟨a, ⟨haA, ?_⟩, ?_⟩
    · have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
        calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
          _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
      rw [this]
      exact J'.mul_mem haJ' (J'.mul_mem hk₂ hk')
    · rintro b ⟨hbA, hbJ'⟩
      have hgJ : ∃ m₁ m₂ : J, k₁ * k₂ * x * k' = (m₁ : G) * x * m₂ :=
        ⟨⟨k₁ * k₂, hJJ hk⟩, ⟨k', hJJ hk'⟩, rfl⟩
      obtain ⟨c, -, hc⟩ := h2 _ hgJ
      have haJg : a⁻¹ * (k₁ * k₂ * x * k') ∈ J := by
        have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
          calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
            _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
        rw [this]; exact J.mul_mem haJ (J.mul_mem hk₂J (hJJ hk'))
      rw [hc b ⟨hbA, hJJ hbJ'⟩, hc a ⟨haA, haJg⟩]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local : ∀ {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G), J' ≤ J → J ⊓ Lc ≤ J' → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y) → x ∈ Lc → (∀ a ∈ A, a ∈ Lc) → Bridge.IsDC J x A → Bridge.IsDC J' x A := by
  first | exact @GlobalTheory.isDC_of_smaller_level_same_local | exact GlobalTheory.isDC_of_smaller_level_same_local | (intros; apply GlobalTheory.isDC_of_smaller_level_same_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerLevelHecke
open Formalism.IndefR.Lev _root_.Formalism.L2.NTheta GlobalTheory.SplitHeckeAdj

theorem local_group_two {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L L' : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1)
    (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (he : IsIdemAt e P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (hoff' : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ g, SuppAt e V g → fin V g ∈ Lc) ∧
      (∀ g, SuppAt e V g → fin V g⁻¹ ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l) ∧
      (levEnv V β L).J ⊓ Lc ≤ (levEnv V β L').J := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hP
  have hff := h01.1
  have hcf := h01.2.1
  have h02 := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hff hcf).1
  refine h02.elim fun L₀ hL₀ => ?_
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e _ hP h1 hoff
  have hK' := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L') hβ).2 P e _ hP h1 hoff').1
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hL : ∀ g, g ∈ L₀ ↔ SuppAt e V g := hL₀
  have h04 := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  have h05 := transport_local (fin V) (GfC V) (levG V β (flag1L L)) L₀ (levEnv V β L).J (SuppAt e V)
    (SuppF V (1 - (e + cA D e))) (KsphC V ∅) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L))
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L) (fun g hg => hg.1) hL (fun g => supp_fin V he)
    (fun g g' => commute_compl V _ hff hcf) (fun g => chi_eq V β L) hK hχ hsp h04
  refine ⟨L₀.map (fin V), fun g hg => ⟨g, (hL g).2 hg, rfl⟩,
    fun g hg => ⟨g⁻¹, L₀.inv_mem ((hL g).2 hg), rfl⟩, h05.1, ?_⟩
  rintro _ ⟨hj, g, hg, rfl⟩
  have a := (hL g).1 hg
  have b := supp_fin V he a
  exact (mem_J V β L' b).2 ((hK' g a).2 ((hK g a).1 ((mem_J V β L b).1 hj)))

theorem isDC_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  intro D V β Λ hSD L Q' xq hQ Pl0 pl ok i hoff hi x A hx hA hDC
  have hle := (GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ).1
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  obtain ⟨α, ⟨e, ϖ, he, -, -, hα⟩, hxα⟩ := hx hi
  obtain ⟨Lc, l1, l2, l3, l4⟩ := local_group_two V β Λ L { L with Q := Q', xq := xq } hβ (pl i.1) e he
    (fun PP h => hoff PP (h.imp_right fun h' => hQ h')) hoff
  have e1 : x = fin V α⁻¹ := Subtype.ext hxα
  refine GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local _ _ Lc x A hle l4 l3 ?_ (fun a ha => ?_) hDC
  · rw [e1]
    exact l2 α hα.2.1
  · obtain ⟨g, hg, rfl⟩ := loc_supp V (hA a ha) he
    exact l1 g hg

end GlobalTheory.SmallerLevelHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_representatives_split_place_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  first | exact @GlobalTheory.SmallerLevelHecke.isDC_smaller_level | exact GlobalTheory.SmallerLevelHecke.isDC_smaller_level | (intros; apply GlobalTheory.SmallerLevelHecke.isDC_smaller_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatMatExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharChange
open Formalism.IndefR.Lev

theorem ratMat_exists {D : D7} (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  have h := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨γE, -, e⟩ := Subgroup.mem_map.1 h
  exact ⟨γE, e.symm⟩

theorem flag_vals {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hcg : ∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ))
    (hxq : ∀ PP ∈ L.Q, ∀ x, ∃ a, D.what₂.embLL a = ((L.xq PP x : ℂˣ) : ℂ)) (x) :
    ∃ a, D.what₂.embLL a = ((levFn β (flagL L) x : ℂˣ) : ℂ) := by
  have h1 : (flagL L).P.chi = 1 := rfl
  unfold levFn
  rw [h1, subgroupCharExtension_one_apply, one_mul]
  refine RingHom.mem_fieldRange.1 ?_
  simp only [Units.val_mul, Units.coe_prod]
  refine Subfield.mul_mem _ (Subfield.prod_mem _ fun PP hP => Subfield.prod_mem _ fun j hj => ?_)
    (Subfield.prod_mem _ fun PP hP => ?_)
  · obtain ⟨a, ha⟩ := hcg j (Finset.mem_range.1 hj) PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := hxq PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩

end GlobalTheory.TwistCharChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SubLevel

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Gen

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

def dcRel (J' : Subgroup G) : Setoid G where
  r h h' := ∃ (γ : Γ) (k : J'), h' = ι γ * h * (k : G)
  iseqv := {
    refl := fun h => ⟨1, 1, by simp⟩
    symm := fun {h h'} ⟨γ, k, e⟩ => ⟨γ⁻¹, k⁻¹, by rw [e, map_inv, Subgroup.coe_inv]; group⟩
    trans := fun {h h' h''} ⟨γ, k, e⟩ ⟨γ₂, k₂, e₂⟩ =>
      ⟨γ₂ * γ, k * k₂, by rw [e₂, e, map_mul, Subgroup.coe_mul]; group⟩ }

theorem stab_mono_mem {J J' : Subgroup G} (hJ : J' ≤ J) {y k : G} (hk : k ∈ J) {g : Γ}
    (hg : g ∈ stab ι J' (y * k)) : g ∈ stab ι J y := by
  rw [mem_stab ι] at hg ⊢
  have h1 : (y * k)⁻¹ * ι g * (y * k) ∈ J := hJ hg
  have e : y⁻¹ * ι g * y = k * ((y * k)⁻¹ * ι g * (y * k)) * k⁻¹ := by group
  rw [e]
  exact J.mul_mem (J.mul_mem hk h1) (J.inv_mem hk)

end Gen

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (J' : Subgroup G)

def yN (c : Quotient (dcRel ι J')) : G := P.y (P.decC c.out) * (P.decK c.out : G)

theorem yN_rel (c : Quotient (dcRel ι J')) : (dcRel ι J').r (yN P J' c) c.out := by
  show ∃ (γ : Γ) (k : J'), c.out = ι γ * yN P J' c * (k : G)
  refine ⟨P.decG c.out, 1, ?_⟩
  show c.out = ι (P.decG c.out) * (P.y (P.decC c.out) * (P.decK c.out : G)) * ((1 : J') : G)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc]
  exact P.dec_spec c.out

theorem mk_yN (c : Quotient (dcRel ι J')) : Quotient.mk (dcRel ι J') (yN P J' c) = c :=
  (Quotient.sound (yN_rel P J' c)).trans (Quotient.out_eq c)

theorem reps_new : IsReps ι J' (yN P J') := by
  intro h
  refine ⟨Quotient.mk (dcRel ι J') h, ?_, ?_⟩
  · exact Quotient.exact (mk_yN P J' (Quotient.mk (dcRel ι J') h))
  · rintro i ⟨γ, k, e⟩
    have hr : (dcRel ι J').r (yN P J' i) h := ⟨γ, k, e⟩
    exact (mk_yN P J' i).symm.trans (Quotient.sound hr)

theorem stabN_finite (hJ : J' ≤ J) (c : Quotient (dcRel ι J')) : Finite (stab ι J' (yN P J' c)) := by
  haveI : Finite (stab ι J (P.y (P.decC c.out))) := Finite.of_equiv _ (P.stabI (P.decC c.out)).toEquiv
  refine Finite.of_injective
    (fun g : stab ι J' (yN P J' c) =>
      (⟨(g : Γ), stab_mono_mem ι hJ (P.decK c.out).2 g.2⟩ : stab ι J (P.y (P.decC c.out)))) ?_
  intro a b hab
  have hv := congrArg Subtype.val hab
  exact Subtype.ext hv

include P in
theorem cl_finite (hfi : (J'.subgroupOf J).FiniteIndex) : Finite (Quotient (dcRel ι J')) := by
  haveI := hfi
  refine Finite.of_surjective
    (fun p : S.Cl × (J ⧸ J'.subgroupOf J) => Quotient.mk (dcRel ι J') (P.y p.1 * ((p.2.out : J) : G))) ?_
  intro c
  obtain ⟨d, γ, k, e⟩ : ∃ (d : S.Cl) (γ : Γ) (k : J), c.out = ι γ * P.y d * (k : G) :=
    ⟨_, _, _, P.dec_spec c.out⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (s := J'.subgroupOf J) k
  have hjJ' : ((j : J) : G) ∈ J' := Subgroup.mem_subgroupOf.1 j.2
  refine ⟨(d, (QuotientGroup.mk k : J ⧸ J'.subgroupOf J)), ?_⟩
  show Quotient.mk (dcRel ι J') (P.y d * (((QuotientGroup.mk k : J ⧸ J'.subgroupOf J).out : J) : G)) = c
  rw [hj]
  have hr : (dcRel ι J').r (P.y d * ((k * (j : J) : J) : G)) c.out := by
    refine ⟨γ, ⟨((j : J) : G)⁻¹, J'.inv_mem hjJ'⟩, ?_⟩
    show c.out = ι γ * (P.y d * ((k : G) * ((j : J) : G))) * ((j : J) : G)⁻¹
    rw [e]
    group
  exact (Quotient.sound hr).trans (Quotient.out_eq c)

variable (χ' : J' →* ℂˣ) (hχ' : ∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoG (y : G) (g : stab ι J' y) (x : S.V) : W :=
  (χ' (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoG_rg (y : G) (g : stab ι J' y) (x : S.V) : InRg P (rhoG P J' χ' y g x) := by
  obtain ⟨x', hx'⟩ := hρ (g : Γ) x
  obtain ⟨a, ha⟩ := hχ' (stabK ι g)
  refine ⟨a • x', ?_⟩
  rw [map_smulₛₗ, hx', ha]
  rfl

def rhoGE (y : G) (g : stab ι J' y) : Module.End K S.V where
  toFun x := cinv P (rhoG P J' χ' y g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add (f := _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _),
      coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_add (f := _), smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoGE (y : G) (g : stab ι J' y) (x : S.V) :
    P.coef (rhoGE P J' χ' hχ' hρ y g x) = rhoG P J' χ' y g x :=
  coef_cinv P (rhoG_rg P J' χ' hχ' hρ y g x)

def rhoGN (y : G) : stab ι J' y →* Module.End K S.V where
  toFun := rhoGE P J' χ' hχ' hρ y
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoGE]
    simp [rhoG, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoGE, coef_rhoGE]
    simp only [rhoG, coef_rhoGE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

end Main

end GlobalTheory.SubLevel

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.SubLevel

theorem classPres_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  intro G Γ _ _ ι W _ _ K _ _ _ σ S ρ J χ P J' hJ hfi χ' hχ' hρ
  haveI : Finite (Quotient (SubLevel.dcRel ι J')) := SubLevel.cl_finite P J' hfi
  letI fC : Fintype (Quotient (SubLevel.dcRel ι J')) := Fintype.ofFinite _
  haveI hfS : ∀ c, Finite (stab ι J' (SubLevel.yN P J' c)) := fun c => SubLevel.stabN_finite P J' hJ c
  letI fG : ∀ c, Fintype (stab ι J' (SubLevel.yN P J' c)) := fun c => Fintype.ofFinite _
  exact ⟨Quotient (SubLevel.dcRel ι J'), fC, fun c => P.decC c.out, fun c => P.decK c.out,
    fun c => stab ι J' (SubLevel.yN P J' c), fun c => inferInstance, fG,
    fun c => SubLevel.rhoGN P J' χ' hχ' hρ (SubLevel.yN P J' c),
    { y := SubLevel.yN P J'
      reps := SubLevel.reps_new P J'
      stabI := fun c => MulEquiv.refl _
      coef := P.coef
      coef_li := P.coef_li
      coef_span := P.coef_span
      coef_pair := P.coef_pair
      coef_act := fun c g x => SubLevel.coef_rhoGE P J' χ' hχ' hρ (SubLevel.yN P J' c) g x },
    fun c => rfl, rfl⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPres_of_finiteIndex_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  first | exact @GlobalTheory.classPres_subLevel | exact GlobalTheory.classPres_subLevel | (intros; apply GlobalTheory.classPres_subLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PresHecke

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Raw

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} {inR : I → Prop} {isT isLoc : I → G → Prop}

theorem keepsDcRaw (P : ClassPres ι S σ ρ J χ) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (i : I) (hi : inR i) : Keeps P (dcL (W := W) (hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (hok i hi).2.2 Lc (fun a ha => hL1 _ ((hok i hi).2.1 a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _


open Classical in
def opRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keepsDcRaw P hx hA hok hloc i hi) else if one i then 1 else 0

def heckeRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) : HeckeTie ι P (opRaw P hχ hρ hx hA hok hloc one) inR isT isLoc where
  hx := hx
  hA := hA
  hx_ok i hi := (hok i hi).1
  hA_loc i hi := (hok i hi).2.1
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC i hi := (hok i hi).2.2
  op_eq i hi f := by
    unfold opRaw
    rw [dite_eq_left hi, ext_trE]
    rfl

end Raw

end GlobalTheory.PresHecke

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange GlobalTheory.PresHecke

theorem sideReal_ofPres : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  intro G Γ _ _ ι I c l isT isLoc K _ _ _ σ S G0 _ inR P hσ hρ red hsurj hker hx hA hok hloc one
  have hχ : ∀ k : l.J, ∃ b : K, σ b = (l.χ k : ℂ) := fun k => by rw [← l.ch_J]; exact hσ _
  exact ⟨actNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ,
    opRaw P hχ hρ hx hA hok hloc one,
    ⟨P, actTieNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ, heckeRaw P hχ hρ hx hA hok hloc one⟩,
    rfl, rfl, fun i hi => ⟨fun ho => by simp [opRaw, hi, ho], fun ho => by simp [opRaw, hi, ho]⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperatorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  first | exact @GlobalTheory.sideReal_ofPres | exact GlobalTheory.sideReal_ofPres | (intros; apply GlobalTheory.sideReal_ofPres <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm


set_option maxHeartbeats 3200000 in
theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 N : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
  {j : Fin D.R.m} {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X)


set_option maxHeartbeats 2000000 in
theorem baseOf_ext {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (extR R Y) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩


set_option maxHeartbeats 2000000 in
theorem ext_ext : Ext T R κ v₀ O j (extR R Y) v₀ (fun i => omExt Y (O i)) := by
  refine ⟨fun τ h => (fixBase_ext Y j τ).2 h, fun τ ζ Φ Φ' h => ?_, ?_⟩
  · exact (h)
  · exact (by with_unfolding_all exact ((Ext.refl (T := T) (R := R) (κ := κ) (v₀ := v₀) (O := O) (j := j)).2.2 :))

end


set_option maxHeartbeats 2000000 in
theorem extend_tuples : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  intro h1 _ _ h4 h5 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL N _ χ xi Q xiR hV hi hn hQ
  obtain ⟨hC, hfin, ⟨hfw⟩, hio, hg, hp, hph, hB⟩ := hL
  let V : NewLev D N := ⟨χ, xi, Q, xiR⟩
  have hL' : (extL R.toLevCh V).Is (.inl A.μ0) := by
    have hL := hC.lev
    exact
      { mu0 := hL.mu0
        eta := hL.eta
        xi := Sum.rec hL.xi fun n => (hV n).xi
        xi_inj := by
          rintro (t | n) (t' | n') h
          · exact congrArg _ (hL.xi_inj h)
          · exact absurd h.symm (hn n' t)
          · exact absurd h (hn n t')
          · exact congrArg _ (hi h)
        xi_base := hL.xi_base
        xi_fin := Sum.rec hL.xi_fin fun n => (hV n).xi_fin
        xi_triv := Sum.rec hL.xi_triv fun n => (hV n).xi_triv
        xi_tame := Sum.rec hL.xi_tame fun n => (hV n).xi_tame
        Pg := hL.Pg
        Q_pl := Sum.rec hL.Q_pl fun n => (hV n).Q_pl
        Q_off := Sum.rec hL.Q_off fun n => (hV n).Q_off
        Q_de p hp := (hQ p hp).imp fun _ h => Sum.rec h.1 h.2
        Q_ram := Sum.rec hL.Q_ram fun n => (hV n).Q_ram
        chi := hL.chi
        xiR := Sum.rec hL.xiR fun n => (hV n).xiR
        βY := hL.βY
        βX := hL.βX
        βV := hL.βV
        βW := hL.βW }
  obtain ⟨X, Y0, h0⟩ := fam_stage (GlobalTheory.SideLevel.sideReal_moreLevel) hC hL' hV
  obtain ⟨Y, hC', hT⟩ := core_ext h4 GlobalTheory.HcPort.print_harishChandraModules h1 h5 (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hC hL' Y0 h0
  have hg' : QGuard (extR R Y) := ⟨Sum.rec hg.1 fun n => (hV n).half, Sum.rec hg.2 fun n => (hV n).guard⟩
  exact ⟨T0 ⊕ N, extA A X, extR R Y, extF F X, v₀, fun i => omExt Y (O i),
    ⟨hC', inferInstance, ⟨fwExt Y hfw⟩, ioExt_ext R Y hio, hg', omPins_ext Y hT hp, phaseTie_ext Y hph, baseOf_ext Y hB⟩,
    ext_ext Y, fun n => ⟨.inr n, rfl, rfl⟩⟩

end GlobalTheory.TupExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLawsStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  first | exact @GlobalTheory.TupExt.extend_tuples | exact GlobalTheory.TupExt.extend_tuples | (intros; apply GlobalTheory.TupExt.extend_tuples <;> assumption)
end
