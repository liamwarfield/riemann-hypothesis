module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
namespace GlobalTheory.Mem.R3.DefLatBC

theorem gsdbc_round_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ b : Formalism.L2.Col.GSDBC ι (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁)
      (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
        (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
          fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂),
      ∀ (ψ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun) d₁ d₂,
        HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((b.lift ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  refine ⟨Formalism.L2.Col.hfsFormBC ι F (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := _) => d.1.N)
    ((Formalism.L2.DIV.rhoVr (X.coefExt L ι).emb lam).comp (Formalism.L2.Col.ufGL X.E n)) (Formalism.L2.DIV.pairVr (X.coefExt L ι).emb lam 1)
    (fun d => Formalism.L2.DIV.nabAtr (X.coefExt L ι).emb lam d.1.N) (fun d => Formalism.L2.DIV.delAtr (X.coefExt L ι).emb lam d.1.N)
    (fun γ v => Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n γ) v) Λ₁, fun ψ d₁ d₂ hd => ?_⟩
  obtain rfl : d₂ = d₁ := eq_of_heq hd
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  exact heq_of_eq ((MvPolynomial.map_map ι c₂ _).trans (by rw [hc']; rfl))

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


set_option maxHeartbeats 4000000 in
theorem gsdbc_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)), ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  generalize hk : (j : ℕ) + 1 = k
  generalize hk' : (j' : ℕ) + 1 = k'
  obtain rfl : k' = k := by rw [← hk, ← hk', hj]
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.DefLatBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValuesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsData_extendedData_baseChange_sameValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)), ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext | exact GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelsExtendedDataCorrespondFieldEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelsExtendedDataCorrespondFieldEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LevBC

theorem exists_intCast_of_card_prime {R : Type} [Ring R] (h : (Nat.card R).Prime) (x : R) : ∃ n : ℤ, (n : R) = x := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero h.ne_zero
  have htop : AddSubgroup.zmultiples (1 : R) = ⊤ := by
    rcases h.eq_one_or_self_of_dvd _ (AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : R))) with h1 | h1
    · exfalso
      have hb := AddSubgroup.eq_bot_of_card_eq _ h1
      have h10 : (1 : R) = 0 := by
        have : (1 : R) ∈ AddSubgroup.zmultiples (1 : R) := AddSubgroup.mem_zmultiples 1
        rw [hb] at this
        exact (AddSubgroup.mem_bot).1 this
      have : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
      rw [Nat.card_unique] at h
      exact Nat.not_prime_one h
    · exact AddSubgroup.eq_top_of_card_eq _ h1
  have hx : x ∈ AddSubgroup.zmultiples (1 : R) := by rw [htop]; exact AddSubgroup.mem_top x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact ⟨n, by rw [← hn, zsmul_one]⟩

theorem exists_intCast_vGs (B : Base) (px : PreX B.toPre) (PP : Pl B.host.E) (hPP : PP ∈ (B.primes px).vGs)
    (c : 𝓞 B.host.E ⧸ PP.asIdeal) : ∃ n : ℤ, (n : 𝓞 B.host.E ⧸ PP.asIdeal) = c := by
  classical
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B px
  have hi : ∃ i, PP ∈ (B.primes px).vG i := by
    rcases Finset.mem_union.1 hPP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hi
  have hn := hPr.vG_norm i PP hi
  have hp := hPr.g_prime i
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  rw [← hn] at hp
  exact exists_intCast_of_card_prime hp c

theorem baseLevelCharacter_map_coefficientRingHom {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {LL LL' : Type} [CommRing LL] [CommRing LL']
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (ψ' : ∀ PP : Pl E, AddChar (kP PP) LL') (φ : LL →+* LL')
    (h : ∀ PP ∈ Pg, ∀ c, ψ' PP c = φ (ψ PP c)) (x : (P0 Pg r ψ).H) (x' : (P0 Pg r ψ').H) (hx : (x : G0 Pg r) = x') :
    (((P0 Pg r ψ').chi x' : LL'ˣ) : LL') = φ (((P0 Pg r ψ).chi x : LLˣ) : LL) := by
  obtain ⟨x, hxm⟩ := x
  obtain ⟨x', hxm'⟩ := x'
  simp only at hx
  subst hx
  show ((((∏ PP : ↥Pg, (addCharHom (ψ' PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm'⟩ : LL'ˣ)) : LL') =
    φ (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm⟩ : LLˣ) : LL)
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ _ _ => rfl⟩
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, prod_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h PP.1 PP.2 _

theorem lev_bc (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (I : ColIn B px) (I' : ColIn B' px') (hI : I.Ok) (hI' : I'.Ok) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    (g' ∈ lev0 I' ↔ g ∈ lev0 I) ∧ ∀ (h0 : g ∈ lev0 I) (h0' : g' ∈ lev0 I'),
      ((chr0 I' ⟨g', h0'⟩ : B'.LLˣ) : B'.LL) = φ (chr0 I ⟨g, h0⟩ : B.LLˣ) := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp I I' hI hI' φ hφ g g' hg
  subst h
  cases hp
  cases hg
  refine ⟨Iff.rfl, fun h0 h0' => ?_⟩
  refine baseLevelCharacter_map_coefficientRingHom _ _ _ _ φ (fun PP hPP c => ?_) ⟨_, h0⟩ ⟨_, h0'⟩ rfl
  rw [psiC_of_mem _ hPP, psiC_of_mem I' hPP]
  obtain ⟨n, hn⟩ := exists_intCast_vGs _ _ PP hPP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
  have e1 := hI'.weil ⟨PP, hPP⟩ c n hn.symm
  have e2 := hI.weil ⟨PP, hPP⟩ c n hn.symm
  have e3 := hφ (I.Ch.psi0 ⟨PP, hPP⟩ c)
  exact RingHom.injective _ (e1.trans (e2.symm.trans e3.symm))

end GlobalTheory.Mem.R3.LevBC

namespace GlobalTheory.Mem.R3.Rw

theorem extN_baseLevel_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (g' ∈ (z'.F.lv2.lvl false).P ↔ g ∈ (z.F.lv2.lvl false).P) ∧ ∀ (hg : g ∈ (z.F.lv2.lvl false).P) (hg' : g' ∈ (z'.F.lv2.lvl false).P), (((z'.F.lv2.lvl false).ψ ⟨g', hg'⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.F.lv2.lvl false).ψ ⟨g, hg⟩ : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ g g' hg
  exact GlobalTheory.Mem.R3.LevBC.lev_bc B B' hE.1 w.px w'.px hpx w.I w'.I w.ok w'.ok φ hφ g g' hg

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelsExtendedDataCorrespondFieldEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevels_extendedData_correspond_fieldEmbedding : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (g' ∈ (z'.F.lv2.lvl false).P ↔ g ∈ (z.F.lv2.lvl false).P) ∧ ∀ (hg : g ∈ (z.F.lv2.lvl false).P) (hg' : g' ∈ (z'.F.lv2.lvl false).P), (((z'.F.lv2.lvl false).ψ ⟨g', hg'⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.F.lv2.lvl false).ψ ⟨g, hg⟩ : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  exact @GlobalTheory.Mem.R3.Rw.extN_baseLevel_bc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearFormsLiftSameComplexValues
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC.LiftExt


open _root_.Formalism.L2.Col in
set_option maxHeartbeats 1000000 in
private theorem liftHom_reidx (X : Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam₁ lam₂ : X.Tau → DomWeight n)
    (hl : lam₂ = lam₁) {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : LevFam X.E X.K n SG₁) (Λ₂ : LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ Lf : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun →+
      (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₂
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).EqFun,
      (∀ (a : X.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((Lf ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst lam₂
  subst SG₂
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have hmem : ∀ ψ : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun,
      (fun d => hfsJ ι lam₁ (ψ.1 d)) ∈ (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₁
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) (Λ₁.coefMap ι)).EqFun := by
    intro ψ
    obtain ⟨φ₂, h⟩ := GlobalTheory.Mem.R3.Tr.levelFamily_coefficientChange_liftRound X ι e he lam₁ Λ₁ (Λ₁.coefMap ι) (fun w => rfl)
      (fun w h₁ h₂ hh => by
        have : h₁ = h₂ := Subtype.ext hh
        subst this
        rfl) ψ
    have : (fun d => hfsJ ι lam₁ (ψ.1 d)) = φ₂.1 := funext fun d => Subtype.ext (h d).symm
    rw [this]
    exact φ₂.2
  refine ⟨{ toFun := fun ψ => ⟨fun d => hfsJ ι lam₁ (ψ.1 d), hmem ψ⟩, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Subtype.ext
    funext d
    exact map_zero _
  · intro ψ χ
    apply Subtype.ext
    funext d
    exact map_add _ _ _
  · intro a ψ
    apply Subtype.ext
    funext d
    exact hfsJ_smul ι lam₁ a (ψ.1 d)
  · intro ψ d₁ d₂ hd
    cases hd
    apply heq_of_eq
    show MvPolynomial.map c₂ (MvPolynomial.map ι (ψ.1 d₁).1) = _
    rw [MvPolynomial.map_map]
    have hc' : c₂.comp ι = c₁ := RingHom.ext hc
    rw [hc']


open _root_.Formalism.L2.Col in
private theorem formsLift_of_eqFunLift {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [StarRing K₁] [Field K₂] [NumberField K₂] [StarRing K₂]
    (ι : K₁ →+* K₂) (S₁ : GSD K₁) (S₂ : GSD K₂) (h₁ : S₁.Ok) (h₂ : S₂.Ok) (Lf : S₁.EqFun →+ S₂.EqFun)
    (hLf : ∀ (a : K₁) ψ, Lf (a • ψ) = ι a • Lf ψ) :
    ∃ L : (S₁.toCSD h₁).Forms →+ (S₂.toCSD h₂).Forms, (∀ (a : K₁) f, L (a • f) = ι a • L f) ∧
      ∀ f, (S₂.res h₂).symm (L f) = Lf ((S₁.res h₁).symm f) := by
  refine ⟨(S₂.res h₂).toLinearMap.toAddMonoidHom.comp (Lf.comp (S₁.res h₁).symm.toLinearMap.toAddMonoidHom),
    fun a f => ?_, fun f => ?_⟩
  · show S₂.res h₂ (Lf ((S₁.res h₁).symm (a • f))) = ι a • S₂.res h₂ (Lf ((S₁.res h₁).symm f))
    rw [map_smul, hLf, map_smul]
  · show (S₂.res h₂).symm (S₂.res h₂ (Lf ((S₁.res h₁).symm f))) = _
    exact LinearEquiv.symm_apply_apply _ _


set_option maxHeartbeats 4000000 in
private theorem eqFun_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x) :
    ∃ Lf : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).EqFun →+ (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').EqFun,
      (∀ (a : B.fields.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((Lf ψ).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hj
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have ef : f' = f := eq_of_heq hf
  have ep : w'.px = w.px := eq_of_heq hpx
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hι' : ∀ x, (baseOfColW w').embLL (ι x) = (baseOfColW w).embLL x := hι
  refine liftHom_reidx (baseOfColW w).fields ι (baseOfColW w').tauLL ?_ _ _ rfl ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hι
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hι' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' W').trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w W).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w W) (twistRamifiedPrimes_empty_colTuples w' W') _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of ι p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    refine Eq.trans ?_ (hι' _).symm
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    have eC : w'.I.C = w.I.C := w'.C_eq.trans (ef.trans w.C_eq.symm)
    rw [eC] at e1
    exact e1.trans e2.symm


set_option maxHeartbeats 4000000 in
private theorem forms_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').Ok) :
    ∃ L : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms →+ (Formalism.L2.Col.GSD.toCSD _ h₂).Forms,
      (∀ (a : B.fields.K) ψ, L (a • ψ) = ι a • L ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm (L ψ)).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm ψ).1 d).1) := by
  obtain ⟨Lf, hs, hc⟩ := eqFun_lift w w' W W' hpre hf hpx j j' hj ι hι
  obtain ⟨L, hL, hr⟩ := formsLift_of_eqFunLift ι _ _ h₁ h₂ Lf hs
  refine ⟨L, hL, fun ψ d d' hd => ?_⟩
  rw [hr]
  exact hc _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC.LiftExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) ∧ (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  exact GlobalTheory.Mem.R3.DefLatBC.LiftExt.forms_lift w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hf hp ((j : ℕ) + 1) ((j' : ℕ) + 1)
    (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.MKExt
open _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cusp_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f' : cusp (Xo' j') c' (U' j') a' n') :
    ∃ f : cusp (Xo j) c (U j) a n, HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f', HEq.rfl, Iff.rfl⟩

theorem cusp_match' {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f : cusp (Xo j) c (U j) a n) :
    ∃ f' : cusp (Xo' j') c' (U' j') a' n', HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f, HEq.rfl, Iff.rfl⟩

theorem extendByZero_eq_of_heq_families {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : ext0 (a' t) = ext0 (a t) := by
  subst hj; cases h; rfl

section Comparison₂
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem nrm_le_one_iff (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m)
    (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    (∀ la (y : (R.FW i).Pt la), (R.FW i).nrm la y (fw.e i f) ≤ 1) ↔
      ∀ la, ∀ v ∈ valSet (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (algCls (T.Q.Xo ((i : ℕ) + 1)) T.Q.c) la,
        0 ≤ v (f : T.R ((i : ℕ) + 1)) := by
  constructor
  · intro h la v hv
    have h1 := h la ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h la y
    rw [fw.nrm_eq, Core.nrmM_le_one_iff]
    exact h la _ (fw.pt i la y).2

end Comparison₂

end GlobalTheory.Mem.R3.MKExt

namespace GlobalTheory.Mem.R3.MKExt
open _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor


set_option maxHeartbeats 4000000 in
theorem mk_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_
  obtain ⟨hB, -⟩ := hE
  clear * - hB hN hj φ hφ
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M1 := fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'
  have M2 := fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  ext x'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f, hff, hP⟩ := M1 f'
    have hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1 := by
      rw [he']; exact h2
    have hI := hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')
    have hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x' :=
      congrArg Subtype.val he'
    refine ⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL),
      ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩
    have h3 := hN.forms j j' hj f f' hff k k' hk
    apply hinj
    rw [hφ]
    exact (congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3
  · rintro ⟨x, ⟨h1, h2⟩, hrel⟩
    obtain ⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f', hff, hP⟩ := M2 f
    have hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1 := by
      rw [he]; exact h2
    have hI' := hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)
    have hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x :=
      congrArg Subtype.val he
    have hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
      funext k'
      have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
      have h3 := hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk
      have h4 := hrel (Fin.cast hn k') k' hk
      apply hinj
      rw [h4]
      exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
    subst hx'
    exact ⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩

end GlobalTheory.Mem.R3.MKExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supLattice_extendedData_eq_coordinatewiseImage : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  first | exact @GlobalTheory.Mem.R3.MKExt.mk_ext | exact GlobalTheory.Mem.R3.MKExt.mk_ext | (intros; apply GlobalTheory.Mem.R3.MKExt.mk_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem csum_res_symm {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (h : S.Ok)
    (f : (S.toCSD h).Forms) (c : S.Cl) :
    (((S.res h).symm f : S.EqFun) : S.D → S.V) (Quotient.out c) = (f.1 : S.Cl → S.V) c :=
  congrArg (fun u : (S.toCSD h).Forms => (u.1 : S.Cl → S.V) c) ((S.res h).apply_symm_apply f)

theorem csum_round_bc (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (hstar : ∀ x, ι (star x) = star (ι x))
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hH : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (Λ₂ ⟨w.1, hw⟩).H = (Λ₁ w).H)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x)
    (h₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).Ok)
    (h₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hS
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨H₂, l₂, rfl⟩ : ∃ (H₂ : ∀ w : ↥SG₂, Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))) (l₂ : ∀ w, ↥(H₂ w) →* Lˣ),
      Λ₂ = fun w => ⟨H₂ w, l₂ w⟩ := ⟨fun w => (Λ₂ w).H, fun w => (Λ₂ w).lam, rfl⟩
  have hH' : H₂ = fun w => (Λ₁ w).H := funext fun w => hH w w.2
  subst hH'
  have key : ∀ (p : Pol X.K X.Tau n) (q : Pol L X.Tau n), HEq (MvPolynomial.map c₂ q) (MvPolynomial.map c₁ p) →
      q = MvPolynomial.map ι p := by
    intro p q h
    apply MvPolynomial.map_injective c₂ c₂.injective
    rw [eq_of_heq h, MvPolynomial.map_map, show c₂.comp ι = c₁ from RingHom.ext hc]
  unfold CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have a1 := key _ _ (hf (Quotient.out c) (Quotient.out c) HEq.rfl)
  have a2 := key _ _ (hg (Quotient.out c) (Quotient.out c) HEq.rfl)
  have b1 := csum_res_symm _ h₁ f c
  have b2 := csum_res_symm _ h₁ g c
  have b3 := csum_res_symm _ h₂ f' c
  have b4 := csum_res_symm _ h₂ g' c
  have a1' : (f'.1 c).1 = MvPolynomial.map ι (f.1 c).1 :=
    (congrArg Subtype.val b3).symm.trans (a1.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b1))
  have a2' : (g'.1 c).1 = MvPolynomial.map ι (g.1 c).1 :=
    (congrArg Subtype.val b4).symm.trans (a2.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b2))
  have hp := (baseChangePairingV_holds X.E X.K L ι hstar X.Tau n X.emb lam 1 (f.1 c) (g.1 c) (f'.1 c) (g'.1 c) a1' a2').2
  exact congrArg₂ (· * ·) rfl hp

theorem glue_inv_H_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (A₂ ⟨w.1, hw⟩).H = (A₁ w).H) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      ((A₂.glue B₂).inv ⟨w.1, hw⟩).H = ((A₁.glue B₁).inv w).H := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).H = ((A₁.glue B₁) w).H
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1]
  exact hA ⟨w.1, h1⟩ h2


set_option maxHeartbeats 1000000 in
theorem csum_refTuple {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂}
    (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl)
    (hpre : B₂.toPre = B₁.toPre) (hp : HEq w₂.px w₁.px) (j₁ j₂ : ℕ) (hj : j₁ = j₂)
    (ι : B₁.LL →+* B₂.LL) (hι : ∀ x, B₂.embLL (ι x) = B₁.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hj
  have hstar : ∀ x, ι (star x) = star (ι x) := by
    intro x
    apply B₂.embLL.injective
    rw [hι, B₂.starLL_cx, hι, B₁.starLL_cx]
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx : w₂.px = w₁.px := eq_of_heq hp
  refine csum_round_bc (baseOfColW w₁).fields ι hstar (baseOfColW w₂).tauLL ?_ ((baseOfColW w₁).wts.lamV j₁) ?_
    (Formalism.L2.Col.mtTyKK w₁.I.Ch w₁.I.sel (mu0F (X := (baseOfColW w₁).fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).inv
    (Formalism.L2.Col.mtTyKK w₂.I.Ch w₂.I.sel (mu0F (X := (baseOfColW w₂).fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₁).inv
    ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι h₁ h₂ f g f' g' hf hg
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · refine (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans (Eq.trans ?_ (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
    rw [hpx]
    rfl
  · exact glue_inv_H_of_empty (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ fun w hw => rfl


set_option maxHeartbeats 1000000 in
theorem csum_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ L _ hL a b => ?_
  exact csum_refTuple w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hp ((j : ℕ) + 1) ((j' : ℕ) + 1) (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
    a b (L a) (L b) (hL a) (hL b)

end GlobalTheory.Mem.R3.DefLatBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLift_extendedData_carries_classSum : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.csum_ext | exact GlobalTheory.Mem.R3.DefLatBC.csum_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.csum_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongAtOfNearSame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearWd

theorem congE_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : ∀ j l : Fin n, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * ((g⁻¹ * g') (Pi.single j (1 : E)) l - (Pi.single j (1 : E) : Sp E n) l))) :
    CongE P c g' g := by
  intro x hx
  have e1 : g (g⁻¹ (g' x)) = g' x := by
    show (g * g⁻¹) (g' x) = g' x
    rw [mul_inv_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x) = g ((((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x)) := by
    rw [map_smul, map_sub]
    show _ = _ • (g (g⁻¹ (g' x)) - g x)
    rw [e1]
  rw [e]
  refine (hg _).2 ?_
  rw [stdAt, mem_localization_standardLattice] at hx ⊢
  intro l
  have hs := GlobalTheory.TopStep.apply_eq_sum ((g⁻¹ * g').toLinearMap - LinearMap.id) x l
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, Pi.sub_apply] at hs
  rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => ha.add hb) (by simpa using GlobalTheory.TopInv.intAt_nat (P := P) 0) fun j _ => ?_
  rw [mul_left_comm]
  exact (hx j).mul (h j l)

theorem congAt_of_near_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (k k' : GL (Fin N) E)
    (h : GlobalTheory.TwU.NearAt Q n y k) (h' : GlobalTheory.TwU.NearAt Q n y k') : GlobalTheory.TwU.CongAt Q n (GlobalTheory.TwU.ratA F (k⁻¹ * k')) := by
  have e : GlobalTheory.TwU.ratA F (k⁻¹ * k') = (y⁻¹ * GlobalTheory.TwU.ratA F k)⁻¹ * (y⁻¹ * GlobalTheory.TwU.ratA F k') := by
    rw [map_mul, map_inv]; group
  rw [e]
  exact GlobalTheory.CongProd.congAt_mul_prod _ _ _ _ _ _ _ (GlobalTheory.TwU.congAt_inv_pos_depth _ _ _ _ _ _ hn h) h'

theorem val_eq_of_congE {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : (I.idx a).β j)
    (P : SBof I a) (g g' : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j)) (z z' : B.fields.K)
    (hz : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g z)
    (hz' : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j b P) g' z')
    (hgg : CongE P.1 ((I.cst a).D P) g' g) : z = z' := by
  classical
  have hL := hOk.idx_ok a
  obtain ⟨r, hr, hrx, rfl⟩ := hz
  obtain ⟨r', hr', hrx', rfl⟩ := hz'
  have hgC : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp j P.1 ((I.idx a).h j b P) := ⟨r, hr, hrx⟩
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 := hL.int j b P hgC
  let G : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1) := ⟨g, hgI⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hred : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (GlobalTheory.TopStep.redGL _ P.1 G).1.mulVec (redV P.1 x) :=
      fun x hx => GlobalTheory.TopStep.redV_redGL G hx
    have hmem : GlobalTheory.TopStep.redGL _ P.1 G ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨g, hgC, hred⟩
    have hκ : (GlobalTheory.TopStep.redGL _ P.1 G)⁻¹ ∈ ((I.idx a).levG j b ⟨P.1, hP⟩).H := inv_mem hmem
    have hred' : ∀ x ∈ stdAt B.fields.E (B.R.N j) P.1, redV P.1 (g x) = (((GlobalTheory.TopStep.redGL _ P.1 G)⁻¹)⁻¹).1.mulVec (redV P.1 x) := by
      intro x hx
      rw [inv_inv]
      exact hred x hx
    rw [chiInv_at_type I hOk a j b P hP g g r hr hrx _ hκ hred' (congE_refl _ _ _),
      chiInv_at_type I hOk a j b P hP g' g r' hr' hrx' _ hκ hred' hgg]
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : G ∈ ((I.idx a).levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ j b ⟨P.1, hQ⟩]
      exact Subgroup.mem_subgroupOf.2 hgC
    have hg1 : g = ((G⁻¹)⁻¹).1 := by rw [inv_inv]
    rw [chiInv_at_twist I hOk a j hj b P hQ g g r hr hrx G⁻¹ (inv_mem hH) hg1 (congE_refl _ _ _),
      chiInv_at_twist I hOk a j hj b P hQ g' g r' hr' hrx' G⁻¹ (inv_mem hH) hg1 hgg]

end GlobalTheory.Mem.Col2.QChi.NearWd

namespace GlobalTheory.Mem.Col2.QChi

theorem nearPair_val_unique : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a)
    (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))
    (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K),
    GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g' z' → z = z' := by
  intro B X I hOk l Z a v P x g g' z z' h h'
  have hL := hOk.idx_ok a
  have hm := hL.hm
  have key : ∀ j, j = B.R.m - 2 + 1 → ∃ b : (I.idx a).β j, (I.idx a).h j b P = 1 := by
    rintro j rfl
    obtain ⟨b, -⟩ := hL.last_uniq
    exact ⟨b, hL.last_h b P⟩
  obtain ⟨b, hb⟩ := key (B.R.m - 1) (by omega)
  obtain ⟨hz, hn⟩ := h
  obtain ⟨hz', hn'⟩ := h'
  rw [← hb] at hz hz'
  have hD : 1 ≤ (I.cst a).D P := hL.cst_ok.D_pos P
  unfold NearV at hn hn'
  have hc := NearWd.congAt_of_near_same _ _ hD _ _ _ hn hn'
  have hgI : g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 :=
    hL.int _ b P ((GlobalTheory.TwU.exists_midLev_iff _ _ _ _ _ _ _ g).1 ⟨z, hz⟩)
  exact NearWd.val_eq_of_congE I hOk a (B.R.m - 1) (by omega) b P g g' z z' hz hz'
    (NearWd.congE_of_cols P.1 _ g g' hgI (GlobalTheory.LevFrame.cols_of_congAt (sm I l Z) P.1 _ (g⁻¹ * g') (by rw [map_mul, map_inv]; exact hc)))

end GlobalTheory.Mem.Col2.QChi

end
end
