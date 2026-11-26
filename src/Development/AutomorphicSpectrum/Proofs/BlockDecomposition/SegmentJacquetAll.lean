module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.SegCoarse

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_jacquet_all : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  first | exact @GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet | exact GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet | (intros; apply GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F
open GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OneExDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev sConj (x : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E) →* GL (Fin n) (x.adicCompletion E) :=
  GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv x)

theorem exists_equiv_of_dualIsConj {π : CuspSub E n} (hd : GlobalTheory.ContraPair.DualIsConj π) (x : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)))
    (τ : SmIrr (GL (Fin n) (x.adicCompletion E))) (hσ : π.IsLocComp (GlobalTheory.ThetaSatake.cw x) σ)
    (ha : IsAdmissible σ.ρ) (hτ : π.IsLocComp x τ) :
    ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v, τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc x) n g) (T v) = T (σ.ρ g v) := by
  obtain ⟨B, -, hB, hfinB, -, -⟩ := hd
  obtain ⟨f, f0, hf⟩ := hτ
  have hs : Continuous (sConj (n := n) x) :=
    Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ x).1)
  let τ' : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)) :=
    { V := τ.V, ρ := MonoidHom.comp τ.ρ (sConj x), smooth := fun v => (τ.smooth v).preimage hs
      irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective x) τ.irred }
  have hσ' := ((cuspSub_iff π).2.1 _ σ).2 hσ
  let β : π.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := B.compl₂ f
  have hβ : β ≠ 0 := fun h => f0 (LinearMap.ext fun v =>
    hB (f v) fun φ => LinearMap.congr_fun (LinearMap.congr_fun h φ) v)
  obtain ⟨F, hF⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred _ σ hσ' β hβ
  let P : σ.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := β ∘ₗ F.1.codRestrict π.V F.2.1
  have hP : ∀ g u v, P (σ.ρ g u) (τ'.ρ g v) = P u v := fun g u v => by
    have e1 : F.1.codRestrict π.V F.2.1 (σ.ρ g u) =
        π.op (.fin (locGL E n _ g)) (F.1.codRestrict π.V F.2.1 u) := Subtype.ext (F.2.2 g u)
    have e2 : f (τ'.ρ g v) = π.op (GlobalTheory.ContraPair.conjOp (.fin (locGL E n _ g))) (f v) := by
      change f (τ.ρ (sConj x g) v) = π.op (.fin (GeneralLinearGroup.map _ (locGL E n _ g))) (f v)
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL, hf, CuspSub.locRep_eq]
    change B (F.1.codRestrict π.V F.2.1 (σ.ρ g u)) (f (τ'.ρ g v)) = B (F.1.codRestrict π.V F.2.1 u) (f v)
    rw [e1, e2, hfinB]
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ n) ha σ.irred
  let e₁ := (GlobalTheory.InvPairing.pairMap σ.ρ τ'.smooth P hP).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ τ'.smooth P hP hF τ'.irred hirr)
  obtain ⟨e₂⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irred
  let e : σ.V ≃ₗ[ℂ] τ.V := (e₂.trans e₁.symm).toLinearEquiv
  have he : ∀ g v, e (σ.ρ g v) = τ.ρ (sConj x (invT n _ g)) (e v) := fun g v => by
    have h := GlobalTheory.ConjPairLoc.equiv_apply (e₂.trans e₁.symm) (invT n _ g) v
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n _ (invT n _ g) = g := Units.ext (Matrix.transpose_transpose _)
    rw [MonoidHom.comp_apply, h1] at h
    exact h
  refine ⟨e, fun g v => ?_⟩
  rw [he]
  congr 2
  exact Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem eq_cw_of_conjPl {w u : HeightOneSpectrum (𝓞 E)} (h : ConjPl w u) : u = GlobalTheory.ThetaSatake.cw w := by
  obtain ⟨h1, h2⟩ := h
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with e | e
  · subst e
    rcases h2 with h2 | h2
    · exact absurd rfl h2
    · exact (GlobalTheory.BCT.LocMem.conjSrc_eq_of_not_split _ h2).symm
  · exact eq_conjSrc e

end GlobalTheory.CompanionTheory.OneExDatum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDual
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegLDual

theorem lSegDual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ
  obtain ⟨hd, hco⟩ := id hπ
  have hsm : IsSmooth π := hco.isSubquotient.isSmooth (isSmooth_prodIrr _ hd)
  obtain ⟨hirr, f, hf, -⟩ := hco
  have hci : (contra π).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hirr) hirr
  obtain ⟨hd', ⟨e⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  have hinj : Function.Injective (GlobalTheory.ContraRefl.contraMap f) := fun a b h => Subtype.ext (LinearMap.ext fun v => by
    obtain ⟨w, rfl⟩ := hf v
    exact LinearMap.congr_fun (congrArg Subtype.val h) w)
  exact GlobalTheory.T.irreducible_sub_segment_product hA hZ (segDual Δ) hd' (contra π) (isSmooth_smoothRep _) hci
    (e.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f))
    (e.toLinearEquiv.injective.comp hinj)

end GlobalTheory.CompanionTheory.SegLDual

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSegmentDualStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_segment_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegDual k := by
  first | exact @GlobalTheory.CompanionTheory.SegLDual.lSegDual | exact GlobalTheory.CompanionTheory.SegLDual.lSegDual | (intros; apply GlobalTheory.CompanionTheory.SegLDual.lSegDual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.CgMod

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

def restr (S : AddSubgroup M) (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) : S ≃ₜ+ S where
  toFun s := ⟨U s.1, hU _ s.2⟩
  invFun s := ⟨U.symm s.1, hU' _ s.2⟩
  left_inv s := Subtype.ext (U.left_inv s.1)
  right_inv s := Subtype.ext (U.right_inv s.1)
  map_add' x y := Subtype.ext (map_add U x.1 y.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

def dbl [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M) (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0)
    (h3 : ∀ x, P x + L (P (L.symm x)) = x) : (S × S) ≃ₜ+ M where
  toFun p := p.1.1 + L p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨P (L.symm x), hPm _⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + L p.2.1) = p.1.1
      rw [map_add (f := _), hPs _ p.1.2, h1 _ p.2.2, add_zero]
    · change P (L.symm (p.1.1 + L p.2.1)) = p.2.1
      have hl : L.symm (L p.2.1) = p.2.1 := L.left_inv _
      rw [map_add (f := _), map_add (f := _), h2 _ p.1.2, zero_add, hl, hPs _ p.2.2]
  right_inv x := h3 x
  map_add' p q := by
    change (p.1.1 + q.1.1) + L (p.2.1 + q.2.1) = (p.1.1 + L p.2.1) + (q.1.1 + L q.2.1)
    rw [map_add (f := _)]; abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := (hPc.subtype_mk _).prodMk ((hPc.comp L.symm.continuous).subtype_mk _)

theorem char_sq [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M)
    (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0) (h3 : ∀ x, P x + L (P (L.symm x)) = x)
    (U : M ≃ₜ+ M) (hUL : ∀ x, U (L x) = L (U x)) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) :
    addEquivAddHaarChar (restr S U hU hU') ^ 2 = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  set Ψ := dbl S P hPc hPm hPs L h1 h2 h3 with hΨ
  set T := restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T T)).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T T (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + L (U p.2.1) = U (p.1.1 + L p.2.1)
    rw [map_add (f := _), hUL]
  rw [sq, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ (GlobalTheory.ModuLR.prodCE T T), e]

end Abstract

theorem exists_anti {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, hc, -, hs⟩ := h
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hv : v.IsComplex := hc.isComplex v
  have hsq : ∀ x, σ (σ x) = x := fun x => v.embedding.injective (by rw [hs, hs]; simp)
  have hx : ∃ x, σ x ≠ x := by
    by_contra hn
    push_neg at hn
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hv
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hs v.embedding x
    rw [hn] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hx
  exact ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, hsq]; abel⟩

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol

variable {D : D7} {n : ℕ}

theorem cA_incA (D : D7) (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [cA, sigR, incA, inclR]

theorem hermPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ hermA D n) :
    hermPart D n (c • s) = 0 := by
  have h : adj s = s := hs
  rw [hermPart, adj_smul, h, hc, neg_smul, add_neg_cancel, smul_zero]

theorem hermPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    hermPart D n x + d • hermPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [hermPart, hermPart, adj_smul, he, neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  exact (add_add_sub_cancel _ _ _).trans (half_smul_add x)


set_option synthInstance.maxHeartbeats 400000 in
def mulCE (d e : AE D) (hde : d * e = 1) : Mx D n n ≃ₜ+ Mx D n n where
  toFun x := d • x
  invFun x := e • x
  left_inv x := by
    change e • d • x = x
    rw [smul_smul, mul_comm, hde, one_smul]
  right_inv x := by
    change d • e • x = x
    rw [smul_smul, hde, one_smul]
  map_add' := smul_add d
  continuous_toFun := continuous_const_smul d
  continuous_invFun := continuous_const_smul e

def hermPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (hermPart D n) hermPart_add

set_option maxHeartbeats 400000 in
theorem val_det_ad_inv (a : GL (Fin n) (AE D)) :
    ((Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) : AE D) = cA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  change (adj a.1 : Mx D n n).det = cA D a.1.det
  rw [adj, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem absA_det_ad_inv (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  have h : (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := Units.ext (val_det_ad_inv a)
  rw [h]
  exact GlobalTheory.DiagThetaRule.absA_conj D _

theorem exists_anti_units (D : D7) : ∃ d e : AE D, d * e = 1 ∧ cA D d = -d ∧ cA D e = -e := by
  obtain ⟨δ, hδ, hσ⟩ := exists_anti _ (isCMExt_host D)
  refine ⟨incA D δ, incA D δ⁻¹, ?_, ?_, ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  · rw [cA_incA, hσ, map_neg]
  · rw [cA_incA, map_inv₀, hσ, inv_neg, map_neg]

theorem lr_herm (a : GL (Fin n) (AE D)) : ∀ s ∈ hermA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ hermA D n :=
  fun s hs => (cg a ⟨s, hs⟩).2

theorem lr_herm_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ hermA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ hermA D n :=
  fun s hs => (cg a⁻¹ ⟨s, hs⟩).2

theorem lr_smul (a : GL (Fin n) (AE D)) (d e : AE D) (hde : d * e = 1) (x : Mx D n n) :
    GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ (mulCE d e hde x) = mulCE d e hde (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ x) := by
  change a.1 * (d • x) * ((ad a)⁻¹ : GL (Fin n) (AE D)).1 = d • (a.1 * x * ((ad a)⁻¹ : GL (Fin n) (AE D)).1)
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem integral_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  intro D n lam hlam a f
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (isClosed_hermA (D := D) (r := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h : ∫ c, f (cg a c) ∂lam = _ := integral_comp_char lam (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) f
  rw [h, hT, npow_neg_nat (absA_pos _) n]

end GlobalTheory.CompanionTheory.CgMod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_conjugation : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.CgMod.integral_cg | exact GlobalTheory.CompanionTheory.CgMod.integral_cg | (intros; apply GlobalTheory.CompanionTheory.CgMod.integral_cg <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}
theorem integral_mul_right (m : ℕ) (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    (f : Mx D m n → ℂ) :
    ∫ y, f (HMul.hMul y a.1 : Mx D m n) ∂μ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(m : ℂ)) * ∫ y, f y ∂μ := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := i1
  haveI : LocallyCompactSpace (Mx D m n) := i2
  haveI : SecondCountableTopology (Mx D m n) := i3
  haveI : T2Space (Mx D m n) := i4
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin m) (AE D)) a
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ m := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) m n
      (1 : GL (Fin m) (AE D)) a
    simpa using this
  have hA : 0 < absA D (Matrix.GeneralLinearGroup.det a) := absA_pos _
  have e : ∀ y : Mx D m n, (HMul.hMul y a.1 : Mx D m n) = φ y := fun y => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  have key : ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ :=
    integral_comp_char μ φ f
  rw [hc, npow_neg_nat hA] at key
  simp only [e]
  exact key

theorem integral_shift {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (g : A) :
    ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ :=
  integral_sub_right_eq_self f g

theorem integral_shift_herm (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure) (f : hermA D n → ℂ) (g : hermA D n) :
    ∫ x, f (x - g) ∂lam = ∫ x, f x ∂lam := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  exact integral_shift lam f g

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp [halfTr, mul_add]

theorem halfTr_neg (x : AE D) : halfTr (-x) = -halfTr x := by
  simp [halfTr]

theorem inner_mul_right (V : HSp D) {r : ℕ} (x : Mx D V.rank r) (s : Mx D r r) :
    StdUnn.inner V (HMul.hMul x s : Mx D V.rank r) (HMul.hMul x s : Mx D V.rank r) =
      adj s * StdUnn.inner V x x * s := by
  unfold StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

theorem trace_cg (a : GL (Fin n) (AE D)) (c Q : Mx D n n) :
    Matrix.trace (a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1)) = Matrix.trace (c * Q) := by
  have h1 : a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1) = a.1 * (c * Q * (a⁻¹).1) := by
    calc _ = a.1 * c * (adj a.1 * adj (a⁻¹).1) * Q * (a⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [adj_mul_adj_inv]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem trace_beta (a : GL (Fin n) (AE D)) (B c : Mx D n n) :
    Matrix.trace (B * (a.1 * c * adj a.1)) = Matrix.trace (adj a.1 * B * a.1 * c) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem weil_pt {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) {b1 : Mx D n n}
    (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (y : Mx D V.rank n) :
    (ω (m * u) φ).1 y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (ψ (halfTr (Matrix.trace (b1 * StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)))) *
        φ.1 (HMul.hMul y a.1 : Mx D V.rank n)) := by
  rw [map_mul, Module.End.mul_apply, hω.levi m a hm, hω.unip u b1 hu]

theorem jt_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : hermA D n} (hu : mat u = blk4 1 b1.1 0 1) (φ : schwartzA θ V.rank n) (c : hermA D n) :
    Jt ψ V μ (ω (m * u) φ).1 (cg a c) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ.1 (c + b1)) := by
  set F : Mx D V.rank n → ℂ := fun y => φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V y y) : Mx D n n))) with hF
  have hpt : ∀ y : Mx D V.rank n, (ω (m * u) φ).1 y *
      ψ (halfTr (Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n))) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2)) *
        F (HMul.hMul y a.1 : Mx D V.rank n) := by
    intro y
    have hy : y = (HMul.hMul (HMul.hMul y a.1 : Mx D V.rank n) (a⁻¹).1 : Mx D V.rank n) := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    set Y : Mx D V.rank n := HMul.hMul y a.1 with hY
    have e1 : Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) := by
      rw [hy, inner_mul_right]
      exact trace_cg a c.1 _
    rw [weil_pt hω a hm hu, e1]
    simp only [hF]
    have e2 : Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V Y Y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) + Matrix.trace (b1.1 * StdUnn.inner V Y Y) := by
      rw [← Matrix.trace_add, ← Matrix.add_mul]
      rfl
    rw [e2, halfTr_add, AddChar.map_add_eq_mul]
    ring
  unfold Jt
  simp only [hpt]
  rw [integral_const_mul, integral_mul_right V.rank μ hμ a F]

end GlobalTheory.CompanionTheory.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.AdmDiscFin

section Dual

variable {K : Type} [Group K]

def shiftL (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) (k : K) : Y →ₗ[ℂ] Y where
  toFun f := ⟨fun x => f.1 (k * x), hY f.1 f.2 k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Representation ℂ K (Module.Dual ℂ Y) where
  toFun k := (shiftL Y hY k).dualMap
  map_one' := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY 1 f) = ξ f
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL])
  map_mul' k l := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY (k * l) f) = ξ (shiftL Y hY l (shiftL Y hY k f))
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL, mul_assoc])

theorem le_coeffSpan_dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Y ≤ GlobalTheory.Published.AutFin.coeffSpan (dualRep Y hY) := by
  intro f hf
  let ev : Module.Dual ℂ Y := (LinearMap.proj (1 : K)).comp Y.subtype
  refine Submodule.subset_span ⟨Module.Dual.eval ℂ Y ⟨f, hf⟩, ev, funext fun k => ?_⟩
  change f k = f (k * 1)
  rw [mul_one]

theorem isContRep_dualRep [TopologicalSpace K] [ContinuousMul K] (Y : Submodule ℂ (K → ℂ))
    (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) [FiniteDimensional ℂ Y] (hc : ∀ f ∈ Y, Continuous f) :
    GlobalTheory.Published.AutFin.IsContRep (dualRep Y hY) := by
  intro ℓ ξ
  let ev : K → Module.Dual ℂ Y := fun x => (LinearMap.proj x).comp Y.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ x, v.1 x = 0 := fun x => hv _ (Submodule.subset_span ⟨x, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext h2)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ Y).surjective ℓ
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ (shiftL Y hY k f) := by
    intro ξ hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact (hc f.1 f.2).comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key ξ (hspan ▸ Submodule.mem_top)

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem continuous_slice (φ : Sm E M) (g : GA E M) :
    Continuous fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E M => (Unitary.toUnits k : GL (Fin M) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin M) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E M) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E M =>
      ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin M) (Fin M) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E M =>
      toL ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

theorem admissible_discrete_spaces : PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDisc := by
  intro E _ _ _ M K' W' hK' hW' V hV
  haveI := hW'
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose c hc using hsc
  let Y : Submodule ℂ (Kinf E M → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E M, φ ∈ V ∧ TypeB K' W' φ ∧ ∃ g : GA E M, f = fun k => φ.1 (g * infGL E M (Unitary.toUnits k))}
  have hYW : Y ≤ W' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, -, hφ, g, rfl⟩
    exact hφ.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφV, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφV, hφ, g * infGL E M (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, -, g, rfl⟩ := hf
      exact continuous_slice φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E M K' hK' (Module.Dual ℂ Y) (dualRep Y hYl)
    (isContRep_dualRep Y hYl hYc) c
  have hle : {φ | φ ∈ V ∧ TypeB K' W' φ} ⊆ GlobalTheory.Published.AutFinGL.forms K' (dualRep Y hYl) c := by
    rintro φ ⟨hφV, hφ⟩
    refine ⟨hV.aut φ hφV, fun k hk => Subtype.ext (funext fun g => hφ.1 k hk g), fun g => ?_,
      fun τ u => hc τ u φ hφV⟩
    exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφV, hφ, g, rfl⟩)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

end GlobalTheory.CompanionTheory.AdmDiscFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzLevi

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)
open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_add' blockMatrix_one mat_mul')
open GlobalTheory.CompanionTheory.IwaAd (levi_mem_P adj_mul_adj_inv adj_inv_mul_adj)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adj_zero' {k l : ℕ} : adj (0 : Mx D k l) = 0 := by
  have h := adj_add (0 : Mx D k l) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  simp only [blkA, blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
    Matrix.toBlocks_fromBlocks₁₁]

theorem blockMatrix_zero' {R : Type} [CommRing R] (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem emb_comm (M : Maps D hn) (ζ : hermA D ρ) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    M.w * M.nzx ζ 0 * M.emb g₀ = M.emb g₀ * (M.w * M.nzx ζ 0) := by
  have hE := M.emb_mat g₀ _ _ _ _ hg
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  simp only [mat_mul']
  rw [hE, M.w_mat, M.nzx_mat, adj_zero']
  simp only [submatrix_fromBlocks_mul]
  simp only [blockMatrix_zero' hn, blockMatrix_add', blockMatrix_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem mat_inv_levi (g₀ : G D p) (a : GL (Fin p) (AE D)) (hg : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g₀⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1)) = (1 : Mx D (p + p) (p + p)) := by
    rw [hg, submatrix_fromBlocks_mul]
    have e1 : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : HMul.hMul (adj (a⁻¹).1) (adj a.1) = (1 : Mx D p p) := adj_inv_mul_adj a
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
    exact block_matrix_one
  calc mat g₀⁻¹ = HMul.hMul (mat g₀⁻¹) (HMul.hMul (mat g₀) (blk4 (a⁻¹).1 0 0 (adj a.1))) := by
        rw [h1]; exact (Matrix.mul_one _).symm
    _ = HMul.hMul (mat (g₀⁻¹ * g₀)) (blk4 (a⁻¹).1 0 0 (adj a.1)) := by
        rw [mat_mul']; exact (Matrix.mul_assoc _ _ _).symm
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
        rw [inv_mul_cancel]; exact Matrix.one_mul _

theorem exists_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) :
    ∃ b : GL (Fin n) (AE D), b.1 = bl hn 1 0 0 a.1 := by
  have e : a.1 * (a⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e' : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨bl hn 1 0 0 a.1, bl hn 1 0 0 (a⁻¹).1, ?_, ?_⟩, rfl⟩
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e]
    exact blockMatrix_one hn
  · rw [blockMatrix_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, e']
    exact blockMatrix_one hn

theorem det_lv (hn : ρ + p = n) (a : GL (Fin p) (AE D)) (b : GL (Fin n) (AE D)) (hb : b.1 = bl hn 1 0 0 a.1) :
    Matrix.GeneralLinearGroup.det b = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hb]
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem wz_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ b₀ χ z f hf g₀ a hg x
  have hE := M.emb_mat g₀ _ _ _ _ hg
  have hE' := M.emb_mat g₀⁻¹ _ _ _ _ (mat_inv_levi g₀ a hg)
  rw [blockMatrix_zero' hn] at hE hE'
  have hP : M.emb g₀ ∈ P D n :=
    levi_mem_P hE hE' (by rw [← map_mul, inv_mul_cancel, map_one])
  obtain ⟨b, hb⟩ := exists_lv hn a
  have hA : blkA (mat (M.emb g₀)) = b.1 := by
    rw [hE, blkA_blk4, hb]
  have e : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.emb g₀ * x)) =
      (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        f (M.w * M.nzx ζ 0 * x) := by
    intro ζ
    rw [← mul_assoc, emb_comm M ζ g₀ a hg, mul_assoc, hf _ hP b hA, det_lv hn a b hb]
  simp only [Wz]
  simp only [e]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul]

end GlobalTheory.CompanionTheory.WzLevi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_levi_equivariance : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  first | exact @GlobalTheory.CompanionTheory.WzLevi.wz_emb | exact GlobalTheory.CompanionTheory.WzLevi.wz_emb | (intros; apply GlobalTheory.CompanionTheory.WzLevi.wz_emb <;> assumption)
end
end
