module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl finIdl_incU)

noncomputable section

namespace GlobalTheory.BottomReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem xiH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t : T) (a : D.host.Eˣ) :
    (L.xiH t).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) = 1 := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 := (L.xiH t).2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
  have h2 := HChar.inf_eq_one_of_order hn ho a
  rw [HChar.inf, MonoidHom.comp_apply] at h2
  rw [h2, one_mul] at h1
  exact h1

theorem nuH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (nuH G t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (nuH G t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [nuH, Subgroup.coe_div, Subgroup.coe_mul, MonoidHom.div_apply, MonoidHom.mul_apply,
    xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem prod_pow_eq {N : ℕ} (χ : HeckeU D N) (e : ℤ) (ν : HChar D.host.E) (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x))
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ) =
      ((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D (Units.mk0 a ha))) : ℂˣ) : ℂ) := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := congrArg (fun z : ℂˣ => (z : ℂ)) (hf (GlobalTheory.NormSum.UnramHecke.incU D u))
  simp only [Units.val_zpow_eq_zpow_val] at hB
  have hB' : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e =
      (((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D u))) : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact hB
  have hX : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hA
  rw [hX, inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [mul_comm e, zpow_mul]
  have := congrArg (·⁻¹) hB'
  simp only [inv_inv] at this
  rw [← this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_neg, neg_neg]

theorem alphaH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (alphaH L t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (alphaH L t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [alphaH, Subgroup.coe_mul, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem exps_eq_of {N N₁ : ℕ} (χ : HeckeU D N) (χ₁ : HeckeU D N₁) (e e₁ : ℤ) (ν ν₁ : HChar D.host.E)
    (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x)) (hf₁ : ∀ x, χ₁.f x ^ e₁ = (ν₁⁻¹).1 (finIdl D x)) (τ : D.what₂.Tau) :
    e * χ.n τ = e₁ * χ₁.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e₁ * χ₁.n τ) (fun a ha => by
      have hne : ∀ τ, Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (by simpa using ha) (by exact_mod_cast norm_ne_zero_iff.2 (by simpa using ha))
      simp_rw [zpow_sub₀ (hne _), Finset.prod_div_distrib, prod_pow_eq χ e _ hf a ha, prod_pow_eq χ₁ e₁ _ hf₁ a ha, hν]
      exact div_self (Units.ne_zero _))
  have h := congrFun hc τ
  simpa [sub_eq_zero] using h

theorem pair_real_eq {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁)
    (ν ν₁ : HChar D.host.E) (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, P.W.chV'.f x ^ P.W.ep' = (ν⁻¹).1 (finIdl D x))
    (hf₁ : ∀ x, P₁.W.chV'.f x ^ P₁.W.ep' = (ν₁⁻¹).1 (finIdl D x)) (hd : P.d = P₁.d) :
    (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧ P.n = P₁.n := by
  have h := exps_eq_of P.W.chV' P₁.W.chV' P.W.ep' P₁.W.ep' ν ν₁ hν hf hf₁
  refine ⟨h, funext fun τ => ?_⟩
  have h1 := P.wt τ
  have h2 := P₁.wt τ
  rw [h τ, hd] at h1
  have : (P.n τ : ℤ) = P₁.n τ := by omega
  exact_mod_cast this

theorem bottom_real_eq {μ₀ : T} (hL : L.Is μ₀) {i j : Fin D.R.m} {t t' : T} {𝔪 𝔪₁ : Ideal (𝓞 D.host.E)}
    {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} {P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q} {P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁}
    (h : IsBottom G t i j 𝔪 P P') (h₁ : IsBottom G t' i j 𝔪₁ P₁ P₁') :
    (P.a = P₁.a ∧ P.d = P₁.d ∧ P.n = P₁.n ∧ (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧
        ∀ τ, P.W.ep * P.W.chV.n τ = P₁.W.ep * P₁.W.chV.n τ) ∧
      (P'.a = P₁'.a ∧ P'.d = P₁'.d ∧ P'.n = P₁'.n ∧ (∀ τ, P'.W.ep' * P'.W.chV'.n τ = P₁'.W.ep' * P₁'.W.chV'.n τ) ∧
        ∀ τ, P'.W.ep * P'.W.chV.n τ = P₁'.W.ep * P₁'.W.chV.n τ) := by
  obtain ⟨ha, ha', hd, hd'⟩ := h.rank
  obtain ⟨hb, hb', he, he'⟩ := h₁.rank
  have hν := nuH_finIdl_incU G hL t t' i j
  have hdd : P.d = P₁.d := by rw [hd, he]
  have hdd' : P'.d = P₁'.d := by rw [hd', he', hdd]
  obtain ⟨r1, r2⟩ := pair_real_eq P P₁ _ _ hν h.chars.2 h₁.chars.2 hdd
  obtain ⟨r1', r2'⟩ := pair_real_eq P' P₁' _ _ hν h.chars'.2 h₁.chars'.2 hdd'
  refine ⟨⟨by rw [ha, hb], hdd, r2, r1, ?_⟩, ⟨by rw [ha', hb'], hdd', r2', r1', ?_⟩⟩
  · exact exps_eq_of P.W.chV P₁.W.chV P.W.ep P₁.W.ep _ _ (fun _ => rfl) h.chars.1 h₁.chars.1
  · refine exps_eq_of P'.W.chV P₁'.W.chV P'.W.ep P₁'.W.ep (alphaH L t i j)⁻¹ (alphaH L t' i j)⁻¹ (fun a => ?_)
      (fun x => by rw [inv_inv]; exact h.chars'.1 x) (fun x => by rw [inv_inv]; exact h₁.chars'.1 x)
    show ((alphaH L t i j).1 _)⁻¹ = ((alphaH L t' i j).1 _)⁻¹
    rw [alphaH_finIdl_incU hL t t' i j a]

end GlobalTheory.BottomReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem GlobalTheory.WeilCont.schA_periodic_finite_cosets : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  intro F _ _ κ _ L hLo hLc K hK
  have hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k :=
    fun k => continuous_id.sub continuous_const
  have hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F,
      (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  have hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite := by
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun k => {w | w - k ∈ L})
      (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))
    refine (t.finite_toSet.image QuotientAddGroup.mk).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp (hcov hw)
    exact ⟨k, hk, ((hmk w k).2 hwk).symm⟩
  obtain ⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧
      ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by
    refine ⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1,
      Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩
    · exact ⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)
  refine ⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y,
    fun i => ?_, fun i j => ?_, ?_⟩
  · refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp,
      fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L})
      ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc)
      ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont (y i))) fun w hw => ?_⟩
    · dsimp only
      rw [(hmk x' x).2 hx']
    · dsimp only
      rw [if_neg]
      intro h
      exact hw ((hmk w (y i)).1 (h.trans (hy i).symm))
  · dsimp only
    rw [hy j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (he h').symm), if_neg h]
  · intro Ψ hΨ hper hsupp
    choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)
    refine ⟨f, funext fun z => ?_⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w :=
      ⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,
        funext fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩
    simp only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]
    by_cases hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K
    · obtain ⟨i0, hi0⟩ := (hS _).1 hw
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0.symm, mul_one, hf]
        have hL : w - y i0 ∈ L := (hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)
        rw [← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]
        congr 1
        funext i
        apply Prod.ext
        · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) =
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) +
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0
          rw [map_zero, add_zero]
        · change w i = y i0 i + (w i - y i0 i)
          exact (add_sub_cancel _ _).symm
      · intro j _ hj
        rw [if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0 := by
        by_contra h
        exact hw ⟨w, hsupp _ h, rfl⟩
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hw (h ▸ (hS _).2 ⟨i, rfl⟩)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.schA_periodic_finite_cosets | exact GlobalTheory.WeilCont.schA_periodic_finite_cosets | (intros; apply GlobalTheory.WeilCont.schA_periodic_finite_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenberg
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaSmoothF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def iotaHom {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

theorem contDiff_heis_iota (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) (x : WOF F E nS nT) :
    ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)
  let φ : (IxF F nS nT → ℂ) →+ ℂ :=
    { toFun := fun v => lam (symplOHF σ JS JT ξ₀ x (iotaVF ι v))
      map_zero' := by rw [iotaVF_zero, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun u v => by rw [iotaVF_add, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ x (continuous_iotaVF hι))
  let eqv := (Module.finBasis ℝ (IxF F nS nT → ℂ)).equivFunL
  let L' : (Fin (Module.finrank ℝ (IxF F nS nT → ℂ)) → ℝ) →+ WOF F E nS nT :=
    (iotaHom ι).comp eqv.symm.toLinearEquiv.toAddMonoidHom
  have hL' : Continuous L' := (continuous_iotaVF hι).comp eqv.symm.continuous
  have hsm := hf.smooth _ L' hL' (fun t => real_iotaVF hι _) x
  have hg : ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => f (x + iotaVF ι v) := by
    have h1 := hsm.comp eqv.contDiff
    convert h1 using 1
    funext v
    simp [L', iotaHom]
  have e : (fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x) =
      fun v => Complex.exp (φ.toRealLinearMap hφ v) * f (x + iotaVF ι v) := by
    funext v
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ x _ (real_iotaVF hι v))]
    rfl
  rw [e]
  exact ((φ.toRealLinearMap hφ).contDiff.cexp).mul hg

end GlobalTheory.ThetaSmoothF


open GlobalTheory.ThetaSmoothF in
theorem GlobalTheory.ThetaSmoothF.sm_of_thetaF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι hψ f hf
  have hstd := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  let H := HMF (nS := nS) (nT := nT) JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)
  let B₀ : (IxF F nS nT → ℂ) →ₗ[ℝ] (IxF F nS nT → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
      (fun x x' y => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun x y y' => by simp [add_dotProduct])
      (fun c x y => by simp [star_smul, smul_dotProduct])
  let om : (IxF F nS nT → ℂ) →L[ℝ] (IxF F nS nT → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ H *ᵥ x).im := rfl
  have hH : IsHeis (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ H *ᵥ x).im) (rhoVF σ JS JT ξ₀ B.ψ hψ ι) := by
    refine ⟨fun g => ?_, fun u v g => ?_, fun u g => norm_rhoBF hψ _ g, fun g => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι 0) g = g
      rw [iotaVF_zero]
      exact rhoBF_zero hψ g
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι v) g) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (u + v)) g
      rw [rhoBF_rhoBF, iotaVF_add, GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι u v]
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hψ g).comp (continuous_iotaVF hι)
  refine GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set (IxF F nS nT → ℂ) (BBF σ JS JT ξ₀ B.ψ) om (rhoVF σ JS JT ξ₀ B.ψ hψ ι) (e ▸ hH)
    (WOF F E nS nT) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)), x + iotaVF ι v, fun b => rfl⟩)
    {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g.1} ?_ ?_ f hf
  · intro g hg x
    exact (contDiff_heis_iota σ B hB JS JT ξ₀ hι hg x).differentiable (by simp)
  · intro g hg z
    let L : ℝ →+ WOF F E nS nT :=
      { toFun := fun t => iotaVF ι (t • z)
        map_zero' := by rw [zero_smul, iotaVF_zero]
        map_add' := fun s t => by rw [add_smul, iotaVF_add] }
    have hL : Continuous L := (continuous_iotaVF hι).comp (continuous_id.smul continuous_const)
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => real_iotaVF hι _
    let d : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g.1 w) 0
    have hlev : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u d = d := by
      obtain ⟨U, hU, hUf⟩ := hg.level
      exact ⟨U, hU, fun u hu hu0 =>
        GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 L hL hL0 u hu0 (hUf u hu hu0)⟩
    have hsm : ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L' →
        (∀ t, (L' t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ∞ fun t => d (w + L' t) :=
      fun k L' hL' hL'0 w => GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 k L' hL' hL'0 w
    have hd : IsThetaFunOF σ JS JT ξ₀ B.ψ d :=
      ⟨fun γ w => GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 γ w, hlev,
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd d hlev hsm, hsm⟩
    have hb := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hψ d hd
    refine ⟨toBF d hd.cont hb hd.quasi, hd, fun x => ?_⟩
    exact (GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 x).hasDerivAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenbergStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_smoothVector_realHeisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  first | exact @GlobalTheory.ThetaSmoothF.sm_of_thetaF | exact GlobalTheory.ThetaSmoothF.sm_of_thetaF | (intros; apply GlobalTheory.ThetaSmoothF.sm_of_thetaF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKType
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShift

open GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem smul_apply_of_eq {H W : Type} [AddCommGroup W] [Module ℂ W] (c : ℂ) (hc : c ≠ 0) (f : H → W) (h : H) (w : W)
    (hw : f h = c⁻¹ • w) : (c • f) h = w := by
  rw [Pi.smul_apply, hw, smul_inv_smul₀ hc]

theorem pt_shift (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : κ ∈ GfC (Vc D i)) (hκ' : κ' ∈ GfC (Wc D i)) (a : ℂ)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = a • R.vP i t) :
    ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = a • R.ptP i t P :=
  GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hM.inf (hP.ωP i t) _ _ _ _ _
    (hP.pt_theta i t) κ hκ κ' hκ' a hv

theorem thF_shift_of_eigen (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P)
    (hy : ∀ h, (c • R.extV i t y') h = R.extV i t y (h * κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hP.thF i t).elim fun thP hPF => ?_
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hP.ωP i t)
    (R.ptP i t P) (hP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hM.νV i t).1.1 (R.fdV i t)
      (hM.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hM.HV i t y)
    hy
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thF_shift_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hM hP i t g0 κ κ' hκ hκ' y y' hy v x
  have hc0 := levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ
  exact thF_shift_of_eigen R hM hP i t g0 κ κ' hκ y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ) hc0
    (pt_shift R hM hP i t κ κ' hκ.1 hκ'.1 _ (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hlev hM.inf hP.ωP hP.vP i t g0 κ κ' hκ hκ'))
    (fun h => smul_apply_of_eq _ hc0 _ h _ (hy h)) v x

end GlobalTheory.ThetaShift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKTypeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  first | exact @GlobalTheory.ThetaShift.thF_shift_of_models | exact GlobalTheory.ThetaShift.thF_shift_of_models | (intros; apply GlobalTheory.ThetaShift.thF_shift_of_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShiftSmooth

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  have hs : (flagL (R.datWp i R.triv)).s = 0 := rfl
  have hQ : (flagL (R.datWp i R.triv)).Q = ∅ := rfl
  rw [hs, hQ]
  simp

theorem exists_translate (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) :
    ∃ U ∈ R.Wall i σ, ∀ v x, U v x = X v (x * κ') := by
  refine ⟨postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0) X,
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) g0 X hX _ fun _ => rfl, fun v x => ?_⟩
  have hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (X v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ X hX v).2.2 k hk h
  have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) hT ⟨κ', hκ'⟩ κ' hκ' x
  rw [levChi_flag_eq_one, inv_one, one_mul] at h1
  exact h1

theorem translate_of_lowT (R : RealDat D A Ks) (hθ : IsInfFam R.θ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i)) (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (X X' : MMap (R.MW i σ)) (hX : X ∈ R.Wall i σ) (hX' : X' ∈ R.Wall i σ)
    (h : ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (x : GA D (Wc D i)), X' (fun ρ => v ρ) x = X (fun ρ => v ρ) (x * κ'))
    (v : (R.MW i σ).Vec) (x : GA D (Wc D i)) : X' v x = X v (x * κ') := by
  obtain ⟨U, hU, hUv⟩ := exists_translate R hθ i σ g0 κ' hκ' X hX
  have h0 : X' - U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i σ) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ (X' - U) (Submodule.sub_mem _ hX' hU) fun w => by
      funext z
      exact sub_eq_zero.2 ((h w z).trans (hUv _ z).symm)
  rw [sub_eq_zero.1 h0]
  exact hUv v x

theorem thF_shift_all : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP i t g0 κ κ' hκ hκ' y y' hy
  exact translate_of_lowT R hM.inf i (sg0 D A) g0 κ' hκ' (R.thF i t y) (R.thF i t y') (hP.thF_mem i t y)
    (hP.thF_mem i t y') (GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType R hL hM hP i t g0 κ κ' hκ hκ' y y' hy)

end GlobalTheory.ThetaShiftSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectorsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : (R.MW i (sg0 D A)).Vec) (x : GA D (Wc D i)), R.thF i t y' v x = R.thF i t y v (x * κ') := by
  first | exact @GlobalTheory.ThetaShiftSmooth.thF_shift_all | exact GlobalTheory.ThetaShiftSmooth.thF_shift_all | (intros; apply GlobalTheory.ThetaShiftSmooth.thF_shift_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
namespace GlobalTheory.WeilL2Words
open NumberField IsDedekindDomain

theorem adeleOfMixedSpaceComponent_add (F : Type) [Field F] [NumberField F] (z w : mixedEmbedding.mixedSpace F) :
    arch1 F (z + w) = arch1 F z + arch1 F w :=
  Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z w) (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem mul_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    a * arch1 F z = arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * z) := by
  refine Prod.ext ?_ ?_
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

theorem adeleOfMixedSpaceComponent_zero (F : Type) [Field F] [NumberField F] : arch1 F 0 = 0 :=
  Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl

theorem add_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (a + arch1 F z).1 = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 + z ∧
    (a + arch1 F z).2 = a.2 := by
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = _
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  · exact add_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

def arch1Hom (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F where
  toFun := arch1 F
  map_zero' := adeleOfMixedSpaceComponent_zero F
  map_add' := adeleOfMixedSpaceComponent_add F

theorem adeleOfMixedSpaceComponent_finsetSum (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (z : ι → mixedEmbedding.mixedSpace F) :
    arch1 F (∑ i ∈ s, z i) = ∑ i ∈ s, arch1 F (z i) :=
  map_sum (arch1Hom F) z s

theorem dotProduct_arch (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : κ → AdeleRing (𝓞 F) F)
    (y : κ → mixedEmbedding.mixedSpace F) :
    a ⬝ᵥ arch F y = arch1 F (∑ k, InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 * y k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  exact Finset.sum_congr rfl fun k _ => mul_arch1' F (a k) (y k)

theorem fst_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (arch1 F z).1 = z :=
  RingEquiv.apply_symm_apply _ z

theorem dS_sum_pureA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro F _ _ _ κ _ ψ hψ m g f h
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Complex.ofRealCLM.toLinearMap.comp (ℓ.comp M))
  have hL : ∀ X, L X = ((ℓ (∑ k, X k * h.2 k) : ℝ) : ℂ) := by
    intro X
    simp [L, M]
  have hg : (fun X => (2 * Real.pi * Complex.I) * L X).HasTemperateGrowth :=
    ((2 * Real.pi * Complex.I) • L).hasTemperateGrowth
  refine ⟨fun i => SchwartzMap.smulLeftCLM ℂ (fun X => (2 * Real.pi * Complex.I) * L X) (f i) +
    LineDeriv.lineDerivOp h.1 (f i), ?_⟩
  funext a
  set X : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 with hX
  set Y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2 with hY
  set c : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 with hc
  set A : ℝ := ℓ (∑ k, X k * h.2 k) with hA
  set B : ℝ := ℓ (c * ∑ k, h.1 k * h.2 k) with hB
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) *
        ∑ i, f i (X + t • h.1) * g i Y := by
    funext t
    unfold GlobalTheory.WeilM.schr
    congr 1
    · have e0 : (archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2 =
          arch1 F (∑ k, (t • h.1) k * (t • h.2) k) := by
        rw [archPair, dotProduct_arch]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· * (t • h).2 k) (fst_arch1 F ((t • h).1 k))
      have e1 : a ⬝ᵥ (archPair F (t • h)).2 + ⅟(2 : AdeleRing (𝓞 F) F) * ((archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2)
          = arch1 F (t • (∑ k, X k * h.2 k) + t ^ 2 • (c * ∑ k, h.1 k * h.2 k)) := by
        rw [e0, mul_arch1', archPair, dotProduct_arch, ← adeleOfMixedSpaceComponent_add]
        congr 1
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum,
          Finset.mul_sum, smul_smul, pow_two]
        rfl
      rw [e1, hℓ, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + (archPair F (t • h)).1) k).1) = X + t • h.1 :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).1
      have hy : (fun k => ((a + (archPair F (t • h)).1) k).2) = Y :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).2
      unfold GlobalTheory.WeilM.pureA
      rw [hx, hy]

  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((f i).hasFDerivAt (X + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add X)).mul_const (g i Y))
  have hT := hφ.cexp.fun_mul hS
  unfold dS
  rw [key]
  refine (HasDerivAt.deriv hT).trans ?_
  simp only [Finset.sum_apply, GlobalTheory.WeilM.pureA, SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [hL, ← hA]
  simp only [← hX, ← hY, ← hA, id, zero_smul, add_zero, one_smul, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [show ((0:ℝ) ^ (2 - 1)) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring
end GlobalTheory.WeilL2Words
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFinitePartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  first | exact @GlobalTheory.WeilL2Words.dS_sum_pureA | exact GlobalTheory.WeilL2Words.dS_sum_pureA | (intros; apply GlobalTheory.WeilL2Words.dS_sum_pureA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelTensorValues
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSpan

theorem exists_form {G Γ W X Y : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [AddCommGroup Y]
    [Module ℂ Y] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (h : G)
    (hfin : Finite (Bridge.stab ι J h)) (w : W) (p : X → G) (Φ : X → W →ₗ[ℂ] Y) (v : Y)
    (law : ∀ x γ (k : J), p x = ι γ * h * k → Φ x (ρ γ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • v) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, ∃ N : G → ℕ, (∀ x, Φ x (f (p x)) = (N (p x) : ℂ) • v) ∧
      ∀ γ (k : J), N (ι γ * h * k) ≠ 0 := by
  let S : G → Set Γ := fun x => {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}
  have hS : ∀ x, (S x).Finite := by
    intro x
    rcases (S x).eq_empty_or_nonempty with e | ⟨γ₀, h₀⟩
    · rw [e]; exact Set.finite_empty
    · refine (Set.finite_range fun δ : Bridge.stab ι J h => γ₀ * δ.1).subset fun γ hγ => ⟨⟨γ₀⁻¹ * γ, ?_⟩, by simp⟩
      rw [Bridge.mem_stab]
      have := J.mul_mem h₀ (J.inv_mem hγ)
      convert this using 1
      simp only [map_mul, map_inv]
      group
  let term : G → Γ → W := fun x γ =>
    if hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J then ((χ ⟨_, hm⟩ : ℂˣ) : ℂ) • ρ γ w else 0
  have hsupp : ∀ x, Function.support (term x) ⊆ (hS x).toFinset := by
    intro x γ hγ
    by_contra hn
    have : ¬ h⁻¹ * (ι γ)⁻¹ * x ∈ J := fun hm => hn ((hS x).mem_toFinset.2 hm)
    exact hγ (dif_neg this)
  have hterm : ∀ δ x (k : J) γ, term (ι δ * x * k) (δ * γ) = ((χ k : ℂˣ) : ℂ) • ρ δ (term x γ) := by
    intro δ x k γ
    have e : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
      simp only [map_mul]; group
    by_cases hm : h⁻¹ * (ι γ)⁻¹ * x ∈ J
    · have hm' : h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := e ▸ J.mul_mem hm k.2
      have e' : (⟨_, hm'⟩ : J) = ⟨_, hm⟩ * k := Subtype.ext e
      simp only [term, dif_pos hm, dif_pos hm']
      rw [e', map_mul χ, map_mul ρ, map_smul, smul_smul, Units.val_mul, mul_comm]
      rfl
    · have hm' : ¬ h⁻¹ * (ι (δ * γ))⁻¹ * (ι δ * x * k) ∈ J := fun hh =>
        hm ((J.mul_mem_cancel_right k.2).1 (e ▸ hh))
      simp only [term, dif_neg hm, dif_neg hm', map_zero, smul_zero]
  refine ⟨fun x => ∑ᶠ γ, term x γ, ?_, fun x => (hS x).toFinset.card, fun x => ?_, fun γ k => ?_⟩
  · intro δ x k
    show ∑ᶠ γ, term (ι δ * x * k) γ = ((χ k : ℂˣ) : ℂ) • ρ δ (∑ᶠ γ, term x γ)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
    have hf : (Function.support (term x)).Finite := (hS x).toFinset.finite_toSet.subset (hsupp x)
    have := (((χ k : ℂˣ) : ℂ) • ρ δ).toAddMonoidHom.map_finsum hf
    refine Eq.trans ?_ this.symm
    exact finsum_congr fun γ => hterm δ x k γ
  · show Φ x (∑ᶠ γ, term (p x) γ) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_eq_sum_of_support_subset _ (hsupp _), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hm : h⁻¹ * (ι γ)⁻¹ * p x ∈ J := (hS _).mem_toFinset.1 hγ
    simp only [term, dif_pos hm]
    rw [map_smul, law x γ ⟨_, hm⟩ (by simp only []; group), smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · refine (Finset.card_pos.2 ⟨γ, (hS _).mem_toFinset.2 ?_⟩).ne'
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    convert k.2 using 1
    group

theorem law_abstract {H G' W X : Type} [Group H] [Group G'] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (L : W →ₗ[ℂ] (X → ℂ))
    (x h γ k a : H) (hu : h⁻¹ * γ⁻¹ * x = k * a) (c : ℂ) (hk : ρ k⁻¹ = 1) (hh : ρ h⁻¹ = 1) (hx : ρ x = 1)
    (hLk : ∀ w, om (k, 1) (L w) = c • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (w : W) (g : G') :
    om (x, g) (L (ρ γ w)) = om (γ, 1) (c • om (h, g) (L w)) := by
  have e4 : x = γ * h * k * a := by rw [mul_assoc _ k, ← hu]; group
  have e5 : (x, g) = ((γ, 1) : H × G') * ((h, g) * ((k, 1) * (a, 1))) := by
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e4]; simp only [mul_assoc]
  have e6 : ρ a * ρ γ = 1 := by
    have : a = k⁻¹ * h⁻¹ * γ⁻¹ * x := by rw [e4]; group
    rw [this, map_mul, map_mul, map_mul, hx, hk, hh, one_mul, one_mul, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [e5, map_mul om, Module.End.mul_apply, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa,
    ← Module.End.mul_apply (ρ a), e6, Module.End.one_apply, hLk, map_smul]

theorem map_quot {H G : Type} [Group H] [Group G] (p : H →* G) (x h γ : H) (k : G) (e : p x = p γ * p h * k) :
    p (h⁻¹ * γ⁻¹ * x) = k := by
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

theorem kernel_law {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (c : CoefA S) (hc : c.Is) (J : Subgroup (Bridge.Gf S)) (χ : J →* ℂˣ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ J, ∀ w, om (k, 1) (Λ w) = ((χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {h x : GA D S} (hh : h ∈ GfC S) (hx : x ∈ GfC S) (γ : GQ S) (k : J)
    (e : fin S x = Bridge.ratF S γ * fin S h * k) (w : c.W) (g : GA D T) :
    thetaKO om x g (Λ (c.ρ γ w)) = ((χ k : ℂˣ) : ℂ)⁻¹ * thetaKO om h g (Λ w) := by
  refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S (h⁻¹ * (γ : GA D S)⁻¹ * x)).elim fun k' hk0 => hk0.2.elim fun a ha0 => ?_
  have hk := hk0.1
  have ha := ha0.1
  have e2 : fin S k' = k := ha0.2.2.trans (map_quot (finHom S).rangeRestrict x h γ k e)
  have hk' : fin S k' ∈ J := by rw [e2]; exact k.2
  have e3 : (⟨fin S k', hk'⟩ : J) = k := Subtype.ext e2
  have h1 : ∀ w, om (k', 1) (Λ w) = ((χ k : ℂˣ) : ℂ)⁻¹ • Λ w := fun w =>
    (hΛk k' hk hk' w).trans (congrArg (fun z : J => ((χ z : ℂˣ) : ℂ)⁻¹ • Λ w) e3)
  have h2 := law_abstract om c.ρ Λ x h γ k' a ha0.2.1 _ (hc.1 _ (inv_mem hk)) (hc.1 _ (inv_mem hh)) (hc.1 _ hx)
    h1 (hΛa a ha) w g
  refine (congrFun h2 0).trans ?_
  have h3 := hom.om_aut γ γ.2 1 (one_mem _) _ (hom.om_pres (h, g) _ (hΛ w))
  refine (congrFun ((om ((γ : GA D S), 1)).map_smul _ _) 0).trans ?_
  exact congrArg (fun z : ℂ => ((χ k : ℂˣ) : ℂ)⁻¹ * z) h3

theorem ne_zero_of_coset {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (N : G → ℕ) (h y : G)
    (hN : ∀ γ (k : J), N (ι γ * h * k) ≠ 0) (γ : Γ) (u : J) (e : h = ι γ * y * u) : N y ≠ 0 := by
  have := hN γ⁻¹ u⁻¹
  rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at this

theorem coeff_ne_zero {I : Type} [Fintype I] (r : ℕ) (s N : I → ℕ) (hr : r ≠ 0) (hs : ∀ i, s i ≠ 0) (i₀ : I)
    (hN : N i₀ ≠ 0) : ∑ i, (r : ℂ)⁻¹ * (s i : ℂ)⁻¹ * (N i : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < ∑ i, (r : ℝ)⁻¹ * (s i : ℝ)⁻¹ * (N i : ℝ) :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by have := hs i₀; positivity⟩
  have h' := Complex.ofReal_ne_zero.2 h.ne'
  push_cast at h'
  exact h'

theorem exists_integral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : MeasureTheory.Measure (GA D S)} {𝓕 : Set (GA D S)}
    (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (Cl : Type) [Fintype Cl] (y : Cl → GA D S)
    (hy : Bridge.IsReps (Bridge.ratF S) (levEnv S β L).J (fun k => fin S (y k)))
    (hyf : ∀ k, Finite (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k))))
    (hh : ∀ k, y k ∈ GfC S) {h : GA D S} (hf : h ∈ GfC S) (w : c.W) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ g, ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = a * thetaKO om h g (Λ w) := by
  let Φ : Cl → c.W →ₗ[ℂ] (GA D T → ℂ) := fun k =>
    LinearMap.pi fun g => LinearMap.proj (0 : WO S T) ∘ₗ om (y k, g) ∘ₗ Λ
  have hex := exists_form (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ (fin S h)
    (GlobalTheory.SplitReps.finite_stab_of_reps _ le_rfl hy hyf _) w (fun k => fin S (y k)) Φ
    (fun g => thetaKO om h g (Λ w)) (fun x γ k e => funext fun g =>
      kernel_law hom c hc _ _ Λ hΛ hΛa hΛk hf (hh x) γ k e w g)
  refine hex.elim fun f hf0 => hf0.2.elim fun N hN => ?_
  have hrel : (levEnv S β L).J.relIndex (levEnv S β L).J ≠ 0 := by simp
  have h0 : ∃ k, N (fin S (y k)) ≠ 0 := by
    refine (hy (fin S h)).exists.elim fun k hk => hk.elim fun γ hγ => hγ.elim fun u e => ⟨k, ?_⟩
    exact ne_zero_of_coset (Bridge.ratF S) _ N _ _ hN.2 γ u e
  refine h0.elim fun k₀ hk₀ => ⟨f, hf0.1, _, coeff_ne_zero _
    (fun k => Nat.card (Bridge.stab (Bridge.ratF S) (levEnv S β L).J (fin S (y k)))) (fun k => N (fin S (y k))) hrel
    (fun k => (have := hyf k; Nat.card_pos.ne')) k₀ hk₀, fun g => ?_⟩
  refine (GlobalTheory.LiftUnfold.integral_theta hom hs hp c hc β L hL hf0.1 Λ hΛ hΛa hΛk hν _ Cl y le_rfl hrel hy hh g).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : thetaKO om (y k) g (Λ (f (fin S (y k)))) = (N (fin S (y k)) : ℂ) * thetaKO om h g (Λ w) :=
    congrFun (hN.1 k) g
  rw [h1, ← mul_assoc]

theorem mem_span_of_linear {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (j : I → H)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (T : H →ₗ[ℂ] Y) (y : H) (a : ℂ) (ha : a ≠ 0) (v : Y) (e : T y = a • v) :
    v ∈ Submodule.span ℂ (Set.range fun x => T (j x)) := by
  have h1 : T y ∈ (Submodule.span ℂ (Set.range j)).map T := Submodule.mem_map_of_mem (hj ▸ Submodule.mem_top)
  rw [Submodule.map_span, ← Set.range_comp, e] at h1
  exact (Submodule.smul_mem_iff _ ha).1 h1

theorem span_eq_top_of_model {H Y I : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y] (e : H →ₗ[ℂ] Y)
    (he : Function.Injective e) (j : I → H) (x : I → Y) (hj : ∀ i, e (j i) = x i)
    (hx : Submodule.span ℂ (Set.range x) = LinearMap.range e) : Submodule.span ℂ (Set.range j) = ⊤ := by
  refine Submodule.map_injective_of_injective he ?_
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, ← hx]
  exact congrArg (fun z => Submodule.span ℂ (Set.range z)) (funext hj)

end GlobalTheory.KernelSpan
end
