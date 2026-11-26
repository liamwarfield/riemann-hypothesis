module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardHeckeCosetsEqCardSubmodulesSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
open NumberField

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen
variable {R : Type} [CommRing R]

theorem card_torsion_eq {A : Type} [AddCommGroup A] [Module R A] [Finite A] {c π : R} {J : Ideal R}
    (hJ : Ideal.span {c} ⊔ Ideal.span {π} = J) (hc : ∀ x : A, c • x = 0) :
    Nat.card (Submodule.torsionBySet R A (J : Set R)) = Nat.card (A ⧸ J • (⊤ : Submodule R A)) := by
  let f : A →ₗ[R] A := π • LinearMap.id
  have hmem : ∀ a ∈ J, ∃ r s : R, a = r * c + s * π := by
    intro a ha
    rw [← hJ, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨r, s, rfl⟩
  have hπ : π ∈ J := hJ ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self π)
  have h1 : Submodule.torsionBySet R A (J : Set R) = LinearMap.ker f := by
    ext x
    rw [Submodule.mem_torsionBySet_iff, LinearMap.mem_ker]
    constructor
    · intro h; simpa [f] using h ⟨π, hπ⟩
    · rintro h ⟨a, ha⟩
      obtain ⟨r, s, rfl⟩ := hmem a ha
      have h' : π • x = 0 := by simpa [f] using h
      simp only [add_smul, mul_smul, hc, h', smul_zero, add_zero]
  have h2 : J • (⊤ : Submodule R A) = LinearMap.range f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro a ha n _
      obtain ⟨r, s, rfl⟩ := hmem a ha
      refine ⟨s • n, ?_⟩
      change π • (s • n) = _
      rw [add_smul, mul_smul, hc, smul_zero, zero_add, mul_smul, smul_comm]
    · rintro _ ⟨y, rfl⟩
      simpa [f] using (Submodule.smul_mem_smul hπ (Submodule.mem_top : y ∈ (⊤ : Submodule R A)))
  rw [h1, h2]
  have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at e1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [e1, mul_comm] at e2
  exact Nat.eq_of_mul_eq_mul_left hpos e2

end Gen
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
section Sub
variable {R : Type} [CommRing R] {A : Type} [AddCommGroup A] [Module R A] (J : Ideal R)

def toQ (S : Submodule R (Submodule.torsionBySet R A (J : Set R))) :
    Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    show (algebraMap R (R ⧸ J) r) • x ∈ S
    rw [algebraMap_smul]
    exact S.smul_mem r hx

theorem card_sub_eq (m : ℕ) :
    Nat.card {T : Submodule R A // T ≤ Submodule.torsionBySet R A (J : Set R) ∧ Nat.card T = m} =
      Nat.card {S : Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) // Nat.card S = m} := by
  set V := Submodule.torsionBySet R A (J : Set R)
  have cardT : ∀ T : Submodule R A, T ≤ V → Nat.card (toQ J (T.comap V.subtype)) = Nat.card T := fun T hT =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hT y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have cardS : ∀ S : Submodule (R ⧸ J) V, Nat.card ((S.restrictScalars R).map V.subtype) = Nat.card S := fun S =>
    (Nat.card_congr (Submodule.equivMapOfInjective V.subtype V.injective_subtype (S.restrictScalars R)).toEquiv).symm
  refine Nat.card_congr
    { toFun := fun T => ⟨toQ J (T.1.comap V.subtype), (cardT T.1 T.2.1).trans T.2.2⟩
      invFun := fun S => ⟨(S.1.restrictScalars R).map V.subtype, fun _ ⟨x, _, hx⟩ => hx ▸ x.2,
        (cardS S.1).trans S.2⟩
      left_inv := fun T => ?_
      right_inv := fun S => ?_ }
  · apply Subtype.ext
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨⟨y, T.2.1 hy⟩, hy, rfl⟩
  · apply Subtype.ext
    ext x
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := Subtype.ext h
      exact this ▸ hx'
    · intro hx; exact ⟨x, hx, rfl⟩

end Sub
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pSub (D : Datum H) (p : ℕ) : Submodule (𝓞 E) D.La := Ideal.span {(p : 𝓞 E)} • ⊤

theorem mem_pSub {D : Datum H} {p : ℕ} {x : D.La} : x ∈ pSub D p ↔ x ∈ pLat D p := by
  rw [pSub, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, mem_pLat]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

def asSub {D : Datum H} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    Submodule (𝓞 E) D.La where
  toAddSubmonoid := N.toAddSubmonoid
  smul_mem' a x hx := hN a x hx

theorem relIndex_eq_card {D : Datum H} {p : ℕ} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    (pLat D p).relIndex N = Nat.card ((asSub N hN).map (pSub D p).mkQ) := by
  let g : D.La →+ D.La ⧸ pSub D p := (pSub D p).mkQ.toAddMonoidHom
  have hker : g.ker = pLat D p := by
    ext x
    rw [AddMonoidHom.mem_ker, ← mem_pSub]
    exact Submodule.Quotient.mk_eq_zero _
  rw [← hker, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  rfl

def latEquiv (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) :
    LatCount D p J m ≃ {T : Submodule (𝓞 E) (D.La ⧸ pSub D p) //
      T ≤ Submodule.torsionBySet (𝓞 E) (D.La ⧸ pSub D p) (J : Set (𝓞 E)) ∧ Nat.card T = m} where
  toFun N := ⟨(asSub N.1 N.2.2.1).map (pSub D p).mkQ, by
      rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_pSub]
      exact N.2.2.2.1 a ha x hx,
    (relIndex_eq_card N.1 N.2.2.1).symm.trans N.2.2.2.2⟩
  invFun T := ⟨(T.1.comap (pSub D p).mkQ).toAddSubgroup,
    fun x hx => by
      show (pSub D p).mkQ x ∈ T.1
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (mem_pSub.2 hx)]
      exact T.1.zero_mem,
    fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx,
    fun a ha x hx => by
      have h := (Submodule.mem_torsionBySet_iff _ _).1 (T.2.1 hx) ⟨a, ha⟩
      rw [← mem_pSub, ← Submodule.Quotient.mk_eq_zero]
      exact ((pSub D p).mkQ.map_smul a x).trans h,
    by
      refine (relIndex_eq_card _ (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).trans (Eq.trans ?_ T.2.2)
      have e : (asSub (T.1.comap (pSub D p).mkQ).toAddSubgroup
          (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).map (pSub D p).mkQ = T.1 :=
        Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _
      rw [e]⟩
  left_inv N := by
    apply Subtype.ext
    ext x
    show (pSub D p).mkQ x ∈ (asSub N.1 N.2.2.1).map (pSub D p).mkQ ↔ x ∈ N.1
    constructor
    · rintro ⟨y, hy, h⟩
      have h' : y - x ∈ pSub D p := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        exact sub_eq_zero.2 h
      have := N.1.sub_mem hy (N.2.1 (mem_pSub.1 h'))
      simpa using this
    · intro hx; exact ⟨x, hx, rfl⟩
  right_inv T := Subtype.ext (Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _)

end Lat
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

theorem card_latCount : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  intro E _ _ _ H Dw p J hp hJ hpJ k
  haveI := Dw.fin
  haveI := Dw.proj
  letI := Ideal.Quotient.field J
  set R := 𝓞 E
  set L := Dw.La
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have hspan0 : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hJ0 : J ≠ ⊥ := fun h => hp0 (by rw [h] at hpJ; exact (Submodule.mem_bot R).1 hpJ)
  haveI hfinJ : Finite (R ⧸ J) := (Ideal.absNorm_ne_zero_iff J).1 (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h))
  haveI : Finite (R ⧸ Ideal.span {(p : R)}) :=
    (Ideal.absNorm_ne_zero_iff _).1 (fun h => hspan0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hq : Nat.card (R ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

  haveI hA : Finite (L ⧸ pSub Dw p) := by
    haveI : Finite ((R ⧸ Ideal.span {(p : R)}) ⊗[R] L) := Module.finite_of_finite (R ⧸ Ideal.span {(p : R)})
    exact Finite.of_equiv _ (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(p : R)})).toEquiv
  set V := Submodule.torsionBySet R (L ⧸ pSub Dw p) (J : Set R)

  have hc : ∀ x : L ⧸ pSub Dw p, (p : R) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  obtain ⟨π, hπ⟩ := IsDedekindDomain.exists_sup_span_eq
    (show Ideal.span {(p : R)} ≤ J from (Ideal.span_singleton_le_iff_mem J).2 hpJ) hspan0
  have hle : pSub Dw p ≤ J • (⊤ : Submodule R L) :=
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).2 hpJ)
  have hmap : J • (⊤ : Submodule R (L ⧸ pSub Dw p)) = (J • (⊤ : Submodule R L)).map (pSub Dw p).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hV : Nat.card V = Ideal.absNorm J ^ Module.finrank R L := by
    rw [card_torsion_eq hπ hc, hmap,
      Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ hle).toEquiv,
      ← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L J).toEquiv,
      Module.natCard_eq_pow_finrank (K := R ⧸ J), GlobalTheory.SW.Hyper.finrank_fibre R L (R ⧸ J), hq]
  haveI : Finite V := inferInstance
  haveI : Module.Finite (R ⧸ J) V := Module.Finite.of_finite
  have hq2 : 2 ≤ Ideal.absNorm J := by
    rw [← hq]
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ.ne_top
    exact Finite.one_lt_card
  have hinj := Nat.pow_right_injective hq2
  have hdim : Module.finrank (R ⧸ J) V = Module.finrank R L := by
    apply hinj
    show Ideal.absNorm J ^ _ = Ideal.absNorm J ^ _
    rw [← hV, Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
  rw [Nat.card_congr (latEquiv Dw p J _), card_sub_eq]
  have key : ∀ S : Submodule (R ⧸ J) V, Nat.card S = Ideal.absNorm J ^ k ↔ Module.finrank (R ⧸ J) S = k := by
    intro S
    rw [Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
    exact hinj.eq_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), GlobalTheory.GaussCount.subspaceCount (R ⧸ J) V k, hq, hdim]

end GlobalTheory.LatCountGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomialStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  first | exact @GlobalTheory.LatCountGauss.card_latCount | exact GlobalTheory.LatCountGauss.card_latCount | (intros; apply GlobalTheory.LatCountGauss.card_latCount <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardHeckeCosetsEqCardSubmodulesSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeCosetCount

theorem card_eq_latCount : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
      Rc.card = Nat.card (GlobalTheory.HeckeCount.LatCount (T.Q.Dw ((i : ℕ) + 1)) p (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal)
        (Ideal.absNorm P.asIdeal ^ k)) := by
  intro D hHP hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hL hG hF hM hTh hTie i σ hσ hV hFP P p k α Rc hs
  obtain ⟨hso, hp, hpP, -, hk, hα, hdc⟩ := hs
  rw [GlobalTheory.T.splitPlace_hecke_doubleCoset_card_gaussBinom D R hL hF i P k α Rc hso hk hα hdc]
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr := (hTie.laws.unf _ hj T.σ₀ T.good_σ₀).1
  have hrk : Module.finrank (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La = D.R.r := by
    rw [(T.Q.Dw ((i : ℕ) + 1)).rank]; omega
  set J := GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal with hJdef
  have hJm : J.IsMaximal := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    haveI : P.asIdeal.IsMaximal := P.isMaximal
    exact Ideal.map_isMaximal_of_equiv T.Q.H.bar
  have hpJ : ((p : ℕ) : 𝓞 D.host.E) ∈ J := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    have := Ideal.mem_map_of_mem (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hpP
    rwa [map_natCast] at this
  have hN : Ideal.absNorm J = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv P.asIdeal J T.Q.H.bar (by rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal])).toEquiv.symm
  rw [← hN, GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial _ p J hp.pos hJm hpJ k, hrk]

end GlobalTheory.HeckeCosetCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardHeckeCosetsEqCardSubmodulesSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hecke_cosets_eq_card_submodules_split_place : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
      Rc.card = Nat.card (GlobalTheory.HeckeCount.LatCount (T.Q.Dw ((i : ℕ) + 1)) p (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal)
        (Ideal.absNorm P.asIdeal ^ k)) := by
  first | exact @GlobalTheory.HeckeCosetCount.card_eq_latCount | exact GlobalTheory.HeckeCosetCount.card_eq_latCount | (intros; apply GlobalTheory.HeckeCosetCount.card_eq_latCount <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLattice
namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable def hermFormImPullback {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm (h y) (h w)).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_eq_of_im_eq_on_spanning_lattice :
    ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  intro g L _ P hsp Hm h h' hab
  have hB : hermFormImPullback Hm h = hermFormImPullback Hm h' := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    exact hab a b
  have him : ∀ x y, (hermForm Hm (h x) (h y)).im = (hermForm Hm (h' x) (h' y)).im := by
    intro x y
    exact LinearMap.congr_fun₂ hB x y
  intro x y
  have hI : ∀ (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (hermForm Hm (k (Complex.I • x)) (k y)).im = (hermForm Hm (k x) (k y)).re := by
    intro k
    simp [hermForm, map_smul, smul_dotProduct]
  apply Complex.ext
  · rw [← hI h, ← hI h']
    exact him _ _
  · exact him x y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLatticeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family : ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | exact GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

theorem smul_sum_sub_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (cf : Fin n → ℂ) (bv : Fin n → V)
    (s : ℂ) (i : Fin n) (h1 : cf i = 1) (h0 : ∀ j, i < j → cf j = 0) :
    s • ∑ j, cf j • bv j - s • bv i ∈ Submodule.span ℂ (bv '' {j | j < i}) := by
  classical
  have e1 : s • ∑ j, cf j • bv j - s • bv i = ∑ j, (s * (cf j - if j = i then 1 else 0)) • bv j := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp
  rw [e1]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases lt_trichotomy j i with hj | rfl | hj
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · simp [h1]
  · simp [h0 j hj, hj.ne']

theorem exists_lift_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {σ' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di i) ty P) (hP' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di j) ty P')
    {p : ℕ} (hp : p.Prime)
    {y y₁ y₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy₁ : y₁ = F.u j P') (hy₂ : y₂ = F.u j P')
    (C C' : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G))
    (ψ' : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₂)
    (ψp' : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₂ ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hC' : ∀ a ∈ C', a ^ p ^ 2 = 1)
    (hI : Formalism.L2.Pj.IsHkIsog p y y₁ C ψ ψp) (hI' : Formalism.L2.Pj.IsHkIsog p y y₂ C' ψ' ψp') :
    ∃ (gam gam' : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ a b, (F.Di j).EF (gam' a) (gam' b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam' a) = h' (P a)) ∧
      (∀ (w : Fin g → ℂ) (v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h' w) (v ≫ ψ' ≫ pullback.fst _ _)) ∧
      (h = h' → C = C') := by
  subst hy hy₁ hy₂
  obtain ⟨gam, h, h1, h2, -, h4⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam', h', h1', h2', -, h4'⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C' ψ' ψp' hP hP' hp hC' hI'
  refine ⟨gam, gam', h, h', h1, h2, h1', h2', fun w v hvs hd => ?_, fun hh => ?_⟩
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    refine ⟨?_, ?_⟩
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left :=
        fun z => by
          rw [← Category.assoc, hI.2.2.1, h4]
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ' ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ' ≫ pullback.fst _ _ = (F.ex j P' (h' z)).left :=
        fun z => by
          rw [← Category.assoc, hI'.2.2.1, h4']
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h'.toLinearMap w _).1 d1
  · rw [← hI.2.2.2.2.2.1, ← hI'.2.2.2.2.2.1]
    congr 1
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := F.ex_onto i P hP x
    rw [← h4, ← h4', hh]

end GlobalTheory.HeckeInj

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj


set_option maxHeartbeats 1000000 in
theorem eq_of_hkRelFr_frBor : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hU P p i hHP k x C C' z z' w t t' hz hz' ht ht' hB hB'
  obtain ⟨-, -, hall, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨Pm, -, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨k'', x'', t'', hB''⟩ := hall w
  obtain ⟨Pm'', -, per'', hPx'', hv'', -⟩ := hpt k'' x''
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hz
  obtain ⟨ψ', ψp', hI', hL', -⟩ := hz'
  have hpp : p.Prime := hHP.2.2.2.1
  have hwx : w.x = F.u (ik k'') Pm'' := hB''.1.trans hPx''
  obtain ⟨gam, gam', h, h', hiso, hh, hiso', hh', hder, hker⟩ :=
    exists_lift_pair F (ik k) (ik k'') Pm Pm'' per per'' hpp hPx (hB.1.trans hwx) (hB'.1.trans hwx) C.1 C'.1
      ψ ψp ψ' ψp' (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C.2 ha)
      (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C'.2 ha) hI hI'
  choose c'' hc''1 hc''2 hc''3 using hB''.2.1
  let bv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ) := fun τ j =>
    ∑ i, Formalism.L2.Pj.toC (c'' τ j i) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ)
  have hdw : ∀ τ j, IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (bv τ j) (w.u τ j) := fun τ j =>
    (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ ((U.un k'' x'').u τ) _ (hv'' τ) (c'' τ j)
      (w.u τ j)).1 (hPx'' ▸ hc''3 τ j)
  have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm'' per''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
    have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
      apply RingHom.ext
      intro a
      ext <;> simp [epsMul]
    rw [e0]
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  letI : Field (Formalism.L2.Pj.CAt σ) := inferInstanceAs (Field ℂ)
  have col : ∀ (zz : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ)) (tt : Formalism.L2.Pj.Ix Dw → (Formalism.L2.Pj.CAt σ)ˣ)
      (ψ0 : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom zz.x)
      (h0 : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ τ j, Formalism.L2.Pj.IsLieImageH p ψ0 ((U.un k x).u τ j) (zz.u τ j)) →
      (∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (U.un k x).x),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (h0 w) (v ≫ ψ0 ≫ pullback.fst _ _)) →
      (∀ j, j ≠ none → tt j = 1) → Formalism.L2.Pj.FrBor tt w zz →
      ∀ τ m, h0 (Pi.single (e.symm ⟨τ, m⟩) 1) - (p : ℂ) • bv τ m ∈
        Submodule.span ℂ (bv τ '' {j | j < m}) := by
    intro zz tt ψ0 h0 hL0 hder0 ht0 hB0 τ m
    choose cf hcf1 hcf2 hcf3 using hB0.2.1
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL0 τ m
    have d2 := hder0 (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ (w.u τ) _ (hdw τ) (cf τ m)
      (zz.u τ m)).1 (hwx ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ zz.u τ m = wv ≫ ψ0 ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3]
    refine smul_sum_sub_mem_span (fun j => Formalism.L2.Pj.toC (cf τ m j)) (bv τ) _ m ?_ fun j hj => ?_
    · show Formalism.L2.Pj.toC (cf τ m m) = 1
      rw [hcf1 τ m, ht0 _ (by simp)]
      rfl
    · show Formalism.L2.Pj.toC (cf τ m j) = 0
      rw [hcf2 τ m j hj]
      rfl
  obtain ⟨Hm, -, hpos, hHm⟩ := per''.2.2.2.2
  have hform : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm (h' x) (h' y) :=
    GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family Pm per.2.2.2.1 Hm h.toLinearMap h'.toLinearMap fun a b => by
      simp only [LinearEquiv.coe_coe]
      rw [← hh, ← hh, ← hh', ← hh', hHm, hHm, hiso, hiso']
  have hhh := GlobalTheory.T.eq_of_flag_of_hermForm_preserving e Hm hpos h h' hform bv (p : ℂ) hp0
    (col z t ψ h hL (fun w v a b => (hder w v a b).1) ht hB)
    (col z' t' ψ' h' hL' (fun w v a b => (hder w v a b).2) ht' hB')
  exact Subtype.ext (hker hhh)

end GlobalTheory.HeckeInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  first | exact @GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | exact GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | (intros; apply GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeckeTermIdent

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare GlobalTheory.HeckeCount

theorem nonempty_hkKer_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (z : FrPt Xo c Ω) :
    Nonempty (hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  exact ⟨eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)⟩

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem isHeckePrime_of_setting {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {i : Fin D.R.m} {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := by
  obtain ⟨hOff, hp, hpP, hM, -⟩ := hS
  refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  let b : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.L2.Pj.barE D
  have hb : ∀ a : 𝓞 D.host.E, T.Q.H.bar a = b a := fun a => GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations.bar_eq_barE T.Q a
  have hmap : P.asIdeal.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    congr 1; exact RingHom.ext hb
  have hconj : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    apply le_antisymm
    · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
      rintro r ⟨s, hs, e⟩
      have : r = b s := by
        apply RingOfIntegers.coe_injective
        exact e.trans rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hs
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      exact Ideal.subset_span ⟨s, hs, rfl⟩
  have hmax : (P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := Ideal.map_isMaximal_of_equiv b
  have hne : P.asIdeal ≠ P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    intro e; exact hOff.1 (hconj.trans e.symm)
  rw [hmap]
  exact P.isMaximal.coprime_of_ne hmax hne

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem heckeKernelCoset : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2, hx'⟩) z := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hP := GlobalTheory.HeckeTermIdent.isHeckePrime_of_setting hS
  have hE := GlobalTheory.T.exists_heckeKernel_coset_framedPoint D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  choose f hfR hfZ using hE
  have hTot := hHk.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hU : IsUnf (T.U ((i : ℕ) + 1) σ) := hTie.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ σ (hσ ▸ T.toCore.good_σ₀)
  let g : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) → Rc := fun C => ⟨f C, hfR C⟩
  have hinj : Function.Injective g := by
    intro C C' hCC
    have e : f C = f C' := congrArg Subtype.val hCC
    obtain ⟨z, hz⟩ := hTot C
    obtain ⟨z', hz'⟩ := hTot C'
    obtain ⟨hx1, t, ht, hb⟩ := hfZ C z hz
    have key : ∀ a, f C' = a → ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈
        ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
        (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z' := by
      rintro a rfl; exact hfZ C' z' hz'
    obtain ⟨hx2, t', ht', hb'⟩ := key (f C) e.symm
    exact GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange (T.Q.Xo ((i : ℕ) + 1)) T.Q.c σ D.R.r (T.U ((i : ℕ) + 1) σ) hU P.asIdeal p k hP _ _ C C' z z' _ t t'
      hz hz' ht ht' hb hb'
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := Finite.of_injective g hinj
  obtain ⟨eK⟩ := GlobalTheory.HeckeTermIdent.nonempty_hkKer_equiv (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hcard : Nat.card Rc ≤ Nat.card (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := by
    rw [Nat.card_congr eK, ← GlobalTheory.T.card_hecke_cosets_eq_card_submodules_split_place D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS,
      Nat.card_eq_fintype_card, Fintype.card_coe]
  refine ⟨Equiv.ofBijective g (hinj.bijective_of_nat_card_le hcard), fun C z hz => hfZ C z hz⟩

end GlobalTheory.HeckeTermIdent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_complex_point_matches_cosets : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckeTermIdent.heckeKernelCoset | exact GlobalTheory.HeckeTermIdent.heckeKernelCoset | (intros; apply GlobalTheory.HeckeTermIdent.heckeKernelCoset <;> assumption)
end
end
