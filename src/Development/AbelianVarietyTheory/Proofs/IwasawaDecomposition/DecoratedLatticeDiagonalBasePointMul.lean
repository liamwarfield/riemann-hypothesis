module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_row {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (K U : Fin n → P.adicCompletion E)
    {c s : 𝓞 E ⧸ P.asIdeal} (hK : ∀ j, HasRes P (K j) (if j = r then c else 0)) (hU : ∀ j, Valued.v (U j) ≤ 1)
    (hs : HasRes P (U r) s) : HasRes P (∑ j, K j * U j) (c * s) := by
  obtain ⟨s, rfl, hs⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, DilPt.hasRes_mk_iff]
  have hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) =
      ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) *
          (U r - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_
    have := hK j
    by_cases hj : j = r
    · rw [if_pos hj, DilPt.hasRes_mk_iff] at this
      rwa [if_pos hj]
    · rw [if_neg hj] at this
      rw [if_neg hj, sub_zero]
      exact DilPt.hasRes_lt_one this
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoSet_ext {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (hN : d.1.N = d'.1.N) (hf : ∀ P, ∀ x ∈ d'.1.N, d.1.f P x = d'.1.f P x)
    (hbe : ∀ w, ∀ x ∈ d'.1.N, d.1.be w x = d'.1.be w x) : d = d' := by
  have hat : ∀ P, d.1.at P = d'.1.at P := fun P => by unfold Deco.at; rw [hN]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0 :=
    fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hf P _ h
      rw [d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx] at this
      have hp := P.1.isPrime
      exact mul_left_cancel₀ (h0 _ s hs) this
    · rw [d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hbe P _ h
      rw [d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx] at this
      have hp := P.1.isPrime
      funext i
      exact mul_left_cancel₀ (h0 _ s hs) (congrFun this i)
    · rw [d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]

theorem decoOf_dia_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG (E := E) (ST := ST)), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = Formalism.L2.Col.stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow
  classical
  have hg : g ∈ UAd hc n := by
    have := mul_mem h.uni (inv_mem hk.uni)
    rw [mul_inv_cancel_right] at this
    exact this
  have hkc := hk.lat
  rw [hk0] at hkc
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (mem_globLat g w).trans ((hkI _).trans ?_)
    have e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w =
        GlobalTheory.Mem.Col2.pullV (g * k) w := (DilPt.pullbackVector_mul_right g k w).symm
    rw [e]
    refine (mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0 := by
    intro w hw i j
    have h1 : bc (prV (E := E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]
    have h2 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by
      have := congrArg (fun x : GL (Fin n) _ => x.1 i j) h1
      simp only [Units.val_one, Matrix.one_apply] at this
      exact this
    have h3 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by
      rw [map_sub, h2]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl
    rw [map_sub, sub_eq_zero] at h4
    rw [h4]
    split_ifs <;> simp
  have hraw := rlc_decoOf_val hc n ST SG hg
  have hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E := fun x hx =>
    (mem_globLat g x).1 (hN ▸ hx)
  refine ⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩
  · show (decoOf ST SG g).1.N = _
    rw [hraw]
    exact hN
  · show (c P).1 * (decoOf ST SG g).1.f P x = _
    have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have h1 := h.f P x hx _ hl
    rw [DilPt.pullbackVector_mul_right] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1
    have h2 := hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl)
      (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    exact h2.unique h1
  · show (decoOf ST SG g).1.be w x = _
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    funext i
    have h1 := h.be w x hx i
    rw [DilPt.pullbackVector_mul_right] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact (PtExist.hasRes_redA w.1 (hint x hx i)).unique h1

end GlobalTheory.Mem.Col2.DiaPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMulStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG (E := E) (ST := ST)), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  first | exact @GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | exact GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | (intros; apply GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomRayField
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

namespace GlobalTheory.UnramInRay

theorem isModulus_of_top {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {χ : (L ≃ₐ[K] L) →* ℂˣ} (h : IsModulus L χ ⊤) {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) : IsModulus L χ 𝔪 := by
  refine ⟨hm, fun 𝔭 _ => h.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd)), ?_⟩
  rintro α β ⟨ha, hb, -, -, -, hpos⟩
  have hc : ∀ I : Ideal (𝓞 K), IsCoprime I ⊤ := fun I => Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq I)
  exact h.2.2 α β ⟨ha, hb, hc _, hc _, Submodule.mem_top, hpos⟩

theorem nonempty_algHom_rayField : GlobalArtinReciprocity → ∀ (K L R : Type) [Field K] [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field R] [NumberField R]
    [Algebra K R] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRayField K R 𝔪 →
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) → Nonempty (L →ₐ[K] R) := by
  intro H K L R _ _ _ _ _ _ _ _ _ _ 𝔪 hm hR hL
  have := hR.1
  exact rayClassFieldMaximalSt_holds K R L 𝔪 hm hR.2 fun χ =>
    isModulus_of_top (GlobalTheory.UnramModulus.isModulus_top H K L hL χ) hm

end GlobalTheory.UnramInRay

end
end

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem exists_eq_of_isAlgebraic (ι : Qb →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) : ∃ x, ι x = z := by
  let := ι.toAlgebra
  have hi : IsIntegral Qb z := (hz.tower_top Qb).isIntegral
  exact minpoly.mem_range_of_degree_eq_one Qb z
    (IsAlgClosed.degree_eq_one_of_irreducible Qb (minpoly.irreducible hi))

def qbEquiv (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : qb ι M ≃+* M :=
  RingEquiv.ofBijective ((ι.comp (qb ι M).val.toRingHom).codRestrict M fun x => x.2) ⟨RingHom.injective _, fun z => by
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι
      (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z))
    exact ⟨⟨x, mem_qb.2 (hx ▸ z.2)⟩, Subtype.ext hx⟩⟩

theorem numberField_qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] : NumberField (qb ι M) :=
  NumberField.of_ringEquiv M _ (qbEquiv ι M).symm

variable {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb)

@[instance_reducible] def algThrough (L : Fld) (h : j.fieldRange ≤ L) : Algebra E L :=
  (j.toRingHom.codRestrict L fun x => h ⟨x, rfl⟩).toAlgebra

theorem finrank_div (L : Type) [Field L] [NumberField L] [Algebra E L] :
    Module.finrank ℚ L / Module.finrank ℚ E = Module.finrank E L := by
  rw [← Module.finrank_mul_finrank ℚ E L, Nat.mul_div_cancel_left _ Module.finrank_pos]

theorem isRayField_qb (ι : Qb →+* ℂ) {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ}
    (hM : IsRayFieldIn (ι.comp j.toRingHom) 𝔮 M) :
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M), letI := algThrough j _ h; IsRayField E (qb ι M) 𝔮 := by
  obtain ⟨h, hN, hR⟩ := hM
  have hle : j.fieldRange ≤ qb ι M := by
    rintro _ ⟨x, rfl⟩
    exact h x
  refine ⟨numberField_qb ι M, hle, ?_⟩
  let := algOf _ M h
  let := algThrough j _ hle
  have := numberField_qb ι M
  exact hR.of_algEquiv (AlgEquiv.ofRingEquiv (f := qbEquiv ι M) fun x => rfl).symm

theorem le_of_algHom {L N : Fld} (hL : j.fieldRange ≤ L) (hN : j.fieldRange ≤ N)
    (hn : letI := algThrough j L hL; Normal E L)
    (ψ : letI := algThrough j L hL; letI := algThrough j N hN; L →ₐ[E] N) : L ≤ N := by
  let := algThrough j L hL
  let := algThrough j N hN
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E N Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : L →ₐ[E] Qb := (IsScalarTower.toAlgHom E N Qb).comp ψ
  intro x hx
  obtain ⟨y, hy⟩ := (φ.restrictNormal' L).surjective ⟨x, hx⟩
  have h1 : algebraMap L Qb (φ.restrictNormal' L y) = φ y := φ.restrictNormal_commutes L y
  rw [hy] at h1
  have h2 : x = (ψ y : Qb) := h1
  exact h2 ▸ (ψ y).2

theorem isAbelianGalois_iff (L : Fld) (h : j.fieldRange ≤ L) :
    (letI := algThrough j L h; IsAbelianGalois E L) ↔
      ∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x) := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ E Qb := IsScalarTower.of_algebraMap_eq fun q => (j.commutes q).symm
  have : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  have : IsGalois ℚ Qb := IsAlgClosure.isGalois ℚ Qb
  have : IsGalois E Qb := IsGalois.tower_top_of_isGalois ℚ E Qb
  have hmem : ∀ s : Qb ≃ₐ[E] Qb, s.restrictScalars ℚ ∈ GalOf j.fieldRange := fun s => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    exact s.commutes x
  constructor
  · intro hab s hs t ht x hx
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ht
    let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
    let t' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) fun y => ht _ ⟨y, rfl⟩
    have hc : AlgEquiv.restrictNormalHom L (s' * t') = AlgEquiv.restrictNormalHom L (t' * s') := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
    have h1 := AlgEquiv.restrictNormal_commutes (s' * t') L ⟨x, hx⟩
    have h2 := AlgEquiv.restrictNormal_commutes (t' * s') L ⟨x, hx⟩
    have h3 : (s' * t').restrictNormal L = (t' * s').restrictNormal L := hc
    rw [h3, h2] at h1
    exact h1.symm
  · intro H
    have hst : ∀ s : Qb ≃ₐ[E] Qb, ∀ x ∈ L, s x ∈ L := fun s x hx => by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro t ht
      have h1 := H t (IntermediateField.fixingSubgroup_antitone h ht) _ (hmem s) x hx
      rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx] at h1
      exact h1
    let L' : IntermediateField E Qb := (IsScalarTower.toAlgHom E L Qb).fieldRange
    have hn' : Normal E L' := IntermediateField.normal_iff_forall_map_le'.2 fun s => by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨_, hst s x x.2⟩, rfl⟩
    let e : L ≃ₐ[E] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E L Qb)
    have hn : Normal E L := Normal.of_algEquiv e.symm
    have : IsGalois E L := {}
    refine { is_comm := ⟨fun a b => ?_⟩ }
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb a
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb b
    rw [← map_mul, ← map_mul]
    refine AlgEquiv.ext fun x => (algebraMap L Qb).injective ?_
    exact (AlgEquiv.restrictNormal_commutes (s * t) L x).trans
      ((H _ (hmem s) _ (hmem t) x x.2).trans (AlgEquiv.restrictNormal_commutes (t * s) L x).symm)

theorem map_mem_of_normal (L : Fld) (h : j.fieldRange ≤ L) (hn : letI := algThrough j L h; Normal E L) :
    ∀ s ∈ GalOf j.fieldRange, ∀ x ∈ L, s x ∈ L := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro s hs x hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
  have h1 : ((s'.restrictNormal L ⟨x, hx⟩ : L) : Qb) = s x := AlgEquiv.restrictNormal_commutes s' L ⟨x, hx⟩
  exact h1 ▸ (s'.restrictNormal L ⟨x, hx⟩).2


omit j in
theorem hilbert_qb : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M),
      (letI := algThrough j _ h; IsAbelianGalois E (qb ι M)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L] (hL : j.fieldRange ≤ L), (letI := algThrough j L hL; IsAbelianGalois E L) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hR⟩ := isRayField_qb j ι hM
  let := algThrough j _ h
  have := hR.1
  refine ⟨hN, h, hR.1, ?_, fun L _ hL hab hd => ?_⟩
  · rw [finrank_div]
    exact (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E _).1 fun 𝔭 =>
      hR.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))
  · let := algThrough j L hL
    rw [finrank_div] at hd
    obtain ⟨ψ⟩ := GlobalTheory.UnramInRay.nonempty_algHom_rayField H E L (qb ι M) ⊤ top_ne_bot hR
      ((GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E L).2 hd)
    exact le_of_algHom j hL h inferInstance ψ


omit j in
theorem hilbert_qb_aut : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M), j.fieldRange ≤ qb ι M ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s x ∈ qb ι M) ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s (t x) = t (s x)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L], j.fieldRange ≤ L →
        (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hab, hd, hmax⟩ := hilbert_qb H E j ι M hM
  refine ⟨hN, h, map_mem_of_normal j _ h ?_, (isAbelianGalois_iff j _ h).1 hab, hd,
    fun L _ hL hc => hmax L hL ((isAbelianGalois_iff j L hL).2 hc)⟩
  let := algThrough j _ h
  infer_instance

end GlobalTheory.HilbertInClosure

end
end
