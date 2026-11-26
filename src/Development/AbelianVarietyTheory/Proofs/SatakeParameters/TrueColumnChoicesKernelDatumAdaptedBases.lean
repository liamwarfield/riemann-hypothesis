module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChains

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNatCastEqOne
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem conj_eq_complexConj (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

theorem norm_natCast_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℂ_[p])‖ = 1 := by
  rw [GlobalTheory.EigenGenerator.norm_natCast_eq]
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk)

theorem exists_unitary_at (p : ℕ) (hp : p.Prime) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ G : Matrix (Fin N) (Fin N) D.host.E, (G.map D.host.conj).transpose * G = 1 ∧
      (∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E))) ∧
      (∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram D.sp.cm.cmUnram
  have hsd : (⟨L, hL.1, hL.2.1⟩ : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat D.host.E N).SelfDual := by
    intro x
    have h3 := hL.2.2 x
    refine h3.trans (forall₂_congr fun y _ => ?_)
    have e : stdH D.host.E N y x = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y := by
      unfold stdH GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl
    rw [e]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  obtain ⟨γ, hγ, h1, h2⟩ := GlobalTheory.GenusSelfDual.inGenus_of_selfDual hsd p hp
  refine ⟨LinearMap.toMatrix' γ.toLinearMap, ?_, fun x hx => ?_, fun a => ?_⟩
  · ext a b
    have h := hγ (Pi.single b 1) (Pi.single a 1)
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm (Pi.single b (1 : D.host.E)) (Pi.single a 1) = if a = b then 1 else 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      rw [Finset.sum_eq_single b]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, Ne.symm hab, hab]
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rw [hr] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, conj_eq_complexConj]
    rw [← h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · obtain ⟨k, hk, hkx⟩ := h1 x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hkx
    choose c hc using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hy
    refine ⟨k, hk, c, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, Nat.cast_smul_eq_nsmul]
    rw [← hyx]
    have : (fun a => (c a : D.host.E)) = y := funext hc
    rw [this]
    rfl
  · have hm : (fun i => LinearMap.toMatrix' γ.toLinearMap i a) ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std D.host.E N).map γ).L := by
      refine Submodule.mem_map.2 ⟨Pi.single a 1, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod a, ?_⟩
      funext i
      simp [LinearMap.toMatrix'_apply]
    obtain ⟨k, hk, hkx⟩ := h2 _ hm
    exact ⟨k, hk, by rwa [Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.Mem.Col2.TC.AdaptedBases

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem basR_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (G : Matrix (Fin N) (Fin N) D.host.E) (hdet : G.det ≠ 0)
    (h1 : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E)))
    (h2 : ∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) :
    GL3Columns.BasR D lam τ L (G.map (tauEmb D lam τ)) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  unfold GL3Columns.BasR
  rw [hρ]
  have hdet' : (G.map ρ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ρ).2 hdet
  refine ⟨hdet', fun x hx a => ?_, fun a => ?_⟩
  · obtain ⟨k, hk, c, hc⟩ := h1 x hx
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    have hv : (fun i => ρ (x i)) = (G.map ρ).mulVec ((k : ℂ_[p])⁻¹ • fun a => ρ (c a : D.host.E)) := by
      funext i
      have e := congrArg (fun v => ρ (v i)) hc
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at e
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hk0, e, RingHom.map_mulVec]
      rfl
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet'), Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, norm_mul, norm_inv, hk1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ (c a)
  · obtain ⟨k, hk, hkL⟩ := h2 a
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    refine ⟨1, fun _ => (k : ℂ_[p])⁻¹, fun _ => (k : D.host.E) • fun i => G i a, fun _ => by rw [norm_inv, hk1, inv_one],
      fun _ => hkL, fun i => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.map_apply]
    rw [inv_mul_cancel_left₀ hk0]

theorem dualM_eq_self {N : ℕ} {G : Matrix (Fin N) (Fin N) D.host.E} (h : (G.map D.host.conj).transpose * G = 1) : dualM G = G :=
  Matrix.inv_eq_right_inv h

theorem basR_smul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} {N : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M : Matrix (Fin N) (Fin N) ℂ_[p]} (hM : GL3Columns.BasR D lam τ L M)
    {s : ℂ_[p]} (hs : ‖s‖ = 1) : GL3Columns.BasR D lam τ L (s • M) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; exact zero_ne_one hs
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, fun x hx a => ?_, fun a => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) h0
  · have e : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hs, inv_one, one_mul]
    exact h1 x hx a
  · obtain ⟨n, r, x, hr, hx, he⟩ := h2 a
    refine ⟨n, fun k => s * r k, x, fun k => by rw [norm_mul, hs, one_mul]; exact hr k, hx, fun i => ?_⟩
    rw [Matrix.smul_apply, he i, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ne_two_ne_q_of_adPl {w : D.what₂.places.Pl} (hw : AdPl D w) :
    D.what₂.places.resChar w ∉ D.host.small ∧ D.what₂.places.resChar w ≠ D.host.q := by
  unfold AdPl Formalism.BasicNotions.Host.cls at hw
  constructor
  · intro h
    simp [Formalism.BasicNotions.primeClass, h] at hw
  · intro h
    rw [h, Formalism.BasicNotions.primeClass_q] at hw
    simp at hw

theorem dgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : DgenUnitAd P O := by
  intro w hw u μ τ
  obtain ⟨h2, hq⟩ := ne_two_ne_q_of_adPl hw
  obtain ⟨M, hM, hemb, hs⟩ := (O u μ).dgen_gen
  obtain ⟨s, hs1, hs2⟩ := hs τ
  rw [← hs1]
  exact GlobalTheory.EigenGenerator.norm_generator_eq_one D _ (P.lam w) h2 hq M hemb τ s hs2

theorem exists_sys (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : ∃ Pm : SysFam D u μ,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) := by
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  choose G hG h1 h2 using fun i (c : (D.chTw u μ).cls i) =>
    exists_unitary_at (D := D) (D.what₂.places.resChar w) hp ((O u μ).lat i c).1 ((O u μ).lat i c).2
  refine ⟨fun i c _ => G i c, fun i _ c τ => ?_, fun _ _ _ _ _ _ => rfl, fun i _ c _ _ _ => (dualM_eq_self (hG i c)).symm⟩
  exact basR_of (P.lam w) τ _ (G i c) (Matrix.det_ne_zero_of_left_inverse (hG i c)) (h1 i c) (h2 i c)

end GlobalTheory.Mem.Col2.TC.AdaptedBases

open IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedThKerEntC
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdOfMemSupport
noncomputable section

namespace GlobalTheory.KerRescale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G _root_.Formalism.L2.Ker Classical

theorem card_eq_sum_colLen (μ : YoungDiagram) : μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have hmap : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (0, c.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
    exact YoungDiagram.mem_iff_lt_rowLen.1 h2
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun c hc => hmap c hc),
    Fin.sum_univ_eq_sum_range (fun c => μ.colLen c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

section Hom

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) {K : Type} [CommMonoid K] (a : Lt → K)

def wt : KM.XZ Lt N0 N1 → Additive K := Sum.elim (fun _ => 0) (fun z => Additive.ofMul (a z.1))

theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.minorXZ N0 N1 s p I) (p • Additive.ofMul (a s)) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (KM.XZ Lt N0 N1) ℤ) (Additive.ofMul (a s)) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold KM.minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => Additive.ofMul (a s))
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Gxz_hom (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.Gxz N0 N1 nu I) (∑ s, (nu s).card • Additive.ofMul (a s)) := by
  unfold KM.Gxz
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun s _ => ?_
  rw [card_eq_sum_colLen, Finset.sum_smul]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun c _ => minorXZ_hom N0 N1 a s _ (I s c)

theorem prod_of_mem_support (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) (μ : KM.XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (KM.Gxz N0 N1 nu I).support) :
    ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun z n => a z.1 ^ n) = ∏ s, a s ^ (nu s).card := by
  have h := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hμ' : μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
    ext x; cases x <;> simp
  rw [hμ', Finsupp.weight_apply, Finsupp.sum_sumElim] at h
  generalize Finsupp.sumFinsuppEquivProdFinsupp μ = p at h ⊢
  have h2 := congrArg Additive.toMul h
  unfold Finsupp.sum at h2
  simp only [Function.comp_apply, wt, Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, toMul_sum,
    toMul_nsmul, toMul_ofMul] at h2
  exact h2

end Hom

theorem applyAt0_rescale {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime] (a : Lt → ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    KM.applyAt0 N0 N1 l (MvPowerSeries.rescale (fun z => a z.1) Th) (KM.Gxz N0 N1 nu I) =
      (∏ s, a s ^ (nu s).card) • KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I) := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [MvPowerSeries.coeff_rescale, prod_of_mem_support N0 N1 a nu I μ hμ, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem rescale_atLin {σ κ : Type} [Finite σ] [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (a : κ → ℂ_[p])
    (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rescale a (atLin c (fun j => MvPowerSeries.X j) F) =
      atLin (fun k j => a j * c k j) (fun j => MvPowerSeries.X j) F := by
  unfold atLin
  have hs : MvPowerSeries.HasSubst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * MvPowerSeries.X j) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hs (MvPowerSeries.HasSubst.smul_X a)]
  congr 1
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.rescale_eq_subst, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← MvPowerSeries.rescaleAlgHom_apply, map_smul, MvPowerSeries.rescaleAlgHom_apply,
    MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X a)]
  show c k j • (a j • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])) = (a j * c k j) • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])
  rw [mul_comm, mul_smul]

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D}
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem tauEmb_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (x : D.host.E) : ∃ y : D.what₂.LL, tauEmb D (P.lam w) τ x = P.iL w y := by
  have e : D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) = embT D τ x := RingHom.congr_fun D.embE_φ₀ _
  refine ⟨D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x), ?_⟩
  rw [P.iL_lam, e]
  rfl

def adUnit (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Cw D w :=
  if AdPl D w then (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ else 1

theorem norm_adUnit (hU : DgenUnitAd P O) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) :
    ‖adUnit P O w u μ τ‖ = 1 := by
  unfold adUnit
  split_ifs with hw
  · rw [norm_inv, hU w hw u μ τ, inv_one]
  · exact norm_one

end GlobalTheory.KerRescale

end
end

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR _root_.Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := _root_.GlobalTheory.KForm.KerJ.mtType_of_hecke (D := D) (C := C) (n := n) Dt ξ hn hord mt h u

end GlobalTheory.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.KerEntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR _root_.Formalism.L2.Host GlobalTheory.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1


open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in
theorem adaptedTh_kerEntC {D : D7} {P : Examples₂.EntPl D} {O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)} {Bs : PlaceMatrixFamily D} {Dx : DivX D} {Tw : TwForms D}
    (hB : BasOk P O Bs) (hA : AdaptedEnt P O Bs Dx) (h : KerEntHyp P O Bs Dx Tw) : AdaptedTh (kerEntC P O Bs h) O := by
  intro w hw u μ hl
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hA w hw u μ hl
  refine ⟨Pm, h1, h2, h3, fun i hi c c' => ?_⟩
  show thAtW P O Bs u μ w i c c' = _
  unfold thAtW
  congr 1
  funext k j
  unfold adCoef
  split_ifs with hk
  · set s := Formalism.MainNotions.TaylorLogMetric.lamC (P.lam w) ((O u μ).dgen k.1) with hs
    have hs0 : s ≠ 0 := by
      intro h0
      have hd := (hB u μ w (i + 1) hi c' k.1).1
      haveI hne : Nonempty (Fin (D.R.N (i + 1))) := ⟨j.2.2⟩
      rw [h4 (i + 1) hi c' k.1, ← hs, h0, _root_.inv_zero, zero_pow (by omega), zero_smul] at hd
      exact hd Matrix.det_zero
    have hdet : ((Pm i c k.1).map (tauEmb D (P.lam w) k.1)).det ≠ 0 := (h1 i hi.le c k.1).1
    have ht : s⁻¹ ^ i ≠ 0 := pow_ne_zero _ (inv_ne_zero hs0)
    have hinv : (s⁻¹ ^ i • (Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ =
        (s⁻¹ ^ i)⁻¹ • ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [h4 (i + 1) hi c' k.1, h4 i hi.le c k.1, ← hs, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : (1 : ℂ_[D.what₂.places.resChar w]) * s * s⁻¹ ^ (i + 1) * (s⁻¹ ^ i)⁻¹ = 1 := by
      rw [inv_pow, inv_pow, inv_inv, pow_succ]
      field_simp
    simp only [show (kerEntC P O Bs h).lam w = P.lam w from rfl]
    generalize ((Pm (i + 1) c' k.1).map (tauEmb D (P.lam w) k.1)) k.2.1 j.2.2 = x
    generalize ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ j.2.1 k.2.2 = y
    linear_combination (x * y) * e
  · rfl

end GlobalTheory.Mem.Col2.KerEntTrue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBases
noncomputable section

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G _root_.Formalism.L2.Ker Classical

theorem colsOf_smul {k : Type} [CommRing k] {N : ℕ} (t : k) (Y : Matrix (Fin N) (Fin N) k) :
    GL3Columns.colsOf (t • Y) = fun a j => t * GL3Columns.colsOf Y a j := by
  funext a j
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem deX_smul {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (t : Lt → k)
    (y : Lt → Fin N → ℕ → k) :
    GL3Columns.DeX N nu (fun s a j => t s * y s a j) = MvPolynomial.C (∏ s, t s ^ (nu s).card) * GL3Columns.DeX N nu y := by
  unfold GL3Columns.DeX
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [GlobalTheory.KerRescale.card_eq_sum_colLen, ← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e : (Matrix.of fun i j : Fin ((nu s).colLen c) => ∑ a : Fin N, MvPolynomial.C (t s * y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a)) =
      (MvPolynomial.C (t s) : MvPolynomial (Lt × ℕ × Fin N) k) • Matrix.of fun i j : Fin ((nu s).colLen c) => ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a) := by
    ext i j
    simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc]
  rw [e, Matrix.det_smul, Fintype.card_fin, map_pow]

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G _root_.Formalism.L2.Ker Classical

variable {D : D7}

theorem canM_scale (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) (t : D.what₂.Tau → Cw D w)
    {F : FrP D w N → Cw D w} (hF : F ∈ LinearMap.range (canM D w N nu)) (y : FrP D w N) :
    F (fun τ => t τ • y τ) = (∏ z, t (tauPl D z) ^ (nu z).card) * F y := by
  obtain ⟨ph, rfl⟩ := hF
  show ph (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (t (tauPl D s) • y (tauPl D s))) = _ * ph (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s)))
  simp only [colsOf_smul]
  have h := deX_smul N nu (fun s => t (tauPl D s)) (fun s => GL3Columns.colsOf (y (tauPl D s)))
  rw [h, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem atBas_smul (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ} (t : D.what₂.Tau → Cw D w)
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w (fun τ => t τ • M τ) Q y = atBas P w M Q (fun τ => t τ • y τ) := by
  simp only [atBas, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul]

def scB (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w) (B : PlaceMatrixFamily D) : PlaceMatrixFamily D :=
  fun u μ w i c τ => a w u μ τ ^ i • B u μ w i c τ

variable (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem srcFun_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (v : polV D u i)
    (y : FrP D w (D.R.N i)) :
    srcFun P (scB a B) u μ w i c v y = (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      srcFun P B u μ w i c v (fun τ => a w u μ τ ^ i • y τ) := by
  simp only [srcFun, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, scB]
  rw [show scB a B u μ w i c = fun τ => a w u μ τ ^ i • B u μ w i c τ from rfl, atBas_smul P w (fun τ => a w u μ τ ^ i)]
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib, mul_assoc]

theorem tgtFun_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) (v : polV D u (i + 1))
    (y : FrP D w (D.R.N (i + 1))) :
    tgtFun P (scB a B) u μ w i c' v y = (∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      tgtFun P B u μ w i c' v (fun τ => a w u μ τ ^ (i + 1) • y τ) := by
  simp only [tgtFun, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, scB]
  rw [show scB a B u μ w (i + 1) c' = fun τ => a w u μ τ ^ (i + 1) • B u μ w (i + 1) c' τ from rfl, atBas_smul P w (fun τ => a w u μ τ ^ (i + 1))]
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib, mul_assoc]

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G _root_.Formalism.L2.Ker Classical

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem prSC_scB (hC : CanOnto P) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m)
    (c : (D.chTw u μ).cls i) (v : ValQ O u μ i) (φ : MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N i)) (Cw D w)) :
    prSC P O (scB a B) u μ w i c v φ = ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) * prSC P O B u μ w i c v φ := by
  have e : srcFun P (scB a B) u μ w i c (secC O u μ i v) = ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) • srcFun P B u μ w i c (secC O u μ i v) := by
    funext y
    rw [srcFun_scB, canM_scale w (D.R.N i) (nuD D u i) (fun τ => a w u μ τ ^ i) (canS_of P B hC u μ w i hi c _) y, Pi.smul_apply,
      smul_eq_mul, mul_assoc]
  show canInv D w (D.R.N i) (nuD D u i) (srcFun P (scB a B) u μ w i c (secC O u μ i v)) φ = _ *
    canInv D w (D.R.N i) (nuD D u i) (srcFun P B u μ w i c (secC O u μ i v)) φ
  rw [e, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem prTC_scB (hC : CanOnto P) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m)
    (c' : (D.chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i)) :
    prTC P O (scB a B) u μ w i c' v' I = ((∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) * prTC P O B u μ w i c' v' I := by
  have e : tgtFun P (scB a B) u μ w i c' (secC O u μ (i + 1) v') = ((∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) • tgtFun P B u μ w i c' (secC O u μ (i + 1) v') := by
    funext y
    rw [tgtFun_scB, canM_scale w (D.R.N (i + 1)) (nuD D u i) (fun τ => a w u μ τ ^ (i + 1)) (canT_of P B hC u μ w i hi c' _) y,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
  show onMin D w (D.R.N (i + 1)) (nuD D u i) (canInv D w (D.R.N (i + 1)) (nuD D u i) (tgtFun P (scB a B) u μ w i c' (secC O u μ (i + 1) v'))) I = _ *
    onMin D w (D.R.N (i + 1)) (nuD D u i) (canInv D w (D.R.N (i + 1)) (nuD D u i) (tgtFun P B u μ w i c' (secC O u μ (i + 1) v'))) I
  rw [e, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]

theorem thAtW_scB (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (i : ℕ) (hi : i < D.R.m) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    thAtW P O (scB a B) u μ w i c c' = MvPowerSeries.rescale (fun z => a w u μ (tauPl D z.1)) (thAtW P O B u μ w i c c') := by
  unfold thAtW
  rw [GlobalTheory.KerRescale.rescale_atLin]
  congr 1
  funext k j
  split_ifs with hk
  · have hs0 : a w u μ k.1 ≠ 0 := norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)
    have h0 := (hB u μ w i hi.le c k.1).1
    have e : (a w u μ k.1 ^ i • B u μ w i c k.1)⁻¹ = (a w u μ k.1 ^ i)⁻¹ • (B u μ w i c k.1)⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    show 1 * lamC (P.lam w) ((O u μ).dgen k.1) * (a w u μ k.1 ^ (i + 1) • B u μ w (i + 1) c' k.1) k.2.1 j.2.2 *
      (a w u μ k.1 ^ i • B u μ w i c k.1)⁻¹ j.2.1 k.2.2 = _
    rw [e, hk]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [pow_succ]
    field_simp
  · exact (mul_zero _).symm

theorem unF_scB (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    unF P O (scB a B) u μ w i c c' = unF P O B u μ w i c c' * ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
      ∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) := by
  unfold unF scB
  simp only [Matrix.det_smul, Fintype.card_fin, mul_zpow, Finset.prod_mul_distrib]
  ring

end GlobalTheory.Pdv.KerScale

namespace GlobalTheory.Pdv.KerScale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G _root_.Formalism.L2.Ker Classical

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem basOk_scB (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) : BasOk P O (scB a B) := fun u μ w i hi c τ =>
  GlobalTheory.Mem.Col2.TC.AdaptedBases.basR_smul (hB u μ w i hi c τ) (by rw [norm_pow, ha, one_pow])

theorem kerEntHyp_scB {Dx : DivX D} {Tw : TwForms D} (ha : ∀ w u μ τ, ‖a w u μ τ‖ = 1) (hB : BasOk P O B) (hC : CanOnto P)
    (hR : ∀ u μ, GL3Columns.RhoAlg (O u μ)) (h : KerEntHyp P O B Dx Tw) : KerEntHyp P O (scB a B) Dx Tw := by
  have hn : ∀ w u μ τ, a w u μ τ ≠ 0 := fun w u μ τ => norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)
  have nS : ∀ u μ w i, ‖(∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card‖ = 1 := fun u μ w i => by
    simp [norm_prod, norm_zpow, norm_pow, ha]
  have nT : ∀ u μ w i, ‖(∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) *
      ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card‖ = 1 := fun u μ w i => by
    simp [norm_prod, norm_zpow, norm_pow, ha]
  refine ⟨fun u μ w hw i hi c' v' I => ?_, fun u μ w hw i hi φ => ?_, fun u μ w hw i hi φ => ?_,
    fun u μ w hw i hi c c' v v' hK I => ?_⟩
  · obtain ⟨b, hb⟩ := h.val u μ w hw i hi c' v' I
    exact ⟨b, by rw [prTC_scB P O B a hC u μ w i hi, norm_mul, nT, one_mul, hb]⟩
  · have e : ∀ c v J, ‖prSC P O (scB a B) u μ w i c v J‖ = ‖prSC P O B u μ w i c v J‖ := fun c v J => by
      rw [prSC_scB P O B a hC u μ w i hi, norm_mul, nS, one_mul]
    simp only [e]
    exact h.latS u μ w hw i hi φ
  · have e : ∀ c' v' I, ‖prTC P O (scB a B) u μ w i c' v' I‖ = ‖prTC P O B u μ w i c' v' I‖ := fun c' v' I => by
      rw [prTC_scB P O B a hC u μ w i hi, norm_mul, nT, one_mul]
    simp only [e]
    exact h.latT u μ w hw i hi φ
  · have k0 := h.kform u μ w hw i hi c c' v v' hK I
    have hF := unF_ne P O B hB u μ (hR u μ) w i hi c c'
    have hU0 : ((∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
        ∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))
        (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))
    have hF' : unF P O (scB a B) u μ w i c c' ≠ 0 := by
      rw [unF_scB]
      exact mul_ne_zero hF hU0
    rw [prTC_scB P O B a hC u μ w i hi, k0, thAtW_scB P O B a ha hB u μ w i hi c c',
      GlobalTheory.KerRescale.applyAt0_rescale _ _ _ (fun s => a w u μ (tauPl D s)), map_smul, smul_eq_mul, prSC_scB P O B a hC u μ w i hi]
    unfold unC
    rw [if_neg hF, if_neg hF', unF_scB]
    have key : (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) *
        (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (hn w u μ τ))))]
    have key2 : (∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) * (∏ z, a w u μ (tauPl D z) ^ (nuD D u i z).card) =
        ∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [← mul_pow, ← pow_succ]
    generalize (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ ((D.chTw u μ).sSharp i τ)) = U1 at *
    generalize (∏ τ, ((a w u μ τ ^ i) ^ D.R.N i) ^ (-(D.chTw u μ).sSharp i τ)) = S1 at *
    generalize (∏ z, (a w u μ (tauPl D z) ^ i) ^ (nuD D u i z).card) = S2 at *
    generalize (∏ z, a w u μ (tauPl D z) ^ (nuD D u i z).card) = G at *
    generalize (∏ z, (a w u μ (tauPl D z) ^ (i + 1)) ^ (nuD D u i z).card) = T2 at *
    generalize (∏ τ, ((a w u μ τ ^ (i + 1)) ^ D.R.N (i + 1)) ^ (-(D.chTw u μ).sDiv i τ)) = U2 at *
    generalize unF P O B u μ w i c c' = F at *
    generalize prSC P O B u μ w i c v _ = p
    linear_combination (-(F * U2 * p * S2 * G)) * key + (-(F * U2 * p)) * key2

end GlobalTheory.Pdv.KerScale

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.kerEntC_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∃ (Bs : PlaceMatrixFamily (I.rec7 l Z)) (h : KerEntHyp Pl O Bs Y (I.tw l l0 Z)), EntOk (kerEntC Pl O Bs h) O := by
  intro B X I hok hp l Z l0 Y O Pl hq hs hu hj
  choose Pm h1 h2 h3 using GlobalTheory.Mem.Col2.TC.AdaptedBases.exists_sys Pl O
  have hU := GlobalTheory.Mem.Col2.TC.AdaptedBases.dgenUnitAd Pl O
  have hB : BasOk Pl O (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ)) :=
    fun u μ w i hi c τ => h1 w u μ i hi c τ
  have hC := GlobalTheory.T.toy_entPl_canOnto _ Pl
  have hR : ∀ u μ, GL3Columns.RhoAlg (O u μ) := fun u μ => KerEntTrue.rhoAlg_std I hok hp l Z hs u μ
  have h0 := GlobalTheory.T.kernelEntryHyp_of_trueColumnChoices I hok hp l Z l0 Y O Pl _ hq hs hB
    (fun u a w _ i _ c τ j k => GlobalTheory.KerRescale.tauEmb_mem Pl w τ (Pm w u a i c τ j k)) hu hj
  have ha := GlobalTheory.KerRescale.norm_adUnit Pl O hU
  have hBs := GlobalTheory.Pdv.KerScale.basOk_scB Pl O _ _ ha hB
  have h := GlobalTheory.Pdv.KerScale.kerEntHyp_scB Pl O _ _ ha hB hC hR h0
  have hA : AdaptedEnt Pl O (GlobalTheory.Pdv.KerScale.scB (GlobalTheory.KerRescale.adUnit Pl O)
      (fun u μ w i c τ => (Pm w u μ i c τ).map (Formalism.MainNotions.TaylorLogMetric.tauEmb _ (Pl.lam w) τ))) Y := fun w hw u μ _ =>
    ⟨Pm w u μ, h1 w u μ, h2 w u μ, h3 w u μ, fun i _ c τ => by
      show GlobalTheory.KerRescale.adUnit Pl O w u μ τ ^ i • _ = _
      unfold GlobalTheory.KerRescale.adUnit
      rw [if_pos hw]⟩
  exact ⟨_, h, ⟨fun u μ w _ => kfTieOf Pl O _ hBs hC h u μ w, fun u μ w _ => kfTieOf_un Pl O _ hBs hC h u μ (hR u μ) w⟩,
    KerEntTrue.adaptedTh_kerEntC hBs hA h⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoices_kernelDatum_adaptedBases : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∃ (Bs : PlaceMatrixFamily (I.rec7 l Z)) (h : KerEntHyp Pl O Bs Y (I.tw l l0 Z)), EntOk (kerEntC Pl O Bs h) O := by
  first | exact @GlobalTheory.Pdv.kerEntC_true | exact GlobalTheory.Pdv.kerEntC_true | (intros; apply GlobalTheory.Pdv.kerEntC_true <;> assumption)
end
