module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.FrameEq

theorem map_inj {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (hf : Function.Injective f)
    {M M' : Matrix m n R} (h : M.map f = M'.map f) : M = M' := by
  ext i j
  exact hf (congrFun (congrFun h i) j)

private theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem map_smul_rh {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobW_galW {l : ℕ} [Fact l.Prime] (g : GQ l) (x : WCb l) :
    frobW l (galW l g x) = galW l g (frobW l x) := by
  ext n
  simp [frobW, galW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def, map_pow]

theorem cocycle_frob {R : Type} [CommRing R] {d N : ℕ} (fr ga : R →+* R) (hc : ∀ x, fr (ga x) = ga (fr x))
    (e : R) (T A ε Z : Matrix (Fin d) (Fin d) R) (hT : IsUnit T) (hφ : e ^ N • T.map fr = T * A)
    (hgal : Z * T.map ga = T * ε) (hZ : Z.map fr = Z) :
    e ^ N • (ε * A.map ga) = ga e ^ N • (A * ε.map fr) := by
  have h1 : ga e ^ N • T.map (fun x => ga (fr x)) = T.map ga * A.map ga := by
    have := congrArg (fun M => M.map ga) hφ
    simp only [map_smul_rh, Matrix.map_mul, Matrix.map_map, map_pow] at this
    exact this
  have h2 : Z * T.map (fun x => ga (fr x)) = T.map fr * ε.map fr := by
    have := congrArg (fun M => M.map fr) hgal
    simp only [Matrix.map_mul, Matrix.map_map, hZ] at this
    have e2 : T.map (fun x => ga (fr x)) = T.map (⇑fr ∘ ⇑ga) := by
      ext i j; simp [hc]
    rw [e2]; exact this
  apply hT.mul_left_cancel
  calc T * (e ^ N • (ε * A.map ga)) = e ^ N • (T * ε * A.map ga) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = e ^ N • (Z * (ga e ^ N • T.map (fun x => ga (fr x)))) := by
        rw [h1, ← hgal, Matrix.mul_assoc]
    _ = ga e ^ N • ((e ^ N • T.map fr) * ε.map fr) := by
        rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, h2, Matrix.smul_mul]
    _ = T * (ga e ^ N • (A * ε.map fr)) := by
        rw [hφ, Matrix.mul_smul, Matrix.mul_assoc]


open GlobalTheory.FrameEq in
theorem frame_Y_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y Y' hY _
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  have hz : ∀ z : ℤ_[l], inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := fun z => by
    rw [← (inclWA l).commutes z, padicInt_hom_ext_pt (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [frobW_inclW]
    rw [e1, Matrix.map_mul, hY]
    have e2 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e2, Matrix.smul_mul, ← F.φ]
    have e3 : ((inclW l τ ^ N) • F.T).map (frobW l) = frobW l (inclW l τ) ^ N • F.T.map (frobW l) := by
      ext i j; simp
    rw [e3, frobW_inclW, hτ.1, map_mul, hev, smul_smul, mul_pow, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      ext i j; simp [galW_inclW]
    have e2 : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) := by ext i j; simp [hz]
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, e1, e2, hY]
    have e3 : ((inclW l τ ^ N) • F.T).map (galW l (g : GQ l)) =
        galW l (g : GQ l) (inclW l τ) ^ N • F.T.map (galW l (g : GQ l)) := by
      ext i j; simp
    rw [e3, galW_inclW, Matrix.mul_smul, F.gal, map_pow, map_pow, smul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have key := cocycle_frob (frobW l).toRingHom (galW l (g : GQ l)).toRingEquiv.toRingHom
      (fun x => frobW_galW (g : GQ l) x) (bk.evW bk.E) F.T (F.A.map bk.evW) ((F.ε g).map (inclW l)) (zW (ρ g))
      F.unit F.φ (F.gal g) (by ext i j; simp [zW])
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, map_pow, map_pow, hev]
    have e1 : (F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))).map (inclW l) =
        (F.A.map bk.evW).map (galW l (g : GQ l)).toRingEquiv.toRingHom := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply]
      show _ = galW l (g : GQ l) (bk.evW (F.A i j))
      rw [← hev, galW_inclW]
    have e2 : ((F.ε g).map WittVector.frobenius).map (inclW l) = ((F.ε g).map (inclW l)).map (frobW l).toRingHom := by
      ext i j; simp [frobW_inclW]
    have e3 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e1, e2, e3, ← galW_inclW, hev]
    exact key

end GlobalTheory.FrameEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  first | (exact @GlobalTheory.FrameEq.frame_Y_eqs) | (exact GlobalTheory.FrameEq.frame_Y_eqs) | (intros; apply GlobalTheory.FrameEq.frame_Y_eqs  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlWcbInjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Cyc.UnitGen

theorem gen {O R P : Type*} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup P] [Module O P]
    (f : R →ₐ[O] R) (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, f b = b → ∃ x : O, b = algebraMap O R x) (e₀ t t' : P)
    (h0 : Submodule.span O {e₀} = ⊤) (htf : ∀ c : O, c • e₀ = 0 → c = 0)
    (ht : Submodule.span O {t} = ⊤) (r : R)
    (hr : r • ((1 : R) ⊗ₜ[O] t') = (1 : R) ⊗ₜ[O] e₀) :
    ∃ u : Oˣ, (1 : R) ⊗ₜ[O] t' = algebraMap O R u ⊗ₜ[O] t := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O P e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 htf, ?_⟩
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h0]
  let φ : O ≃ₗ[O] P := LinearEquiv.ofBijective _ hb
  have hφ : ∀ c, φ c = c • e₀ := fun _ => rfl
  have h1 : φ.symm e₀ = 1 := by rw [LinearEquiv.symm_apply_eq, hφ, one_smul]
  obtain ⟨c, rfl⟩ := φ.surjective t'
  obtain ⟨w, rfl⟩ := φ.surjective t
  have hrc : r * algebraMap O R c = 1 := by
    have := congrArg (fun y => TensorProduct.rid O R (φ.symm.toLinearMap.lTensor R y)) hr
    simpa [TensorProduct.smul_tmul', h1, Algebra.smul_def, mul_comm] using this
  have hfr : f r = r := by
    have h2 : f r * algebraMap O R c = 1 := by
      rw [← f.commutes c, ← map_mul, hrc, map_one]
    calc f r = f r * (r * algebraMap O R c) := by rw [hrc, mul_one]
      _ = r * (f r * algebraMap O R c) := by ring
      _ = r := by rw [h2, mul_one]
  obtain ⟨c', rfl⟩ := hf r hfr
  have hc : c' * c = 1 := hinj (by rw [map_mul, hrc, map_one])
  obtain ⟨w', hw'⟩ := Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {φ w})
  have hw : w' * w = 1 := by
    apply φ.injective
    rw [← smul_eq_mul, map_smul, hw', hφ, one_smul]
  refine ⟨⟨c * w', c' * w, ?_, ?_⟩, ?_⟩
  · linear_combination (w' * w) * hc + hw
  · linear_combination (w' * w) * hc + hw
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← map_smul, smul_eq_mul,
      mul_assoc, hw, mul_one]

variable {l : ℕ} [Fact l.Prime]

theorem zl_wcb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero h
  · exact WittVector.p_nonzero l (Cb l) (eq_zero_of_pow_eq_zero h)

theorem ol_rw_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) :=
  by
    haveI := GlobalTheory.Cyc.FontW.free_OL LL
    set_option synthInstance.maxHeartbeats 200000 in
      exact Algebra.TensorProduct.includeLeft_injective (S := ↥(OL LL)) zl_wcb_injective

theorem fixed_RW (LL : FinExt l) (b : RW LL) (hb : φRW LL b = b) :
    ∃ x : ↥(OL LL), b = algebraMap ↥(OL LL) (RW LL) x :=
  by
    haveI := GlobalTheory.Cyc.FontW.free_OL LL
    set_option synthInstance.maxHeartbeats 200000 in
      exact (GlobalTheory.Cyc.FontW.as_one (O := ↥(OL LL)) (frobW l) (GlobalTheory.ArtinSchreierWitt.main l).1
        (GlobalTheory.ArtinSchreierWitt.main l).2.1).2 b hb

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem of_tie {W : LocWach PD LL O v n} {RA R : Type} [CommRing RA] [CommRing R] [Algebra O RA]
    [Algebra O R] {inclR : RA →ₐ[O] R} {φR : R →ₐ[O] R} {gR : G → (R →ₐ[O] R)} {πA : RA}
    (E : EtTie W RA R inclR φR gR πA) (hO : Function.Injective (algebraMap O LL))
    (hinj : Function.Injective (algebraMap O R))
    (hf : ∀ b, φR b = b → ∃ x : O, b = algebraMap O R x)
    (hT : ∀ b, TWmap φR W.one b = b → ∃ t : ↥W.one.L.T, b = (1 : R) ⊗ₜ[O] t)
    (e : W.DD W.one) (t : ↥W.one.L.T) (hN : W.N W.one = Submodule.span (LetA O n) {e})
    (hφ : W.φD W.one e = e) (ht : Submodule.span O {(t : W.one.V)} = W.one.L.T) :
    ∃ u : Oˣ, E.jD W.one e = algebraMap O R u ⊗ₜ[O] t := by
  obtain ⟨e', e₀, h0, hj, hN'⟩ := E.one_e
  obtain ⟨t', ht'⟩ := hT (E.jD W.one e) (by rw [← E.jD_φ, hφ])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (show e' ∈ Submodule.span (LetA O n) {e} by
      rw [← hN, hN']; exact Submodule.mem_span_singleton_self _)
  have hne : (e₀ : W.one.V) ≠ 0 := by
    obtain ⟨x, hx, hxT⟩ := W.one_line
    intro h
    have hxm : x ∈ W.one.L.T := by rw [hxT]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (h0 ▸ Submodule.mem_top : (⟨x, hxm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀})
    have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, h, smul_zero] at this
    exact hx this.symm
  rw [ht']
  refine gen φR hinj hf e₀ t t' h0 (fun c hc => ?_) ?_ (E.ioE (algebraMap _ W.EE a)) ?_
  · have := congrArg Subtype.val hc
    rw [Submodule.coe_smul, ← algebraMap_smul LL] at this
    exact hO (((smul_eq_zero.1 this).resolve_right hne).trans (map_zero _).symm)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (show x ∈ Submodule.span O {(t : W.one.V)} from ht.ge hx)
    exact Submodule.mem_span_singleton.2 ⟨c, Subtype.ext hc⟩
  · rw [← ht', ← E.jD_smul, algebraMap_smul, ha, hj]

end Gen

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (e : W.DD W.one) (t : ↥W.one.L.T), W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} → W.φD W.one e = e → Submodule.span ↥(OL LL) {(t : W.one.V)} = W.one.L.T → ∃ u : (↥(OL LL))ˣ, E.jD W.one e = ((u : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro D HW F l _ K s LL h W E e t hN hφ ht
  exact of_tie E Subtype.val_injective (ol_rw_injective LL) (fixed_RW LL)
    (GlobalTheory.Cyc.FontW.as_TW LL W.one).2 e t hN hφ ht

end GlobalTheory.Cyc.UnitGen
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrExtUnit

theorem exists_unit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    let S := sit D.loc HW l (D.locA l) K s LL h
    let E : S.Comparison₂ := ((F l).E K s LL h).tie
    ∀ (e : S.W.DD S.W.one) (t : ↥S.W.one.L.T),
      S.W.N S.W.one = Submodule.span (LetA S.O S.n) {e} → S.W.φD S.W.one e = e →
      Submodule.span S.O {(t : S.W.one.V)} = S.W.one.L.T →
      ∃ u : (S.O)ˣ, ∀ a : S.O,
        E.jD S.W.one (a • e) = (1 : S.RW) ⊗ₜ[S.O] (((u : S.O) * a) • t) := by
  intro S E e t hN hφ ht
  obtain ⟨u, hu'⟩ : ∃ u : (S.O)ˣ, E.jD S.W.one e = (algebraMap S.O S.RW (u : S.O)) ⊗ₜ[S.O] t :=
    GlobalTheory.Cyc.UnitGen.main D HW F l K s LL h e t hN hφ ht
  refine ⟨u, fun a => ?_⟩
  rw [map_smul, hu', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem smul_cocycle (S : Sit) {T Tp : LocLat S.G S.Qp S.LL S.O} (ι : LatHom T.L Tp.L) (x : T.V)
    (g : S.G) (et : Tp.V) (hx : ι.f x = Tp.ρ g et - et) (b : S.O) :
    ι.f (b • x) = Tp.ρ g (b • et) - b • et := by
  rw [← algebraMap_smul S.LL b x, ← algebraMap_smul S.LL b et, map_smul, map_smul, hx, smul_sub]

theorem smul_proj (S : Sit) {Tp Z : LocLat S.G S.Qp S.LL S.O} (π : LatHom Tp.L Z.L)
    (et : Tp.V) (b : S.O) : b • π.f et = π.f (b • et) := by
  rw [← algebraMap_smul S.LL b et, map_smul, algebraMap_smul]

theorem over_Ks (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExt (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.Cyc.dict_ext_Ks D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨_, resFun_Z1T T _ c hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem over_K (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExtΔ (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro _ hp T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hδ hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.ExtDict.dict_K D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    (fun h2 => absurd h2 hp) T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) hδ ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨c, hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F :=
  fun D HW F l _ K s LL h => ⟨over_Ks D HW F l K s LL h, over_K D HW F l K s LL h⟩

end GlobalTheory.HerrExtUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {B C D : Obj l R} (h : Hom B C) (h₂ : Hom C D) (m : ℕ) :
    qmap (h₂.comp h) m = (qmap h₂ m).comp (qmap h m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem stable_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C)
    (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  intro l _ R _ B C D h h₂ s s₂
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · rw [qmap_comp]
    exact RingHom.Flat.comp (s.flat m) (s₂.flat m)
  · obtain ⟨C', k', h', p⟩ := s.po B' k
    obtain ⟨D', k'', h₂', p₂⟩ := s₂.po C' k'
    refine ⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩
    · apply Hom.ext'
      have e1 := congrArg Hom.f p.comm
      have e2 := congrArg Hom.f p₂.comm
      change k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f
      change k'.f.comp h.f = h'.f.comp k.f at e1
      change k''.f.comp h₂.f = h₂'.f.comp k'.f at e2
      rw [← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]
    · have := (p.po m).paste_horiz (p₂.po m)
      rw [qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      exact this

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomCompStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStablePrismHom_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C) (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  first | exact @GlobalTheory.BSP.stable_comp | exact GlobalTheory.BSP.stable_comp | (intros; apply GlobalTheory.BSP.stable_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFg
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AdicComplExists

variable {L : Type} [CommRing L] {J : Ideal L}

theorem evalₐ_algebraMap' (n : ℕ) (r : L) :
    AdicCompletion.evalₐ J n (algebraMap L (AdicCompletion J L) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem mem_map_pow_iff (hfg : J.FG) (n : ℕ) (y : AdicCompletion J L) :
    y ∈ (J ^ n).map (algebraMap L (AdicCompletion J L)) ↔ AdicCompletion.evalₐ J n y = 0 := by
  rw [← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (J ^ n • ⊤ : Ideal L) = J ^ n := by ext x; simp
  exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq L h').injective).symm

end GlobalTheory.BSP.AdicComplExists


open GlobalTheory.BSP.AdicComplExists in
theorem GlobalTheory.BSP.isCompl_exists : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG →
    ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  intro L _ J hfg
  refine ⟨AdicCompletion J L, inferInstance, algebraMap L (AdicCompletion J L), ⟨?_, ?_, ?_⟩⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  · intro x n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    exact ⟨r, by rw [mem_map_pow_iff hfg, map_sub, evalₐ_algebraMap', hr, sub_self]⟩
  · intro a n ha
    rw [mem_map_pow_iff hfg, evalₐ_algebraMap'] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAdicCompletionMap_of_fg : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG → ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  first | exact @GlobalTheory.BSP.isCompl_exists | exact GlobalTheory.BSP.isCompl_exists | (intros; apply GlobalTheory.BSP.isCompl_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSucc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_pow_succ_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A),
    (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  intro l hl A _ D J hlJ n
  have hl0 : 0 < l := hl.out.pos
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1) := by
      rw [pow_succ' J (n + 1)] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        refine ⟨?_, ?_⟩
        · rw [pow_succ' J (n + 1)]; exact Ideal.mul_mem_mul ha hb
        · rw [D.δ_mul]
          have h1 : a ^ l * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)
          have h2 : b ^ l * D.δ a ∈ J ^ (n + 1) :=
            Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)
          have h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)
          exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨Ideal.add_mem _ hy1 hz1, ?_⟩
        rw [D.δ_add]
        refine Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)
        have hk0 : 0 < k := (Finset.mem_Ioo.1 hk).1
        have hyk : y ^ k ∈ J ^ (n + 1) :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)
    exact key.2

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSuccStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_pow_succ_mem_pow | exact GlobalTheory.BSP.delta_pow_succ_mem_pow | (intros; apply GlobalTheory.BSP.delta_pow_succ_mem_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAndIsogenyInvariant
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem pow_smul_eq (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : LetA O n) ^ k • x = ((PD.p : ℕ) : O) ^ k • x := by
  rw [← map_natCast (algebraMap O (LetA O n)), ← map_pow, algebraMap_smul]

theorem sat_of (T : LocLat G Qp LL O)
    (hs : ∀ (m : ℕ) (x : W.DD T), ((PD.p : O) ^ m) • x ∈ W.N T → x ∈ W.N T) : wachSaturated W T := by
  rintro x ⟨k, hk⟩
  rw [pow_smul_eq] at hk
  exact hs k x hk

theorem isog_of {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L)
    (hi : Function.Bijective f.f → Function.Injective (W.map f) ∧
      (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
        (y ∈ W.N T → x ∈ W.N T')) ∧
      ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T') : p6V W f := by
  intro hf
  obtain ⟨hinj, ⟨c, hc⟩, -⟩ := hi hf
  refine ⟨fun x _ hx => hinj (hx.trans (map_zero _).symm), fun y hy => ?_⟩
  obtain ⟨x, hx, hxN⟩ := hc y
  exact ⟨c, x, hxN hy, hx.trans (pow_smul_eq W T c y).symm⟩

end Generic


set_option linter.unusedVariables false in
theorem saturated_and_isogeny_invariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; (∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → wachSaturated W T) ∧ ∀ (T' T : Lt K LL) (f : LatHom T'.L T.L), IsCrys ((D.loc l).PD K) T'.ρ → IsCrys ((D.loc l).PD K) T.ρ → p6V W f := by
  intro D HW F l _ K s LL h W E
  refine ⟨fun T hT => sat_of W T fun m x hx => sat_loc (HW l) K s LL h T hT m x hx,
    fun T' T f hT' hT => isog_of W f fun hf => isog_loc (HW l) K s LL h T' T f hT' hT hf⟩

end GlobalTheory.NL.Isog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  intro l _ K bk A _ s ι TB a x
  haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨TB.c i y, TB.c_mul i a y⟩
  · intro h
    by_cases ha : a = 0
    · subst ha
      refine ⟨0, ?_⟩
      rw [mul_zero]
      exact h1 x fun i => zero_dvd_iff.1 (h i)
    · choose z hz using h
      obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})
      have key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n := by
        intro n w hw
        have hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a} := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hw
          · exact Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩
        rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hmem
        have h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤
            bk.J ^ n * Ideal.span {a} :=
          Submodule.smul_mono le_rfl inf_le_right
        obtain ⟨v, hv, hva⟩ := Ideal.mem_mul_span_singleton.1 (h2 hmem)
        have hwv : w = v := mul_left_cancel₀ ha (by rw [← hva, mul_comm])
        exact hwv ▸ hv
      have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := fun n =>
        (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))
      obtain ⟨y, hy⟩ := h4 z hfin
      refine ⟨y, ?_⟩
      have h0 := h1 (x - s a * y) fun i => by
        rw [map_sub, TB.c_mul, hy, hz, sub_self]
      exact sub_eq_zero.1 h0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  first | exact @GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | exact GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | (intros; apply GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeft
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mat_cancel_left {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (B M M' : Matrix n n R) (hB : B.det ∈ nonZeroDivisors R) (h : B * M = B * M') : M = M' := by
  have h2 : B.det • M = B.det • M' := by
    have e : ∀ N : Matrix n n R, B.det • N = B.adjugate * (B * N) := fun N => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, h]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  have h4 : (M i j - M' i j) * B.det = 0 := by rw [sub_mul, mul_comm (M i j), mul_comm (M' i j), h3, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hB) _ h4)

theorem bas_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  intro l _ K bk d ρ τ s ht C _ F hE M M' h
  set G : bk.S →+* C := F.comp (toDisc l (X : bk.S) bk.ρ₀) with hG
  have hbas : ht.bas.map F = s.X.map G * ht.Z.map F := by
    rw [bas, Matrix.map_mul, Matrix.map_map]; rfl
  have hl : IsUnit (G (l : bk.S)) := by
    rw [map_natCast]
    have := (isUnit_l_disc l (X : bk.S) bk.ρ₀).map F
    rwa [map_natCast] at this
  have hc : G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ∈ nonZeroDivisors C := by
    rw [map_mul, map_pow, map_pow]
    exact Submonoid.mul_mem _ (Submonoid.pow_mem _ hl.mem_nonZeroDivisors _) (Submonoid.pow_mem _ hE _)
  have hdet : (s.X.map G).det * (s.X'.map G).det = G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ^ d := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, s.X_mul, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero G),
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hX : (s.X.map G).det ∈ nonZeroDivisors C :=
    (mul_mem_nonZeroDivisors.1 (hdet ▸ Submonoid.pow_mem _ hc _)).1
  have hZ : IsUnit (ht.Z.map F).det := by
    have := ht.Z_unit.map F.mapMatrix
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  refine mat_cancel_left _ M M' ?_ h
  rw [hbas, Matrix.det_mul]
  exact Submonoid.mul_mem _ hX hZ.mem_nonZeroDivisors

end GlobalTheory.BSP.Height
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeftStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_matrix_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  first | exact @GlobalTheory.BSP.Height.bas_map_cancel_left | exact GlobalTheory.BSP.Height.bas_map_cancel_left | (intros; apply GlobalTheory.BSP.Height.bas_map_cancel_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfMemProKer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.TameRead

open GlobalTheory.TameQuot

theorem eq_one_of_mem_proKer {I M : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [AddCommGroup M] {l : ℕ} [Fact l.Prime] {k : ℕ}
    (hM : ∀ m : M, (l ^ k) • m = 0) (θ : I →* Multiplicative M)
    (ho : IsOpen (θ.ker : Set I)) {σ : I} (hσ : σ ∈ proKer l I) : θ σ = 1 := by
  refine mem_proKer.1 hσ θ.ker inferInstance ho ?_
  have := Subgroup.quotient_finite_of_isOpen _ ho
  refine IsPGroup.iff_card.1 fun x => ⟨k, ?_⟩
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
  exact hM (θ τ).toAdd

theorem exists_gen_read : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∃ γ ∈ Ine (F := F) A, ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R (G F Ω) M) (k : ℕ), (∀ m : M, (l ^ k) • m = 0) → normV v ≡ 1 [MOD l ^ k] → (∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) → ∀ z : Z1 rho, (z.1 γ = 0 → ∀ σ ∈ Ine (F := F) A, z.1 σ = 0) ∧ ∀ φ : G F Ω, IsFrob A (normV v) φ → rho φ (z.1 γ) = z.1 γ := by
  intro hT F Ω _ _ _ _ _ l _ A v hA hl
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrel⟩ := hT F Ω l A v hA hl
  refine ⟨γ, hγ.1, ?_⟩
  intro R _ M _ _ _ _ rho k hM hq hI z
  have : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  let θ : Ine (F := F) A →* Multiplicative M :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
      have := z.2.2 (g : G F Ω) h
      rw [hI _ g.2] at this
      exact congrArg Multiplicative.ofAdd this
  have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
    (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
  have hJ : ∀ σ ∈ ineKer F A l, z.1 σ = 0 := fun σ hσ =>
    eq_one_of_mem_proKer hM θ ho (σ := ⟨σ, ineKer_le_Ine A l hσ⟩) (coe_mem_ineKer.1 hσ)
  refine ⟨fun h0 σ hσ => ?_, fun φ hφ => ?_⟩
  · have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ.1⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hJ τ hτ, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hγ.2 hσ)
    exact hτ
  · have hc : φ * γ * φ⁻¹ ∈ Ine (F := F) A := conj_mem_Ine hφ.1 hγ.1
    have h1 := hJ _ (hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec A hγ.1⟩ hφ hγ).2.1
    have h2 : θ (((⟨γ, hγ.1⟩ : Ine (F := F) A) ^ normV v)⁻¹ * ⟨_, hc⟩) = 1 := h1
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h2
    have h3 : normV v • z.1 γ = z.1 (φ * γ * φ⁻¹) := congrArg Multiplicative.toAdd h2
    have h4 : normV v • z.1 γ = z.1 γ := by
      rw [← Nat.mod_add_div (normV v) (l ^ k), add_smul, mul_smul, hM, add_zero, hq]
      conv_rhs => rw [← one_smul ℕ (z.1 γ), ← Nat.mod_add_div 1 (l ^ k), add_smul, mul_smul, hM,
        add_zero]
    have h5 := z.2.2 (φ * γ * φ⁻¹) φ
    rw [hI _ hc, inv_mul_cancel_right, z.2.2 φ γ, ← h3, h4, add_comm] at h5
    exact add_right_cancel h5

end GlobalTheory.TameRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMap
namespace GlobalTheory.BSP

theorem exists_ringHom_comp_of_isCompl : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsAdicComplete JC C →
    ∀ g : L →+* C, J.map g ≤ JC → ∃ h : Q →+* C, h.comp i = g := by
  intro L _ Q _ C _ i J JC hi hC g hg
  haveI := hC

  let ψ : (n : ℕ) → L →+* Q ⧸ (J ^ n).map i := fun n => (Ideal.Quotient.mk _).comp i
  have hψ : ∀ n, Function.Surjective (ψ n) := by
    intro n y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hi.surj x n
    exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : ∀ n, RingHom.ker (ψ n) ≤ RingHom.ker ((Ideal.Quotient.mk (JC ^ n)).comp g) := by
    intro n a ha
    have h1 : a ∈ J ^ n := hi.ker a n (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : g a ∈ (J ^ n).map g := Ideal.mem_map_of_mem g h1
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hg n h2
  let F : (n : ℕ) → Q ⧸ (J ^ n).map i →+* C ⧸ JC ^ n := fun n =>
    (Ideal.Quotient.lift (RingHom.ker (ψ n)) ((Ideal.Quotient.mk (JC ^ n)).comp g) (hker n)).comp
      (RingHom.quotientKerEquivOfSurjective (hψ n)).symm.toRingHom
  have hF : ∀ n a, F n (ψ n a) = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n a
    have : (RingHom.quotientKerEquivOfSurjective (hψ n)).symm (ψ n a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [F, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  let f : (n : ℕ) → Q →+* C ⧸ JC ^ n := fun n => (F n).comp (Ideal.Quotient.mk _)
  have hfa : ∀ n x a, x - i a ∈ (J ^ n).map i → f n x = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n x a h
    have : Ideal.Quotient.mk ((J ^ n).map i) x = ψ n a := Ideal.Quotient.eq.mpr h
    simp only [f, RingHom.comp_apply, this, hF]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow JC hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := hi.surj x n
    have ha' : x - i a ∈ (J ^ m).map i := Ideal.map_mono (Ideal.pow_le_pow_right hle) ha
    rw [RingHom.comp_apply, hfa n x a ha, hfa m x a ha']
    rfl
  refine ⟨IsAdicComplete.liftRingHom JC f hf, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero]
  refine IsHausdorff.haus' (I := JC) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom,
    hfa n (i a) a (by simp)]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMapStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsAdicComplete JC C → ∀ g : L →+* C, J.map g ≤ JC → ∃ h : Q →+* C, h.comp i = g := by
  first | exact @GlobalTheory.BSP.exists_ringHom_comp_of_isCompl | exact GlobalTheory.BSP.exists_ringHom_comp_of_isCompl | (intros; apply GlobalTheory.BSP.exists_ringHom_comp_of_isCompl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKFin

theorem finite_witt_quot (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [Finite F] [CharP F l] (n : ℕ) :
    Finite (WittVector l F ⧸ Ideal.span {(l : WittVector l F) ^ n}) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hker : RingHom.ker (WittVector.truncate (p := l) (R := F) n) =
      Ideal.span {(l : WittVector l F) ^ n} := by
    ext x
    rw [WittVector.mem_ker_truncate, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
  exact Finite.of_equiv _ ((Ideal.quotEquivOfEq hker).symm.trans
    (RingHom.quotientKerEquivOfSurjective (WittVector.truncate_surjective l n F))).toEquiv.symm

theorem finite_quot : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ),
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  intro l _ K bk n c
  haveI : Finite (Wq l bk.a ⧸ Ideal.span {(l : Wq l bk.a) ^ n}) := finite_witt_quot l (Fq l bk.a) n
  let J : Ideal (Wq l bk.a) := Ideal.span {(l : Wq l bk.a) ^ n}
  let I : Ideal bk.S := Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c}
  let g : (Fin c → Wq l bk.a ⧸ J) → bk.S ⧸ I := fun t => Ideal.Quotient.mk I
    (∑ i ∈ Finset.range c, C (if h : i < c then (t ⟨i, h⟩).out else 0) * X ^ i)
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => Ideal.Quotient.mk J (coeff (i : ℕ) s), ?_⟩
  let w : ℕ → Wq l bk.a := fun i => if h : i < c then (Ideal.Quotient.mk J (coeff i s)).out else 0
  show Ideal.Quotient.mk I (∑ i ∈ Finset.range c, C (w i) * X ^ i) = Ideal.Quotient.mk I s
  rw [Ideal.Quotient.eq]
  have hw : ∀ i < c, w i - coeff i s ∈ J := by
    intro i hi
    simp only [w, dif_pos hi]
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hsplit : (∑ i ∈ Finset.range c, C (w i) * X ^ i) - s =
      (∑ i ∈ Finset.range c, C (w i - coeff i s) * X ^ i) +
        ((∑ i ∈ Finset.range c, C (coeff i s) * X ^ i) - s) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hw i (Finset.mem_range.1 hi))
    rw [← hy, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq', hm]

end GlobalTheory.BKFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ), Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  first | exact @GlobalTheory.BKFin.finite_quot | exact GlobalTheory.BKFin.finite_quot | (intros; apply GlobalTheory.BKFin.finite_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMulAlt
universe u_1

namespace GlobalTheory.UpperUnipotentProductInertiaEigenvalues

theorem isUpUni_mul {K : Type u_1} [inst : CommRing K] {N : ℕ} {U B : Matrix (Fin N) (Fin N) K}
    (hU : Formalism.MainNotions.S.IsUpUni U) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (U * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hU i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hU i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hU i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentProductInertiaEigenvalues
end
