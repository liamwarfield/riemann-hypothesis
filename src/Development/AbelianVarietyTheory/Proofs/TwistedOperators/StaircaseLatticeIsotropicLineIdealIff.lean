module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairLine

variable {D : D7}

open GlobalTheory.SeeSaw

theorem incA_mul_mem_idV {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
    rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
    exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv
      (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem mem_idV_inv_mul {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : D.host.E} (hx : x ≠ 0) (s : AE D) :
    s ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟) v ↔ incA D x * s ∈ idV 𝔟 v := by
  constructor
  · intro h
    have := incA_mul_mem_idV x h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at this
  · intro h
    have := incA_mul_mem_idV x⁻¹ h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) :
    (d.aᴴ * B.gram * d.a) ⟨c - 1 - p.1, by omega⟩ = Pi.single p 1 ∧
      (d.aᴴ * B.gram * frameMat B A d.ι) = 0 := by
  refine ⟨?_, ?_⟩
  · have e := d.gram
    change d.aᴴ * B.gram * d.a = _ at e
    rw [e]
    funext q
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]
    have := p.2; have := q.2
    by_cases hq : q.1 = p.1
    · rw [if_pos (by omega), if_neg (by omega), if_pos hq]
    · rw [if_neg (by omega), if_neg hq]
  · have e := d.perp
    change (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e
    have hg : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)
    have := congrArg Matrix.conjTranspose e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this

theorem line_mem {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔟 p) v := by
  classical
  obtain ⟨hf1, hf2⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp
  generalize (⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q := ⟨_, rfl⟩
  have hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p := by
    intro u
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q := rfl
    rw [this, hf1]
    simp [Pi.single_apply, dotProduct]
  have hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q := rfl
    rw [this, hf2]
    exact zero_dotProduct y
  have h3 : ∑ l, φ l * d.a l p = 1 := by
    have := congrFun hf1 p
    rw [Pi.single_eq_same, Matrix.mul_apply] at this
    rw [hφ]; exact this
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun z => ∑ l, incA D (φ l) * z l
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  constructor
  · intro h
    have hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show ∑ l, incA D (φ l) * _ ∈ _
      simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum]
      have : ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p := by
        have h1 := hφa u
        have h2 := hφM y
        rw [← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]
        rfl
      rw [this]
      exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)
    have h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v := hle h
    have e : Φ (fun k => t * incA D (d.a k p)) = t := by
      show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t
      calc ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t * incA D (∑ l, φ l * d.a l p) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_mul, mul_left_comm]
        _ = t := by rw [h3, map_one, mul_one]
    rwa [e] at h2
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hs
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b,
        ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩
      · by_cases hr : r = p
        · subst hr; simpa using hb
        · rw [Pi.single_eq_of_ne hr]; exact (𝔟 r).zero_mem
      · funext k
        rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero =>
      convert (latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext k; simp [add_mul]
    | neg x _ hx =>
      convert neg_mem hx using 1
      funext k; simp [neg_mul]

theorem colMul_dJ_mem_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) *
      incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i)) := by
    funext k
    show a * incA D ((F.dJ ρ h).e k i) = _
    rw [he]
    show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _
    rw [map_mul, ← mul_assoc, mul_comm a]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hi := i.2
  rw [e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]
  simp only [stairId, Fin.val_castLE, Nat.add_sub_cancel]

end GlobalTheory.StairLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  first | exact @GlobalTheory.StairLine.colMul_dJ_mem_iff | exact GlobalTheory.StairLine.colMul_dJ_mem_iff | (intros; apply GlobalTheory.StairLine.colMul_dJ_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.PlcAtW

variable {D : D7}

open Classical in
theorem cpt_atPl_self (w : Pl D.host.E) (x : Kw w) : cpt w (toEAf D (atPl w x)) = x := by
  rw [(atPl_spec w x).2 w, Pi.single_eq_same]

theorem atPl_zero (w : Pl D.host.E) : atPl w (0 : Kw w) = 0 := by
  have h := atPl_add w 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def atPlHom (w : Pl D.host.E) : Kw w →+ AE D where
  toFun := atPl w
  map_zero' := atPl_zero w
  map_add' := atPl_add w

theorem atPl_cpt (w : Pl D.host.E) (a : AE D) : atPl w (cpt w (toEAf D a)) = atPl w 1 * a := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [(atPl_spec w _).1, map_mul, (atPl_spec w 1).1, zero_mul]
  · rw [(atPl_spec w _).2 Q, map_mul, map_mul, (atPl_spec w 1).2 Q]
    by_cases hQ : Q = w
    · subst hQ
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne hQ, Pi.single_eq_of_ne hQ, zero_mul]

theorem valuation_le_of_inv_mul {k : Type} [Field k] [ValuativeRel k] (u : kˣ) (b : k)
    (h : ValuativeRel.valuation k (((u⁻¹ : kˣ) : k) * b) ≤ 1) :
    ValuativeRel.valuation k b ≤ ValuativeRel.valuation k (u : k) := by
  have hne : ValuativeRel.valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h
  calc ValuativeRel.valuation k b
      = ValuativeRel.valuation k (u : k) * ((ValuativeRel.valuation k (u : k))⁻¹ * ValuativeRel.valuation k b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
    _ = _ := mul_one _

theorem cpt_atPl_mul (w : Pl D.host.E) (x : Kw w) (z : AE D) :
    cpt w (toEAf D (atPl w x * z)) = x * cpt w (toEAf D z) := by
  rw [map_mul, map_mul, cpt_atPl_self]

theorem valuation_cpt_le_one (w : Pl D.host.E) (x : AE D) (h : finPart D x ∈ intAE D) :
    ValuativeRel.valuation (Kw w) (cpt w (toEAf D x)) ≤ 1 := by
  have h2 := ((GlobalTheory.StdFrames.comp_toAd D).int x).1 h w
  have h3 : cpt w (toEAf D x) ∈ (ValuativeRel.valuation (Kw w)).integer :=
    (GlobalTheory.FinPl.SplitPoint.mem_integer_iff D.host.E w _).2 h2
  exact h3

end GlobalTheory.PlcAtW

open scoped TensorProduct

namespace GlobalTheory.PlcAtW

variable {D : D7}

open scoped Topology in
theorem continuous_cpt_toEAf (w : Pl D.host.E) : Continuous fun a : AE D => cpt w (toEAf D a) := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero (Kw w)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  let f : AE D →+ Kw w := ((cpt w).comp (toEAf D)).toAddMonoidHom
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine (IsValuativeTopology.hasBasis_nhds_zero (Kw w)).tendsto_right_iff.2 fun γ _ => ?_
  have hϖ : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) < 1 := by
    rw [isUnif_unifAt w]
    exact ValuativeRel.uniformizer_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ γ
  set u : (Kw w)ˣ := unifAt w ^ n
  have hu : ValuativeRel.valuation (Kw w) (u : Kw w) < γ := by
    simpa [u, Units.val_pow_eq_pow_val, map_pow] using hn
  have hU : {z : AE D | finPart D (atPl w ((u⁻¹ : (Kw w)ˣ) : Kw w) * z) ∈ intAE D} ∈ 𝓝 (0 : AE D) := by
    refine IsOpen.mem_nhds (h1.preimage (hfc.comp (continuous_const.mul continuous_id))) ?_
    simp only [Set.mem_setOf_eq, mul_zero, map_zero]
    exact zero_mem _
  filter_upwards [hU] with z hz
  have h3 := valuation_cpt_le_one w _ hz
  rw [cpt_atPl_mul] at h3
  exact (valuation_le_of_inv_mul u _ h3).trans_lt hu

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

variable {D : D7}

theorem continuous_atPl (w : Pl D.host.E) : Continuous (atPl (D := D) w) := by
  classical
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, -, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  have ht : Function.Bijective (toAd D) :=
    ⟨GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D), GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)⟩
  let R : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    RingEquiv.ofBijective ((toAd D).comp (Formalism.IndefR.Lev.swapAE D)) (ht.comp hs)
  have hfin : ∀ y, finPart D (e.symm (0, y)) = y := fun y => by
    rw [← (he _).2, RingEquiv.apply_symm_apply]
  have hR : Continuous R.symm := by
    refine GlobalTheory.AdeleBaseChange.continuous_symm_finite D.host.F D.host.E R fun y => ?_
    have key := (GlobalTheory.StdFrames.comp_toAd D).int (e.symm (0, y))
    rw [hfin] at key
    have e1 : ((toAd D).comp (toEAf D)) (e.symm (0, y)) = R y := by
      show toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, y)))) = toAd D (Formalism.IndefR.Lev.swapAE D y)
      rw [hfin]
    rw [e1] at key
    exact key
  have hform : ∀ x, atPl w x = e.symm (0, R.symm (singleV D.host.E w x)) := fun x => by
    refine ae_ext ?_ fun Q => ?_
    · rw [(atPl_spec w x).1, ← (he _).1, RingEquiv.apply_symm_apply]
    · rw [(atPl_spec w x).2 Q]
      show _ = toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, R.symm (singleV D.host.E w x))))) Q
      rw [hfin]
      show _ = R (R.symm (singleV D.host.E w x)) Q
      rw [RingEquiv.apply_symm_apply]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same]
        exact (RestrictedProduct.single_eq_same _ _ _).symm
      · rw [Pi.single_eq_of_ne hQ]
        exact (RestrictedProduct.single_eq_of_ne _ _ hQ).symm
  rw [funext hform]
  exact hes.comp (continuous_const.prodMk (hR.comp (GlobalTheory.FinPl.SplitPoint.continuous_single_at D.host.E w)))

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

theorem exists_plc : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  intro D w e he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_singleton]
  have h := hes w (Finset.mem_singleton_self w)
  have he1 := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h
  refine ⟨{ e := es w
            split := h.1
            π := (cpt w).comp (toEAf D)
            ι := atPlHom w
            π_ι := cpt_atPl_self w
            ι_π := fun a => by
              show atPl w (cpt w (toEAf D a)) = es w * a
              rw [atPl_cpt, ← he1]
            cont_π := continuous_cpt_toEAf w
            cont_ι := continuous_atPl w }, ⟨h, fun _ => rfl, fun _ => rfl⟩, rfl⟩

end GlobalTheory.PlcAtW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionPlaceData : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  first | exact @GlobalTheory.PlcAtW.exists_plc | exact GlobalTheory.PlcAtW.exists_plc | (intros; apply GlobalTheory.PlcAtW.exists_plc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VecsLast

open ValuativeRel

theorem exists_nat_val_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) ≤ valuation k ((ϖ ^ d : kˣ) : k) := by
  refine ⟨GlobalTheory.SplitWeil.resCard k ^ d, pow_pos ?_ d, ?_⟩
  · unfold GlobalTheory.SplitWeil.resCard
    exact Nat.card_pos
  · rw [Nat.cast_pow, map_pow, Units.val_pow_eq_pow_val, map_pow, hϖ]
    exact pow_le_pow_left₀ zero_le' (le_uniformizer_iff.2 GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one) d

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_prodCoord {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {P : Finset (Pl D.host.E)}
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, Mx D m n →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ z, IsHalf e z → (z ∈ Λ ↔ ∀ w : P, GlobalTheory.StepData.IntM (c w z)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e Λ (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  classical
  choose N hN0 hN using fun w : P => exists_nat_val_le (isUnif_unifAt (D := D) w.1) (d w)
  have hk0 : 0 < ∏ w : P, N w := Finset.prod_pos fun w _ => hN0 w
  have hhalf : ∀ (a : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (a • u) := fun a u hu i j => by
    show e * (a • u) i j = (a • u) i j
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]
  have hadd : ∀ {t u : Mx D m n}, IsHalf e u → (IsHalf e (t + u) ↔ IsHalf e t) := fun {t u} hu => by
    constructor
    · intro h i j
      have h1 := h i j
      have h2 := hu i j
      simp only [Matrix.add_apply, mul_add] at h1
      linear_combination h1 - h2
    · intro h i j
      simp only [Matrix.add_apply, mul_add, h i j, hu i j]
  refine ⟨fun t ht => ?_, ∏ w : P, N w, hk0, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hc'
    exact ht (if_neg hc')
  · have hku := hhalf (∏ w : P, N w) u hue
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ((hadd hku).2 ht), if_pos ht]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_add (f := _), map_nsmul]
      refine h2 w _ _ fun i j => ?_
      have hint := (hc u hue).1 hu w i j
      rw [Valuation.mem_integer_iff] at hint
      rw [Matrix.smul_apply, nsmul_eq_mul, map_mul]
      have hle : valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) ≤ valuation (Kw w.1) (N w : Kw w.1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Nat.cast_mul, map_mul]
        exact mul_le_of_le_one_right' (GlobalTheory.RootEx.UnipPow.valuation_natCast_le_one _)
      calc valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) * valuation (Kw w.1) (c w u i j)
          ≤ valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) := mul_le_of_le_one_right' hint
        _ ≤ _ := hle.trans (hN w)
    · rw [if_neg (fun h => ht ((hadd hku).1 h)), if_neg ht]
  · dsimp only at ht
    have hE : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hE] at ht
    have hmem : t ∈ Λ := (hc t hE).2 fun w => h1 w _ (Finset.prod_ne_zero_iff.1 ht w (Finset.mem_univ _))
    exact Λ.nsmul_mem hmem _

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_frames {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1))
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, WO S T →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ (w : P) z, GlobalTheory.StepData.IntM (c w z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w.1)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  refine isSBHalf_prodCoord c (fun z hz => ?_) d ψ h1 h2
  rw [GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT hβS hβT he hAA z hz]
  exact ⟨fun h w => (hc w z).2 (h w.1 w.2), fun h w hw => (hc ⟨w, hw⟩ z).1 (h ⟨w, hw⟩)⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem coord_add (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (x y : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (x + y) = B.coord t w hX hY x + B.coord t w hX hY y := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

noncomputable def coordHom (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) :
    Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D) →+
      Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w) :=
  AddMonoidHom.mk' (fun z => B.coord t w hX hY (z.map fun a => cpt w (toEAf D a))) fun x y => by
    rw [Matrix.map_add _ (fun a b => by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)])]
    exact coord_add B t w hX hY _ _

theorem coordHom_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (coordHom B t w hX hY z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) :=
  GlobalTheory.MixVacBig.coord_int_iff B t w hX hY z

theorem natDatum_props {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} {ϖ : kˣ} {dp : ℕ} {φ : Matrix a b k → ℂ} (h : GlobalTheory.SplitFlip.IsNatDatum ϖ dp φ) :
    (∀ M, φ M ≠ 0 → GlobalTheory.StepData.IntM M) ∧
      ∀ M N, (∀ i j, valuation k (N i j) ≤ valuation k ((ϖ ^ dp : kˣ) : k)) → φ (M + N) = φ M := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun M hM i j => ?_, fun M N hN => hi M N ?_⟩
  · by_contra hc
    refine hM (hs M fun hm => hc ?_)
    have := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat.1 hm i j
    rw [Valuation.mem_integer_iff]
    simpa using this
  · exact GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat.2 hN

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

theorem vecs_last : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.theta D.R.m j))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac inferInstance inferInstance hS hT he (ch.rm.vT_is t D.R.m j le_rfl j.2) hSB
    exact ⟨f, hSB, hf⟩
  · have hS : IsSelfDualC (ch.G.pS (.chi i D.R.m)) (ch.G.latS (.chi i D.R.m)) :=
      isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) D.R.m) ⟨i.2, le_rfl⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.chi i D.R.m)) (ch.G.latT (.chi i D.R.m)) :=
      (node_isV ch.G hL (X := .grid (i : ℕ) D.R.m) ⟨i.2.le, le_rfl⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := (i : ℕ) + 1) (j := D.R.m) i.2 le_rfl
    have hβT := ch.S.B.isFrame_β hL (i := (i : ℕ)) (j := D.R.m) i.2.le le_rfl
    have hmem : GlobalTheory.SplitFlip.Edge.ex i D.R.m ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.ex i D.R.m))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac inferInstance inferInstance hS hT he (ch.rm.vX_is i D.R.m i.2 le_rfl) hSB
    exact ⟨f, hSB, hf⟩

end GlobalTheory.VecsLast
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_row_column_product_data_have_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  first | exact @GlobalTheory.VecsLast.vecs_last | exact GlobalTheory.VecsLast.vecs_last | (intros; apply GlobalTheory.VecsLast.vecs_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPla
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPla
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModBarOff

theorem idV_mul_inv_iff {D : D7} {v : GlobalTheory.FinPl.Pl D} (I : Ideal (𝓞 D.host.E)) (t : 𝓞 D.host.F) (ht : t ∉ v.asIdeal)
    (hI : algebraMap D.host.F D.host.E (t : D.host.F) ∈ (I : GlobalTheory.SeeSaw.FI D))
    (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D) :
    s ∈ GlobalTheory.SeeSaw.idV (𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hI0 : (I : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hI
    exact hF ((map_eq_zero _).1 hI)
  have e : 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) = 𝔞 := by
    rw [mul_assoc, inv_mul_cancel₀ hI0, mul_one]
  constructor
  · revert s
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, h1, h2, a, ha, rfl⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
    refine AddSubgroup.subset_closure ⟨_, g1, g2, _, ?_, GlobalTheory.IdVGen.tmul_eq ht α a⟩
    rw [← e, mul_comm (algebraMap D.host.F D.host.E (t : D.host.F)) a]
    exact FractionalIdeal.mul_mem_mul ha hI
  · refine fun h => GlobalTheory.SeeSaw.idV_mono ?_ v h
    calc 𝔞 = 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) := e.symm
      _ ≤ 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * 1 := by
        gcongr
        exact FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _

theorem exists_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ (u ∈ P.S0 → t ∈ u.asIdeal) := by
    intro u
    by_cases hu : u ∈ P.S0
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        hv ((HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle)) ▸ hu)
      obtain ⟨t, h1, h2⟩ := SetLike.not_le_iff_exists.1 hne
      exact ⟨t, h2, fun _ => h1⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h hu⟩
  choose t ht1 ht2 using h
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, ?_, ?_⟩
  · have := v.isPrime
    exact prod_mem (S := v.asIdeal.primeCompl) fun u _ => pow_mem (show t u ∈ v.asIdeal.primeCompl from ht1 u) _
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun u hu => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 := ht2 u hu
    have h2 : t u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hu]; exact h1
    exact h2

theorem idV_mul_modulBar_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞 s
  obtain ⟨t, ht, hm⟩ := exists_mem_modul P sc hv
  refine idV_mul_inv_iff _ t ht ?_ 𝔞 s
  have h1 : algebraMap D.host.F D.host.E (t : D.host.F) ∈ ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hm, rfl⟩
  have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
  have h3 : D.host.conj (algebraMap D.host.F D.host.E (t : D.host.F)) = algebraMap D.host.F D.host.E (t : D.host.F) :=
    (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  rw [h3] at h2
  exact h2

end GlobalTheory.ModBarOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPlaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ModBarOff.idV_mul_modulBar_inv | exact GlobalTheory.ModBarOff.idV_mul_modulBar_inv | (intros; apply GlobalTheory.ModBarOff.idV_mul_modulBar_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitive
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ColsFB.cols_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF σ h h' v hv i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ (σ + 1) h
  obtain ⟨hc', he', -⟩ := hF.hB σ h'
  have hz := hF.zB' σ h'
  have hζ := hF.ζ (σ + 1)
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  set t := a * incA D ((-D.host.xi0) ^ (i.1 + 1)) with ht
  have hL : FinPl.colMul (F.dJ (σ + 1) h).jX i a =
      fun k => t * incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k ⟨i.1, by omega⟩) := by
    funext k
    simp only [FinPl.colMul, HypDec.jX, GlobalTheory.MixModel.rat, he, colsOf, Matrix.map_apply, map_mul, ht]
    rw [← mul_assoc]
    rfl
  have hR : FinPl.colMul (xFB F σ h') i a =
      fun k => t * incA D ((G.colDec (2 * σ + 2) (by omega) h').a k ⟨i.1, by omega⟩) := by
    funext k
    induction i using Fin.lastCases with
    | last =>
      have e1 : (F.dB σ h').i₀ *ᵥ vecB (F.oB σ h') (F.ζ (σ + 1)) =
          (-D.host.xi0) ^ (σ + 1) • fun i => (G.colDec (2 * σ + 2) (by omega) h').a i ⟨σ, by omega⟩ := by
        rw [vecB, hζ, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hz]
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, e1, ratV, Pi.smul_apply,
        smul_eq_mul, map_mul, ht, Fin.val_last]
      rw [← mul_assoc]
    | cast j =>
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, he', colsOf,
        Matrix.map_apply, map_mul, ht, Fin.coe_castSucc]
      rw [← mul_assoc]
      rfl
  rw [hL, hR]
  have hΛ3 : G.Λ (.grid (2 * σ + 3) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hΛ2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat
      (G.Λ (.core (2 * σ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) :=
    G.sp.colLat _ _ _
  rw [hΛ3, hΛ2, (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).1,
    (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2]
  have hst : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) ⟨i.1, by omega⟩ =
      D.host.AA * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) ⟨i.1, by omega⟩ *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    have e : 2 * (σ + 1) + 1 - 1 - i.1 = (2 * σ + 2 - 1 - i.1) + 1 := by have := i.2; omega
    simp only [stairId, e, Places.stA]
    ring
  rw [hst, GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces G.pl sc hv]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.ColsFB.cols_fb | exact GlobalTheory.ColsFB.cols_fb | (intros; apply GlobalTheory.ColsFB.cols_fb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF
  have t1 := GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_frames_successive_levels : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | exact GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | (intros; apply GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb <;> assumption)
end
end
