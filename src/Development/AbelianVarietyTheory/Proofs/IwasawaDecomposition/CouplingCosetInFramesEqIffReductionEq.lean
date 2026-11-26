module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem coset_eq_iff_redV (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a a' : Sp E n}
    (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) (ha' : ((qOf P : ℕ) : E) • a' ∈ stdAt E n P) :
    {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔
      redV P (((qOf P : ℕ) : E) • a) = redV P (((qOf P : ℕ) : E) • a') := by
  have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  have key : {z | z - a ∈ stdAt E n P} = {z | z - a' ∈ stdAt E n P} ↔ a - a' ∈ stdAt E n P := by
    constructor
    · intro h
      have h0 : a ∈ {z | z - a ∈ stdAt E n P} := by
        show a - a ∈ stdAt E n P
        rw [sub_self]
        exact zero_mem _
      rw [h] at h0
      exact h0
    · intro h
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hz
        have := add_mem hz h
        rwa [sub_add_sub_cancel] at this
      · intro hz
        have := sub_mem hz h
        rwa [sub_sub_sub_cancel_right] at this
  rw [key, GlobalTheory.TopStep.mem_stdAt]
  constructor
  · intro h
    funext i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    show redP P ((((qOf P : ℕ) : E) • a) i) = redP P ((((qOf P : ℕ) : E) • a') i)
    rw [← sub_eq_zero, ← GlobalTheory.TopStep.reduction_sub hi hi']
    apply GlobalTheory.TopStep.redP_eq_zero_of_div
    convert h i using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp
  · intro h i
    have hi := GlobalTheory.TopStep.mem_stdAt.1 ha i
    have hi' := GlobalTheory.TopStep.mem_stdAt.1 ha' i
    have e := congrFun h i
    have h0 : redP P ((((qOf P : ℕ) : E) • a) i - (((qOf P : ℕ) : E) • a') i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hi hi']
      exact sub_eq_zero.2 e
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (GlobalTheory.TopStep.intAt_sub hi hi') h0
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    field_simp

end Local

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mem_vGs_of_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

theorem ptAt_coset (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧
      ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, fun z => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat]
    constructor
    · intro h w hw
      simpa [hw] using h ⟨w, Finset.mem_union_left _ hw⟩
    · intro h P
      have hP := mem_vGs_of_rowSG hQ P
      simpa [hP] using h P.1 hP

theorem cosetIn_eq (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, mem_vGs_of_rowSG hQ P⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hP := mem_vGs_of_rowSG hQ P
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact (hY y').1 hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, hz⟩

theorem bar_eq (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N)
    (hY : ∀ z, z ∈ q.1.2 ↔ ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := (hY z).1 hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, (hY y).2 fun w _ => by rw [sub_self]; exact zero_mem _, key.symm⟩

theorem cosetIn_eq_iff_bar_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  intro X Pr R sel S mu cst u j hQ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := ptAt_coset hQ q h
    obtain ⟨y', hy', hY'⟩ := ptAt_coset hQ q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    rw [funext_iff, funext_iff]
    constructor
    · intro H w
      have := H ⟨w.1, Finset.mem_union_left _ w.2⟩
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY'] at this
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff]
      exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
    · intro H P
      have hP := mem_vGs_of_rowSG hQ P
      have := H ⟨P.1, hP⟩
      rw [bar_eq q hy hY, bar_eq q' hy' hY', Set.singleton_eq_singleton_iff] at this
      rw [cosetIn_eq hQ q hY, cosetIn_eq hQ q' hY']
      exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    rw [h1 q, h1 q', h2 q, h2 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.MemChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_eq_iff_reduction_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, cosetIn q = cosetIn q' ↔ MemChart.bar q = MemChart.bar q' := by
  exact @GlobalTheory.Mem.Col2.MemChart.cosetIn_eq_iff_bar_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeUnifVal

open Formalism.L2.Host

theorem localIdele_eq_locM {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    localIdele E v x = Units.map (Formalism.L2.NC.locM v) x := by
  rfl

theorem at_val_and_unr_iff : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  intro E _ _ χ h hχ v
  have hloc : ∀ x : (v.adicCompletion E)ˣ, χ.loc v x = h.χ (Units.map (Formalism.L2.NC.locM v) x) := by
    intro x
    rw [hχ, ← localIdele_eq_locM]
    rfl
  have hiff : χ.UnrAt v ↔ h.Unr v := by
    constructor
    · intro hu u hu1
      rw [← hloc]
      exact hu u hu1
    · intro hu u hu1
      rw [hloc]
      exact hu u hu1
  refine ⟨fun hu => ⟨hiff.1 hu, fun ϖ hϖ => ?_⟩, hiff⟩
  have hs := unif_spec v
  unfold IsUnifAt at hs
  have hq : IsUnitAt v (ϖ * (atFin v (unif v))⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hs, hϖ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]
  have h1 := hu _ hq
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [← hloc, h1]
  rfl

end GlobalTheory.HeckeUnifVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiserStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeckeChar_idele_value_uniformiser : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  first | exact @GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | exact GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | (intros; apply GlobalTheory.HeckeUnifVal.at_val_and_unr_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NrmAbsOfValuationEqExp
noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

end GlobalTheory.Mem.NrmCompl
end
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.NrmCompl

theorem isNrm_nrmAbs {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) : IsNrm P (nrmAbs P) := by
  intro x
  refine ⟨fun hx => (nrmAbs_eq_one_iff P (x : P.adicCompletion L)).2 hx, fun hx => ?_⟩
  have h : Valued.v (x : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := hx
  rw [nrmAbs_of_valuation_eq_exp P h, _root_.zpow_neg_one]
  rfl

theorem exists_isNrm : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)),
    ∃ nrm : AbsoluteValue (P.adicCompletion L) ℝ, IsNrm P nrm :=
  fun _ _ _ P => ⟨nrmAbs P, isNrm_nrmAbs P⟩

end GlobalTheory.Mem.NrmCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTie

section

variable {L : Type} [Field L] [NumberField L]

def Good (F : Type) [Field F] [NumberField F] [Algebra F L] (χ : HChar L) : Prop :=
  (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) ∧ χ.TrivOn F ∧ ∀ v, χ.TameAt v

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem resFin_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ * χ').resFin v k = χ.resFin v k * χ'.resFin v k := by
  simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

omit [NumberField F] in
theorem resInf_mul (χ χ' : HChar L) (v : InfinitePlace F) (k : Fˣ) :
    (χ * χ').resInf v k = χ.resInf v k * χ'.resInf v k := by
  simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

theorem good_one : Good F (1 : HChar L) := by
  refine ⟨⟨1, one_pos, one_pow 1⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun _ _ _ _ => rfl⟩
  · simp only [HChar.resFin, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl
  · simp only [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem Good.mul {χ χ' : HChar L} (h : Good F χ) (h' : Good F χ') : Good F (χ * χ') := by
  obtain ⟨⟨n, hn, h1⟩, h2, h3⟩ := h
  obtain ⟨⟨n', hn', h1'⟩, h2', h3'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun v x hx hx' => ?_⟩
  · unfold HChar.OrderDvd at *
    rw [mul_pow, pow_mul, h1, one_pow, pow_mul', h1', one_pow, one_mul]
  · rw [resFin_mul, h2.1, h2'.1, one_mul]
  · rw [resInf_mul, h2.2, h2'.2, one_mul]
  · change χ.loc v x * χ'.loc v x = 1
    rw [h3 v x hx hx', h3' v x hx hx', one_mul]

end

theorem good_set {B : Base} (f : Fr B.toPre) (T : TwDat B) {χ : HChar B.host.E} (h : χ ∈ T.set f) : Good B.host.F χ := by
  have hd : Good B.host.F f.del := ⟨f.isDel.fin, f.isDel.triv, f.isDel.tame⟩
  have hd' : Good B.host.F f.del' := ⟨f.isDel'.fin, f.isDel'.triv, f.isDel'.tame⟩
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact good_one
  · exact hd
  · exact hd'
  · have hp : Good B.host.F (T.psi w) := ⟨(T.psi_tw w).1, (T.psi_tw w).2.1, (T.psi_tw w).2.2.1⟩
    unfold TwDat.xiTw
    split_ifs
    · exact hd'.mul hp
    · exact hd.mul hp

end GlobalTheory.Mem.Top.TupTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZOfSurjective
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev csdK : CSD X.K := MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev actK : Representation X.K (G0 X.E Pr.vGs R.r) (csdK W Ch sel mu hX).Forms :=
  g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev dimP : ℕ := (csdK W Ch sel mu hX).lvlDim (actK W Ch sel mu hX) P.grp P.chr

abbrev resK : (mtildeKGSD W Ch sel mu).EqFun ≃ₗ[X.K] (csdK W Ch sel mu hX).Forms :=
  (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)

abbrev formK (x : Fin (dimP W Ch sel mu P hX) → X.K) : (csdK W Ch sel mu hX).Forms :=
  LiftForms.lvlForm (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr x

theorem resK_symm_act (a : G0 X.E Pr.vGs R.r) (f : (csdK W Ch sel mu hX).Forms) :
    (resK W Ch sel mu hX).symm (actK W Ch sel mu hX a f) = g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm f) :=
  LinearEquiv.symm_apply_apply _ _

theorem resK_act (a : G0 X.E Pr.vGs R.r) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    actK W Ch sel mu hX a (resK W Ch sel mu hX φ) = resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a φ) := by
  show resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm (resK W Ch sel mu hX φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem formK_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    formK W Ch sel mu P hX x ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
  rw [← LiftForms.range_lvlForm]
  exact ⟨x, rfl⟩

theorem zOf_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine (mem_MtildeV_iff W Ch sel mu P _).2 ⟨Subtype.prop _, fun a => ?_⟩
  refine (resK_symm_act W Ch sel mu hX a.1 _).symm.trans ?_
  rw [formK_mem W Ch sel mu P hX x a, map_smul]

def zOf : (Fin (dimP W Ch sel mu P hX) → X.K) →ₗ[X.K] MtildeV W Ch sel mu P where
  toFun x := ⟨_, zOf_mem W Ch sel mu P hX x⟩
  map_add' x y := Subtype.ext (by simp only [map_add (f := _)]; rfl)
  map_smul' c x := Subtype.ext (by simp only [map_smul]; rfl)

theorem zOf_val (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    (zOf W Ch sel mu P hX x).1 = ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 := rfl

theorem zOf_injective : Function.Injective (zOf W Ch sel mu P hX) := by
  intro x y h
  apply LiftForms.lvlForm_injective (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr
  apply (resK W Ch sel mu hX).symm.injective
  have h1 : (zOf W Ch sel mu P hX x).1 = (zOf W Ch sel mu P hX y).1 := congrArg Subtype.val h
  exact Subtype.ext h1

theorem zOf_surjective : Function.Surjective (zOf W Ch sel mu P hX) := by
  intro φ
  obtain ⟨hφ, hact⟩ := (mem_MtildeV_iff W Ch sel mu P φ.1).1 φ.2
  have hf : resK W Ch sel mu hX ⟨φ.1, hφ⟩ ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
    intro a
    rw [resK_act, hact a, map_smul]
  rw [← LiftForms.range_lvlForm] at hf
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, Subtype.ext ?_⟩
  rw [zOf_val]
  show ((resK W Ch sel mu hX).symm (LiftForms.lvlForm _ _ P.grp P.chr x)).1 = φ.1
  rw [hx, LinearEquiv.symm_apply_apply]

end Gen

end GlobalTheory.Mem.ColTie
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Lin

variable {K M : Type} [Field K] [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} {n : ℕ}

theorem eq_sum_single (x : Fin n → K) : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_single (j : (Fin n → K) →ₛₗ[σ] M) (x : Fin n → K) :
    j x ∈ Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_single_eq (j : (Fin n → K) →ₛₗ[σ] M) :
    Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_single j x

theorem exists_equiv_of_bases {M' : Type} [AddCommGroup M'] [Module ℂ M'] (j : (Fin n → K) →ₛₗ[σ] M)
    (j' : (Fin n → K) →ₛₗ[σ] M') (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (hli' : LinearIndependent ℂ fun i => j' (Pi.single i 1))
    (hsp' : Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤) :
    ∃ e : M ≃ₗ[ℂ] M', ∀ x, e (j x) = j' x := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := Module.Basis.mk hli' hsp'.ge
  refine ⟨b.equiv b' (Equiv.refl _), fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_single x, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ j, map_smulₛₗ j', LinearEquiv.map_smul]
  congr 1
  have h1 : j (Pi.single i 1) = b i := (Module.Basis.mk_apply hli hsp.ge i).symm
  have h2 : j' (Pi.single i 1) = b' i := (Module.Basis.mk_apply hli' hsp'.ge i).symm
  rw [h1, h2, Module.Basis.equiv_apply, Equiv.refl_apply]

end Lin

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

def ipLev (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeGSD W Ch sel mu P).ip (mtildeOk W Ch sel mu hX P) z.1 z'.1

def ipK (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeKGSD W Ch sel mu).ip (mtildeKOk W Ch sel mu hX) z.1 z'.1

theorem li_zOf : LinearIndependent X.K fun i => zOf W Ch sel mu P hX (Pi.single i 1) := by
  have h := (Pi.basisFun X.K (Fin (dimP W Ch sel mu P hX))).linearIndependent.map' (zOf W Ch sel mu P hX)
    (LinearMap.ker_eq_bot.2 (zOf_injective W Ch sel mu P hX))
  simpa [Function.comp_def] using h

def jP (σ : X.K →+* ℂ) : (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] MtP W Ch sel mu P σ :=
  (toMtP W Ch sel mu P σ).comp (zOf W Ch sel mu P hX)

theorem linearIndependent_jP_single (σ : X.K →+* ℂ) : LinearIndependent ℂ fun i => jP W Ch sel mu P hX σ (Pi.single i 1) :=
  toMtilde_linearIndependent W Ch sel mu P σ (li_zOf W Ch sel mu P hX)

theorem span_range_jP_single_eq_top (σ : X.K →+* ℂ) : Submodule.span ℂ (Set.range fun i => jP W Ch sel mu P hX σ (Pi.single i 1)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← toMtilde_span W Ch sel mu P σ hX, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := zOf_surjective W Ch sel mu P hX z
  exact mem_span_single (jP W Ch sel mu P hX σ) x

end Gen

section TC

attribute [local instance] starE

def sig (B : Base) : B.fields.K →+* ℂ := B.embLL

end TC

end GlobalTheory.Mem.ColTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions.Examples₂ GlobalTheory.EX.WinLow

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  push_cast
  rw [lamOf_eq p j hj, lamOf_eq p j hj, wtQ_eq_wtN, wtQ_eq_wtN]
  have a1 : wtN p (R.N R.m - 1) ≤ wtN p (R.N j - 1) := wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : blkN R (R.N R.m - 1) < R.m := by omega
    unfold wtN
    rw [dite_eq_right c1, dite_eq_left c2]
    have e : (⟨blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold wtN
    rw [dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

theorem hcW_injective {s : Scale} {C : FC} {cD ch : ℝ} {P : PreCh} {q1 : ℕ} {a b : P.R.A → ℤ}
    {c : P.Word → Fin (P.R.k - 2) → Bool} (h : ChOK s C cD ch P q1 a b c) : Function.Injective P.hcW := by
  intro u u' huu
  apply h.inj
  funext l
  have hD : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _)
    exact_mod_cast this
  have e1 := h.code u (placeNo P.H 0) l.1 l.2
  have e2 := h.code u' (placeNo P.H 0) l.1 l.2
  rw [huu, e2] at e1
  change _ - (if c u' l then _ else _) = _ - (if c u l then _ else _) at e1
  cases h1 : c u l <;> cases h2 : c u' l <;> simp only [h1, h2, if_true, Bool.false_eq_true, if_false] at e1 ⊢ <;> (exfalso; linarith)


set_option maxHeartbeats 1000000 in
theorem ev_preX_frame : StandardLattice.SiegelMassRatioCM → Ev fun K => ∀ B : Pre, K.Over B → Nonempty (PreX B) ∧ Nonempty (Fr B) := by
  intro h2b
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ⟨0, fun cD hcD => ?_⟩⟩⟩
  obtain ⟨c2, hw⟩ := window_lower h2b eps C h0 h1 hC cD hcD
  refine ⟨max c2 0, fun ch hch => ?_⟩
  have hch0 : 0 ≤ ch := le_trans (le_max_right _ _) hch
  obtain ⟨x1, hx1⟩ := hw ch (le_trans (le_max_left _ _) hch)
  obtain ⟨x2, hx2⟩ := places_ok eps C cD ch h0 h1 hC hcD hch0
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 406 1 h0 one_pos
  refine ⟨max (max x1 x2) (max x3 (max x4 10)), ?_⟩
  rintro ⟨s, C', cD', ch', P, q1, a, b, c, std, ok, Lv, hdu, hDs, hG⟩ rfl rfl rfl he hx B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
  simp only [max_le_iff] at he hx
  obtain ⟨⟨y1, y2⟩, y3, y4, y5⟩ := hx
  have hev : (Pre.ofCh P Lv sp hT hY hA hV hz).EvenExp := (ok.hc P.u₀).2.2.2
  refine ⟨?_, Pre.nonempty_hframe _ hev⟩
  have hlow := hx1 s P q1 a b c Lv.duStar Lv.Dstar he y1 ok hdu (hDs ▸ (GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P).2)
  have hpl := hx2 s P q1 a b c he y2 ok
  obtain ⟨hf, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, hN, -⟩ := hx3 s P.R he y3 ok.rank
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hk3 := P.R.m_add_three_le_k
  have hm2 := P.R.two_le_m
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (P.R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hN' : (P.R.N P.R.m : ℝ) ≤ s.x ^ 402 := by rw [← pw]; exact_mod_cast hN
  have hb' : s.x ^ 406 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have hone : 1 ≤ s.x := by linarith
  have hz1 : 10 * s.x ^ 405 ≤ s.b := by
    calc 10 * s.x ^ 405 ≤ s.x * s.x ^ 405 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 406 := by ring
      _ ≤ s.b := hb'
  have hfN : (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 405 := by
    calc (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 3 * s.x ^ 402 := mul_le_mul hf' hN' (by positivity) (by positivity)
      _ = s.x ^ 405 := by ring
  have hN2 : (P.R.N P.R.m : ℝ) ≤ s.x ^ 405 := hN'.trans (pow_le_pow_right₀ hone (by norm_num))
  have hx2' : 10 * s.x ≤ s.x ^ 405 := by
    calc 10 * s.x ≤ s.x ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ hone (by norm_num)
  generalize s.x ^ 405 = z at hz1 hfN hN2 hx2'
  have hkN : (P.R.k : ℝ) ≤ P.R.N P.R.m := by
    have : P.R.k ≤ P.R.N P.R.m := Nat.le_add_right _ _
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hbb : 1000 * s.b ≤ s.b * s.b := by nlinarith
  have hxb : 100 * (s.x * s.b) ≤ s.b * s.b := by nlinarith
  choose πg g1 g2 g3 using ok.gnorm
  refine ⟨{ piG := πg
            piG_K := g1
            piG_norm := g2
            piG_cong := fun i => Ideal.mem_span_singleton.1 (g3 i)
            piT := Lv.piT
            piT_K := Lv.piT_K
            piT_norm := Lv.piT_norm
            piT_cong := fun u => Ideal.mem_span_singleton.1 (Lv.piT_cong u)
            pde_split := ok.arith.2.2.1
            ccK_top := P.ccK_top
            e_even := hev
            hcW_inj := hcW_injective ok
            a := s.b * s.b / 5
            g_big := fun i => ?_
            T_gt := fun u => ?_
            a_gt := ?_
            spread_le := fun u j hj τ => ?_ }⟩
  · show 2 * P.R.f * P.R.k < P.H.g i - 1
    have b1 : 1 ≤ s.b := by linarith
    have c1 : s.b ≤ (P.H.g i : ℝ) :=
      calc s.b ≤ (P.R.k : ℝ) * s.b := le_mul_of_one_le_left hb0.le hk1
        _ ≤ ((P.R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 b1) (by norm_num)
        _ ≤ _ := (ok.val.2.2.2.2.1 i).1
    have c2 : (P.R.f : ℝ) * P.R.k ≤ P.R.f * P.R.N P.R.m := mul_le_mul_of_nonneg_left hkN (by positivity)
    have c3 : ((2 * P.R.f * P.R.k + 1 : ℕ) : ℝ) < P.H.g i := by
      push_cast
      nlinarith
    have c4 : 2 * P.R.f * P.R.k + 1 < P.H.g i := by exact_mod_cast c3
    omega
  · show 4 * (s.b * s.b / 5) < (Lv.T u : ℝ)
    have w := (Lv.T_win u).1
    rw [hG] at w
    have hT0 : 0 < (Lv.Dstar / Lv.duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C' s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
      have : (0 : ℝ) < Lv.duStar u := by exact_mod_cast Lv.duStar_pos u
      have := Lv.Dstar_pos
      have : 0 < GamS C' s P.R := Real.exp_pos _
      positivity
    have c1 := ((Real.le_log_iff_exp_le hT0).1 (hlow u)).trans w
    have c2 : s.b * s.b ≤ Real.exp (P.R.m * s.L) := by
      unfold Scale.b
      rw [← Real.exp_add]
      have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm2
      have := mul_le_mul_of_nonneg_right this (by linarith : 0 ≤ s.L)
      exact Real.exp_le_exp.2 (by linarith)
    have := mul_pos hb0 hb0
    linarith
  · show ((2 * P.R.f * P.R.N P.R.m + 1 : ℕ) : ℝ) < 4 * (s.b * s.b / 5)
    push_cast
    nlinarith
  · show (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤ 2 * (s.b * s.b / 5)
    have hk0 : 0 < P.R.k := by omega
    have hm0 : 0 < P.R.m := by omega
    have hm1 : P.R.m - 1 < P.R.m := by omega
    have c1 := spread_lamOf_le (P.hcW u τ) j hj hk0 hm1
    have c2 : (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤
        (((P.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) + P.R.N P.R.m := by
      exact_mod_cast c1
    obtain ⟨⟨p1, -, -, -, p5, -, -, p8, p9⟩, p10⟩ := hpl u τ
    have p1' := (p1 0 (by omega)).2
    rw [seqOf_lt _ hk0] at p5
    rw [seqOf_lt _ hm0] at p8
    rw [seqOf_lt _ hm1] at p9
    obtain ⟨-, -, ⟨b1, v3, -⟩, -⟩ := ok.hc u
    have d1 : (P.hcW u τ).b ⟨0, hm0⟩ ≤ (P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ := by
      rw [(v3 τ _).2, (v3 τ _).1, (v3 τ _).1]
      have : (0 : ℚ) ≤ ((P.R.m - 1 : ℕ) : ℚ) * (h0v s ch' : ℚ) + (h0v s ch' : ℚ) / 2 := by positivity
      simp only [Nat.cast_zero, zero_mul]
      linarith
    have d2 : (((P.hcW u τ).b ⟨0, hm0⟩ : ℚ) : ℝ) ≤ (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) := by exact_mod_cast d1
    have d3 : (P.R.k : ℝ) * (4 * (Delv s cD' : ℝ)) ≤ 2 * s.b := by
      refine p8.trans ?_
      rw [div_le_iff₀ hx0]
      nlinarith
    have ea : s.a = s.x * s.b := rfl
    have hxb0 : 0 ≤ s.x * s.b := by positivity
    rcases p5 with ⟨q, -⟩ | ⟨-, q, -⟩ <;> linarith

end GlobalTheory.Mem.Top

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

open Cardinal Filter Topology

namespace GlobalTheory.PadicCard

theorem mk_le_pow_aleph0_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [T2Space X] (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  have h : ∀ x : X, ∃ u : ℕ → D, Tendsto (fun n => f (u n)) atTop (𝓝 x) := by
    intro x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose u hu using hv
    exact ⟨u, by simpa only [hu] using hlim⟩
  choose g hg using h
  have hinj : Function.Injective g := by
    intro x y hxy
    have := hg y
    rw [← hxy] at this
    exact tendsto_nhds_unique (hg x) this
  simpa using mk_le_of_injective hinj

theorem mk_padic_le (l : ℕ) [Fact l.Prime] : #ℚ_[l] ≤ 𝔠 := by
  simpa using mk_le_pow_aleph0_of_denseRange _ (Padic.denseRange_ratCast l)

theorem mk_padicAlgCl (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 :=
  le_antisymm
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (mk_padic_le l) aleph0_le_continuum))
    ((continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]).trans
      (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective))

theorem mk_padicComplex (l : ℕ) [Fact l.Prime] : #ℂ_[l] = 𝔠 := by
  refine le_antisymm ?_ (continuum_le_cardinal_of_nontriviallyNormedField ℂ_[l])
  calc #ℂ_[l] ≤ #(PadicAlgCl l) ^ ℵ₀ :=
        mk_le_pow_aleph0_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l))
    _ = 𝔠 := by rw [mk_padicAlgCl, continuum_power_aleph0]

theorem card_padicAlgCl_padicComplex :
    ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧
      Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  intro l _
  exact ⟨by rw [mk_padicAlgCl, mk_complex], by rw [mk_padicComplex, mk_complex]⟩

end GlobalTheory.PadicCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplexStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex : ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧ Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  first | exact @GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | exact GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | (intros; apply GlobalTheory.PadicCard.card_padicAlgCl_padicComplex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbOfRangeLe
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIdG_unique (X : Stages) {px : PreX X.B.toPre} {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    {eG eG' : Gc X.B px ≃* G0 Pg X.toD7.R.r} (h : IsPlacewiseIdentity X (px := px) eG) (h' : IsPlacewiseIdentity X (px := px) eG') : eG = eG' := by
  subst hPg
  exact MulEquiv.ext fun g => funext fun P => (h g P.1 P.2 P.2).trans (h' g P.1 P.2 P.2).symm

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) (h' : IsStdChar D ψ' s) :
    ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem isInfFam_unique {D : D7} {θ θ' : Formalism.IndefR.Datum.InfFam D} (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  Formalism.IndefR.Eqv.infFamUnique_holds D θ θ' h h'


end GlobalTheory.Mem.R3.Rw

end
end
