module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.MajorantW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisBase
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem isCompact_K_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) :=
  GlobalTheory.CompanionTheory.StdK.isCompact_of_isStdK B hB.cm b K hK
theorem height_pos_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) : Continuous a ∧ ∀ x, 0 < a x :=
  GlobalTheory.CompanionTheory.Iwasawa.continuous_pos (_root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k hB hK) ha
theorem godement_sum_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) :
    ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧
      ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨C, hC⟩ := key_bound hcm hb.2 hK ha
  have hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E,
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 (Quotient.out q).2
    exact ⟨g, hg⟩
  choose g hg using hrat
  have hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0 := fun q => by
    have hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1 :=
      ⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩
    obtain ⟨P, hP⟩ := hP
    have hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine GlobalTheory.T.left_invertible_exists_nonzero_minor E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_
    calc (P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E) * pl b (g q)
        = P * ((g q).1 : Matrix (Ix n) (Ix n) E) * ((b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1) * ((g q)⁻¹).1 *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by simp only [pl, Matrix.mul_assoc]
      _ = P * (((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1) *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by rw [hb1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hg1, Matrix.mul_one, hP]
  choose f₀ hf₀ using hnz
  let u : Cos σ Y → (Fin n → Ix n) → E := fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)
  have hu1 : ∀ q, u q (f₀ q) = 1 := fun q => div_self (hf₀ q)
  have hinj : Function.Injective u := by
    intro q q' e
    obtain ⟨c, hc⟩ := GlobalTheory.T.plucker_minors_determine_column_space E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)
    have hp := isPar_of_pl (hg q) (hg q') hc
    have : (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q) :=
      cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this.symm
  obtain ⟨C₁, c, hC₁, hcount⟩ := count hcm (Fin n → Ix n) (σ := σ)
  let h : Cos σ Y → ℝ := fun q => vecHt σ (u q)
  have h1 : ∀ q, 1 ≤ h q := fun q => by
    have := one_le_vecHt (σ := σ) (hu1 q)
    exact_mod_cast this
  have hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c := by
    intro T hT
    obtain ⟨hfin, hle⟩ := hcount T hT
    have hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} :=
      fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩
    refine ⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩
    exact_mod_cast Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin
  have a_nonneg : ∀ y, 0 ≤ a y := fun y => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa y
    rw [ha.val p t hp k hk]; exact NNReal.coe_nonneg _
  refine ⟨c, fun s' hs' => ?_⟩
  have hs0 : 0 < s' := lt_of_le_of_lt (Nat.cast_nonneg c) hs'
  have hsum : Summable fun q => h q ^ (-s') := GlobalTheory.T.summable_height_pow_of_polynomial_count _ h h1 C₁ c hcnt s' hs'
  have hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤
      ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') := by
    intro x q
    have hb1 := hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x
    have hpos : 0 < h q := lt_of_lt_of_le one_pos (h1 q)
    have hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb1
    calc _ ≤ (((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹) ^ s' := Real.rpow_le_rpow (a_nonneg _) hb2 hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
  refine ⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩
  have hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s' :=
    Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)
  refine ⟨hS, ?_⟩
  have hx1 : (1 : ℝ) ≤ ht2 x := by exact_mod_cast one_le_heightGL F x.1
  have hx0 : (0 : ℝ) ≤ ht2 x := by positivity
  have hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    exact Nat.le_ceil _
  have hT : 0 ≤ ∑' q, h q ^ (-s') := tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _
  calc ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ s' ≤ ∑' q, ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') :=
        hS.tsum_le_tsum (hterm x) (hsum.mul_left _)
    _ = (C : ℝ) ^ s' * ((ht2 x : ℝ) ^ (2 * n)) ^ s' * ∑' q, h q ^ (-s') := by
        rw [tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr
    _ = _ := by ring
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisBL
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisMult
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem siegelMult_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hn : 1 ≤ n) (χ : Chr F E) (hχ : IsHecke F E χ) (c : ℕ)
    (hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c) {b : GL (Fin n ⊕ Fin n) E}
    {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a)
    (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (A : ℂ → ℂ) (H : ℂ → modFun σ Y) (t : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧
      (∀ μ, IsGrowForm μ → Differentiable ℂ (fun s => μ (H s))) ∧
      ∀ s : ℂ, t < s.re → ∀ x, HasSum (fun q => A s * eisTerm (flat a f s₁ s) x q) ((H s).1 x) := by
  have hSec : SecLaw := Hd.secLaw
  have hWL : WallLaw := Hd.wallLaw_of Hd.secLaw
  have hD : Dict := Hd.dict
  have hDI : DictInf := Hd.dictInf
  have hCM : CMGood := Hd.cmGood_of Hd.stdGood Hd.dict Hd.dictInf
  have hGT : GrpTop := Hd.grpTop
  have hBd : BdetLaw := Hd.bdetLaw
  have hPar : ParLaw := Hd.parLaw_of Hd.bdetLaw Hd.extLaw Hd.grpTop
  have hSg : SgAll := Hd.sgAll
  obtain ⟨⟨ε, hε⟩, t₀, ht₀⟩ := hb
  have hb' : IsFrame2 σ Y b := ⟨⟨ε, hε⟩, t₀, ht₀⟩
  have hcm := hB.cm
  have hunr := hB.unram
  have hgood : (adCM σ χ).Good := hCM F E σ χ c hcm hunr hχ hres
  obtain ⟨-, -, -, ht2', hlc', hsc', hKc⟩ := hGT E (AE F E) (adCM σ χ) hgood (Fin n) ε
  let Φ := frameEquiv (Y := Y) χ ε b hε
  have hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ (adCM σ χ).uΓ ε (Fin n) := rat_iff χ ε b hε
  have hKK : ∀ x, x ∈ K ↔ Φ x ∈ (adCM σ χ).uK ε (Fin n) := fun x => GlobalTheory.T.standard_compact_frame_equiv F E σ n Y hD hDI hcm χ ε b hε B K hK x
  have hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := GlobalTheory.T.parabolic_iff_frame_parabolic F E σ n Y χ ε b hε t₀ ht₀
  have hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
    intro x
    constructor
    · intro hx
      have : par2 σ Y ≤ ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))).comap Φ.toMonoidHom :=
        (Subgroup.closure_le _).2 fun p hp => (hIP p).1 hp
      exact this hx
    · intro hx
      exact Subgroup.subset_closure ((hIP x).2 hx)
  have hH := fun x => uH_eq hD hBd χ hgood ε b hε t₀ ht₀ K hKK a ha x
  have hiwa : Iwa ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))) ((adCM σ χ).uK ε (Fin n)) := by
    intro y
    obtain ⟨p, t, hp, k, hk, e⟩ := ha.iwa (Φ.symm y)
    refine ⟨Φ p, (hIP p).1 ⟨t, hp⟩, Φ k, (hKK k).1 hk, ?_⟩
    rw [← map_mul, ← e, MulEquiv.apply_symm_apply]
  obtain ⟨-, hparU⟩ := hPar E (AE F E) (adCM σ χ) hgood (Fin n) ε (Set.univ : Set (Fin n))
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  haveI := ht2'
  haveI := hlc'
  have hW := hSg F E σ χ c hcm hunr hχ hres ε (Fin n) (by simpa using hn) hiwa
  obtain ⟨σ₀, hσ₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb' hK ha
  refine eis_from_U hSec hWL Φ (continuous_frameEquiv χ ε b hε) _ _ _ ((adCM σ χ).uC ε (Fin n))
    ((adCM σ χ).uH ε (Set.univ : Set (Fin n))) hKc hIP' hIH ?_ K a χ s₁ f hf hΓ hKK hPP hIP hH
    (continuous_frameEquiv_symm χ ε b hε) ?_ ⟨σ₀, fun σ' h => ?_⟩
  · simpa using hW
  · intro p t hp
    refine ⟨?_, ?_⟩
    · show (((adCM σ χ).χ (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hε p).1) : Circle) : ℂ) = _
      rw [GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hε t₀ ht₀ p t hp]
      rfl
    · have := ha.val p t hp 1 (one_mem _)
      rwa [mul_one] at this
  · obtain ⟨C, N, h⟩ := hσ₀ σ' h
    exact ⟨C, N, fun x => (h x).2⟩
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisHalf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.SiegelEis GlobalTheory.CompanionTheory.EisHalf
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem eis_half_plane_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (hH : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
      ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  have hKc : IsCompact (K : Set (G2 σ Y)) := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k hB hK
  obtain ⟨-, hpos⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k hB hK hH
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb hK hH
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x : G2 σ Y,
      Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') := by
    intro σ' h x
    obtain ⟨_, _, h'⟩ := hσ σ' h
    exact (h' x).1
  have hterm : ∀ (z : ℂ) (x : G2 σ Y) (q : Cos σ Y),
      ‖eisTerm (flat a f s₁ z) x q‖ ≤ C * a ((Quotient.out q).1 * x) ^ (z.re + (n : ℝ) / 2) :=
    fun z x q => hC z _
  refine ⟨fun z x => ∑' q, eisTerm (flat a f s₁ z) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro z hz x
    have h1 : σ₀ < z.re + (n : ℝ) / 2 := by linarith
    exact (Summable.of_norm_bounded ((hsum _ h1 x).mul_left C) (hterm z x)).hasSum
  · intro x z hz
    have hz' : σ₀ - (n : ℝ) / 2 < z.re := hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hz'
    set d : ℝ := z.re + 1 with hd
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hc3 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have hd3 : σ₀ < d + (n : ℝ) / 2 := by linarith
    have hu : Summable (fun q : Cos σ Y => |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2))) :=
      ((hsum _ hc3 x).add (hsum _ hd3 x)).mul_left _
    have hdiff : ∀ q : Cos σ Y,
        DifferentiableOn ℂ (fun w : ℂ => eisTerm (flat a f s₁ w) x q) {w : ℂ | c < w.re ∧ w.re < d} :=
      fun q => (differentiable_cpow_term (hpos _) s₁ _).differentiableOn
    have hle : ∀ (q : Cos σ Y) (w : ℂ), w ∈ {w : ℂ | c < w.re ∧ w.re < d} →
        ‖eisTerm (flat a f s₁ w) x q‖ ≤ |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
          a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) := by
      intro q w hw
      have hA := hpos ((Quotient.out q).1 * x)
      have h2 := rpow_le_add_rpow (u := w.re + (n : ℝ) / 2) (c := c + (n : ℝ) / 2)
        (d := d + (n : ℝ) / 2) hA (by linarith [hw.1]) (by linarith [hw.2])
      have h3 := Real.rpow_nonneg hA.le (w.re + (n : ℝ) / 2)
      calc _ ≤ C * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) := hterm w x q
        _ ≤ |C| * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h3
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have hD := Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hle
    have hmem : {w : ℂ | c < w.re ∧ w.re < d} ∈ 𝓝 z :=
      hopen.mem_nhds ⟨hc2, by rw [hd]; linarith⟩
    exact (hD.differentiableAt hmem).differentiableWithinAt
theorem eis_half_mod_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) →
      (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧
      ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k hB hK ha
  have kc := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k hB hK
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)
theorem eisHalf_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (t : ℝ) (v : ℂ → modFun σ Y), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)) ∧
      WHolo (growForms σ Y) v {s | t < s.re} := by
  obtain ⟨Ê, t, hsum, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eis_half_plane_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eis_half_mod_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Aeis
def EisBLW_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
theorem eisBLW_k : _root_.PositivityTheory.SiegelWeilFormula.Aeis.EisBLW_k := by
  intro F E _ _ _ _ _ σ B n Y hB hn χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨t₀, v, hv, hvh⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisHalf_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨A, H, t₁, hA, hAne, hHh, hHs⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.siegelMult_w_k hB hn χ hχ c hc hb hK ha s₁ f hf
  have hHv : ∀ s' : ℂ, max t₀ t₁ < s'.re → ∀ x, (H s').1 x = A s' * (v s').1 x := by
    intro s' hs' x
    have h1 := hHs s' (lt_of_le_of_lt (le_max_right _ _) hs') x
    have h2 := (hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x).mul_left (A s')
    exact h1.unique h2
  let Ehat : ℂ → G2 σ Y → ℂ := fun s' x => if max t₀ t₁ < s'.re then (v s').1 x else (H s').1 x / A s'
  refine ⟨Ehat, ⟨max t₀ t₁, ?_, ?_⟩, ?_⟩
  · intro s' hs' x
    simp only [Ehat, if_pos hs']
    exact hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x
  · intro x
    have hd : DifferentiableOn ℂ (fun s' => evAt x (v s')) {s' : ℂ | t₀ < s'.re} :=
      hvh (evAt x) (isGrowForm_evAt x)
    have hd' : DifferentiableOn ℂ (fun s' => (v s').1 x) {s' : ℂ | max t₀ t₁ < s'.re} :=
      (hd.mono fun s' (hs' : max t₀ t₁ < s'.re) => (show t₀ < s'.re from lt_of_le_of_lt (le_max_left _ _) hs'))
    refine hd'.congr fun s' hs' => ?_
    simp only [Ehat, if_pos (show max t₀ t₁ < s'.re from hs')]
  · intro s₀
    obtain ⟨k, U, u, hUo, hs₀U, hud, hUA⟩ := GlobalTheory.CompanionTheory.Entire.local_factorisation A hA hAne s₀
    refine ⟨k, U, fun s' => (u s')⁻¹ • H s', hUo.mem_nhds hs₀U, ?_, ?_⟩
    · intro s' hs' hne x
      obtain ⟨hu, hAs⟩ := hUA s' hs'
      have hpow : (s' - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      show (u s')⁻¹ * (H s').1 x = (s' - s₀) ^ k * Ehat s' x
      by_cases hre : max t₀ t₁ < s'.re
      · simp only [Ehat, if_pos hre]
        rw [hHv s' hre x, hAs]
        field_simp
      · simp only [Ehat, if_neg hre]
        rw [hAs]
        field_simp
    · intro μ hμ
      have h1 : DifferentiableOn ℂ (fun s' => (u s')⁻¹) U := hud.inv fun s' hs' => (hUA s' hs').1
      have h2 : DifferentiableOn ℂ (fun s' => μ (H s')) U := (hHh μ hμ).differentiableOn
      refine (h1.mul h2).congr fun s' _ => ?_
      simp [map_smul, smul_eq_mul]
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont PositivityTheory.SiegelWeilFormula.Khead
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem majorant_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ C : Set d.G, IsCompact C →
      ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q := by
  have hKc : IsCompact (d.K : Set d.G) := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k d.ok.good d.ok.stdK
  obtain ⟨hac, hpos⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k d.ok.good d.ok.stdK d.ok.hgt
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.flat_section_growth_bound d.K d.a hKc d.ok.hgt hpos d.χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k d.ok.good d.ok.frame d.ok.stdK d.ok.hgt
  refine ⟨σ₀ - (d.n : ℝ) / 2, fun z hz C hC => ?_⟩
  set σ' : ℝ := z.re + (d.n : ℝ) / 2 with hσ'
  have h1 : σ₀ < σ' := by linarith
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup d.G := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hKC : IsCompact ((d.K : Set d.G) * C) := hKc.mul hC
  obtain ⟨M, hM⟩ := hKC.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M', hM'⟩ := hKC.exists_bound_of_continuousOn (hac.inv₀ fun y => (hpos y).ne').continuousOn
  have hr : ∀ x, ∀ c ∈ C, d.a (x * c) ^ σ' ≤ (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a x ^ σ' := by
    intro x c hc
    obtain ⟨k, hk, e⟩ := hgt_mul_right d.ok.hgt x c
    have hkc : k * c ∈ (d.K : Set d.G) * C := Set.mul_mem_mul hk hc
    have r0 := hpos (k * c)
    have rM : d.a (k * c) ≤ |M| := (Real.le_norm_self _).trans ((hM _ hkc).trans (le_abs_self M))
    have hm := hM' _ hkc
    rw [Pi.inv_apply, norm_inv, Real.norm_of_nonneg r0.le] at hm
    have hM'pos : 0 < |M'| := lt_of_lt_of_le (inv_pos.2 r0) (hm.trans (le_abs_self _))
    have rm : |M'|⁻¹ ≤ d.a (k * c) := (inv_le_comm₀ hM'pos r0).2 (hm.trans (le_abs_self _))
    have hb : d.a (k * c) ^ σ' ≤ |M| ^ σ' + (|M'|⁻¹) ^ σ' := by
      rcases le_total 0 σ' with hs | hs
      · exact (Real.rpow_le_rpow r0.le rM hs).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _))
      · exact (Real.rpow_le_rpow_of_nonpos (inv_pos.2 hM'pos) rm hs).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    rw [e, Real.mul_rpow (hpos x).le r0.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hpos x).le _)
  obtain ⟨_, _, hsum⟩ := hσ σ' h1
  refine ⟨fun q => |C0| * (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a ((Quotient.out q).1 * 1) ^ σ', (hsum 1).1.mul_left _,
    fun g hg q => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, GlobalTheory.ThK.Dbl.flat]
    rw [Real.coe_toNNReal _ (hpos y).le]
  rw [hΦ]
  show ‖flat d.a f s₁ z ((Quotient.out q).1 * g)‖ ≤ _
  simp only [mul_one]
  calc _ ≤ C0 * d.a ((Quotient.out q).1 * g) ^ σ' := hC0 z _
    _ ≤ |C0| * d.a ((Quotient.out q).1 * g) ^ σ' := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (hpos _).le _)
    _ ≤ |C0| * ((|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a (Quotient.out q).1 ^ σ') :=
        mul_le_mul_of_nonneg_left (hr _ g hg) (abs_nonneg _)
    _ = _ := by ring
theorem eisWk_k : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k := by
  intro F E _ _ _ _ _ σ d s₁ f hf s₀
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisBLW_k F E σ d.B d.n d.Y d.ok.good d.ok.hn d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → d.G → ℂ), An.Reg (fun x : d.G => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, he, hd⟩ := hw s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hd, ?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with s hs hne
    exact he s hs hne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : d.G => (ht2 x : ℝ)) Ê s := fun s hs => by
    obtain ⟨k, H, a, e⟩ := hp s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, heq⟩ := strip one_le_height_GL2 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  obtain ⟨t2, hmaj⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.majorant_w_k d hf
  have hinv := eis_left_rat_w d.ok.hgt hf d.ok.hecke t Ê hsum
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = flat d.a f s₁ z := fun z => funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, GlobalTheory.ThK.Dbl.flat]
    rw [Real.coe_toNNReal _ (GlobalTheory.CompanionTheory.EisRat.hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → ∀ g, d.eis f s₁ z g = Ê z g := fun z hz g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz g).tsum_eq
  refine ⟨U, p, G, max t t2, hUo, hUr, hs₀, hp0, hGd, hGc, ?_, fun z hz =>
    ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩⟩
  · intro z hz γ hγ g
    obtain ⟨τ, hτ⟩ := hUr.1
    have han : ∀ x, AnalyticOnNhd ℂ (G · x) U := fun x => (hGd x).analyticOnNhd hUo
    have hz₀ : (((max τ t + 1 : ℝ)) : ℂ) ∈ rightOf (max τ t) := by simp
    refine (han (γ * g)).eqOn_of_preconnected_of_eventuallyEq (han g) hUr.isPreconnected
      (hτ (rightOf_subset (le_max_left _ _) hz₀)) ?_ hz
    filter_upwards [(isOpen_rightOf _).mem_nhds hz₀] with w hw
    have hw' : t < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    rw [heq w hw', heq w hw', hinv w hw' γ hγ g]
  · have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    rw [heq z hz1, Heisenberg₂ z hz1]
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
