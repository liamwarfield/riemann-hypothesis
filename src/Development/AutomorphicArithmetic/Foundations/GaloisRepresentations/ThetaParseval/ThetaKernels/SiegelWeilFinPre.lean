module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinMid
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpMain
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocUnit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitChart
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.Tunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_chart_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)
    (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) d.κ),
    GlobalTheory.TowU.IsRat d' ∧ ∀ w, d'.e w = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w := by
  classical
  have hD := d.ok.dbl
  let τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d := Fintype.equivOfCardEq (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ) (fun w w' => by rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hright : ∀ u, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)) = u := fun u => by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']
  let e' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) ≃ₗ[AF F] (d.κ → AF F) × (d.κ → AF F) :=
    { _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ with
      invFun := fun u => d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)
      left_inv := fun w => by
        show d.dd.e.symm (act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w)) = w
        rw [hinv, LinearEquiv.symm_apply_apply]
      right_inv := hright }
  refine ⟨τ, ⟨e', fun w w' => ?_⟩, fun x => ?_, fun w => rfl⟩
  · rw [d.dd.form]
    show om (d.dd.e w) (d.dd.e w') = om (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w')
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]
  · obtain ⟨y, z, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x
    exact ⟨y, z, h⟩
theorem T_chart_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (S0' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ),
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm w)) S0 S0' ∧
    ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (fun k => d.crd X (τ k)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, d', hrat, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.exists_chart_k d
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ d.κ _ d.dd d'
    (by exact d.ok.dbl.rat) hrat
  have hop := hS.1
  have hs : (fun w => d'.e (d.dd.e.symm w)) = fun w => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm w) := funext fun w => he' _
  rw [hs] at hop
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm d.κ := hop.adm' d.l d.ok.dbl.adm
  have hinv : ∀ (y : d.κ → AF F), ∀ φ ∈ schA F d.κ, l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨w, hw⟩ : ∃ w, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = (0, y) := ⟨d'.e.symm (0, y), by rw [← he', LinearEquiv.apply_symm_apply]⟩
    obtain ⟨Z, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    exact d.ok.dbl.kill Z _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ l' hadm hinv
  refine ⟨τ, S0, S0', c, hop, fun Φ hΦ X => ?_⟩
  have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
    GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ hΦ
  have e0 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (incM F d.b.1.toCols₂)ᵀ) = (fun k => d.crd X (τ k), 0) := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame d τ X
  have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
    rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
    rfl
  rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ, e0]
  simp [schr]
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem kStd_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hb hj
  have hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  intro k
  rw [Subgroup.mem_comap, d.ok.stdK (j k)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]
  refine and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))
  rw [blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose,
    Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitHeis
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem tHeis_k : _root_.PositivityTheory.SiegelWeilFormula.THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  set_option backward.isDefEq.respectTransparency false in
  constructor
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F d.b.1.toCols₂)ᵀ) Φ, map_smul, smul_eq_mul]
    change d.B.ψ (⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) * _ = _
    rw [symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, ← Matrix.add_mul]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [hBx, Matrix.transpose_mul, ← Matrix.mul_assoc, Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F t0.1)ᵀ * (diagCols (Fin d.n))ᵀ) Φ, map_smul, smul_eq_mul, add_comm,
      l_shift h hψ _ _ hΦ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    change ⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _ + -(⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) = _
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← Matrix.transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldHgt
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbMain
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsStandardHermitianSpace
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgt
set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory.ThK.Dbl
theorem hgtEx_k : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
end GlobalTheory.ThK.Dbl
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStdEx
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
def StdEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x
theorem stdEx_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (h2 : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.GlobalTheory.ThK.Dbl.StdEx_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsHermUnitSpcK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isHerm_unitSpc_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (n : ℕ) : (unitSpc F E n).IsHerm σ B n 0 := by
  refine ⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩
  · simp only [unitSpc, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · exact map_one σ
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero σ
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hasSig_one
  · simp only [unitSpc]
    rw [mem_std]
    constructor
    · intro hy x hx
      rw [mem_std] at hx
      rw [form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))
    · intro h i
      have hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n := by
        rw [mem_std]
        intro j
        by_cases e : j = i
        · subst e; simpa using isIntegral_one
        · simpa [Pi.single_apply, e] using isIntegral_zero
      have := h _ hx
      rw [form_one] at this
      simpa [Pi.single_apply] using this
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact isCartan_one
  · exact isSplitBasis_stdLattice (B.τ v) hB.cm
end PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_standard_hermitian_space {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Y₀ : Spc F E n) (b₀ : GL (Fin n ⊕ Fin n) E) (K₀ : Subgroup (G2 σ Y₀)) (a₀ : G2 σ Y₀ → ℝ),
      IsFrame2 σ Y₀ b₀ ∧ b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n 1 ∧
      IsStdK (σ := σ) (Y := Y₀) B b₀ K₀ ∧ IsHgt K₀ a₀ := by
  obtain ⟨b, K, a, hb, hK, ha, -, -⟩ :=
    _root_.GlobalTheory.ThK.Dbl.stdEx_of_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.hgtEx_k F E σ B n (UnitHermitianSpace.unitSpc F E n) n 0 hB (Or.inl (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n))
  refine ⟨UnitHermitianSpace.unitSpc F E n, b, K, a, hb, ?_, hK, ha⟩
  obtain ⟨ε, hε⟩ := hb.1
  have hc : ∀ z : E, σ (σ z) = z := (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm |> fun _ => by
    intro z
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have h1 := eps_one hn hc (_root_.PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace.isHerm_unitSpc_k hB n).herm hε
  rw [hε, eps_unit h1]
  simp [Ald.jeps]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbVal
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jpar_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) {p : G2 σ Y} (hp : ParF b p) :
    ParF d.b (j p) ∧ (inFrame d.b (j p)).toBlocks₁₁.det = (inFrame b p).toBlocks₁₁.det := by
  obtain ⟨-, h2, h3⟩ := hJ
  set X := inFrame d.b (j p) with hX
  have hsub : ∀ x y, X (Sum.map (Ald.em0 h) (Ald.em0 h) x) (Sum.map (Ald.em0 h) (Ald.em0 h) y) = inFrame b p x y :=
    fun x y => by rw [← h2 p]; rfl
  have hl : ∀ v, X (Sum.inl (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inl (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  have hl' : ∀ v, X v (Sum.inl (Ald.i0 h)) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) v (Sum.inl (Ald.i0 h)) :=
    fun v => (h3 p _ (by simp) v).2
  have hr : ∀ v, X (Sum.inr (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  constructor
  · show X.toBlocks₂₁ = 0
    ext a c
    show X (Sum.inr a) (Sum.inl c) = 0
    by_cases ha : a = Ald.i0 h
    · subst ha; rw [hr]; simp [Matrix.one_apply]
    by_cases hc : c = Ald.i0 h
    · subst hc; rw [hl']; simp [Matrix.one_apply]
    obtain ⟨a', rfl⟩ := (Ald.ne_last_iff_mem_range h a).1 ha
    obtain ⟨c', rfl⟩ := (Ald.ne_last_iff_mem_range h c).1 hc
    have e := hsub (Sum.inr a') (Sum.inl c')
    simp only [Sum.map_inr, Sum.map_inl] at e
    rw [e]
    exact congrFun (congrFun hp a') c'
  · rw [det_last h X.toBlocks₁₁ (fun c => by
      show X (Sum.inl (Ald.i0 h)) (Sum.inl c) = _
      rw [hl]; by_cases hc : c = Ald.i0 h
      · subst hc; simp
      · simp [Matrix.one_apply, hc, Ne.symm hc])]
    congr 1
    ext a c
    have e := hsub (Sum.inl a) (Sum.inl c)
    simp only [Sum.map_inl] at e
    exact e
theorem val_pull_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (hb : IsFrame2 σ Y b) :
    ∀ (p : G2 σ Y) (t : GL (Fin n) (AE F E)), IsPar p t → ∀ k ∈ d.K.comap j,
      (d.a ∘ j) (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
  intro p t hpt k hk
  obtain ⟨hpf, hdet⟩ := par_to hb hpt
  obtain ⟨hbig, hdet2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.jpar_k h hJ hpf
  obtain ⟨t', ht', hdt'⟩ := par_of d.ok.frame hbig
  show d.a (j (p * k)) = _
  rw [map_mul, d.ok.hgt.val (j p) t' ht' (j k) hk]
  congr 2
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdt', hdet2, hdet]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbUnit
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocUnit
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem UpperTheory.TP.K.exists_locUnit {B : Base F E} (hB : UpperTheory.TP.W.GoodK σ B) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl (F := F)) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      sigR (Fv F v) σ (u : Fv F v ⊗[F] E) = -(u : Fv F v ⊗[F] E) :=
  _root_.UpperTheory.Reformulated.B.Gs6.exists_locUnit hB hξ hσξ v

end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_skewUnit_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    ∃ r : (AE F E)ˣ, cA σ (r : AE F E) = -(r : AE F E) ∧
      (∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v) ∧
      ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1 := by
  classical
  have hc := hB.cm
  obtain ⟨ξ, hξ, hσξ⟩ := UnitA.exists_xi hc
  obtain ⟨S, hS⟩ := UnitA.exists_S (F := F) ξ
  choose u hu1 hu2 hu3 using _root_.UpperTheory.TP.K.exists_locUnit hB hξ hσξ
  let xv : ∀ v : Pl F, (Fv F v ⊗[F] E)ˣ := fun v =>
    ⟨inclR (F := F) (Fv F v) ξ, inclR (F := F) (Fv F v) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let b : ∀ v : Pl F, GL (Fin 1) (Fv F v ⊗[F] E) := fun v => if v ∈ S then sc1 (u v * (xv v)⁻¹) else 1
  have hb : ∀ v ∉ S, b v = 1 := fun v hv => if_neg hv
  let e : ∀ w : InfinitePlace F, w.Completion ⊗[F] E ≃+* ℂ := fun w =>
    RingEquiv.ofBijective (infEmb (B.emb w)) (infEmb_bijective hc (B.emb w))
  have hτ : ∀ w : InfinitePlace F, (B.emb w).1 ξ ≠ 0 := fun w => (map_ne_zero _).2 hξ
  let c : ∀ w : InfinitePlace F, GL (Fin 1) (w.Completion ⊗[F] E) := fun w =>
    sc1 (Units.map (e w).symm.toMonoidHom (Units.mk0 (Complex.I / (B.emb w).1 ξ) (div_ne_zero Complex.I_ne_zero (hτ w))))
  obtain ⟨γ, hγf, hγi⟩ := Frames.exists_GL_of_components S b hb c
  let X : (AE F E)ˣ := ⟨inclR (F := F) (AF F) ξ, inclR (F := F) (AF F) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let r : (AE F E)ˣ := Matrix.GeneralLinearGroup.det γ * X
  have hf : ∀ v, Units.map (compFin F E v).toMonoidHom r = if v ∈ S then u v else xv v := by
    intro v
    have hX : Units.map (compFin F E v).toMonoidHom X = xv v := Units.ext (UnitA.compFin_inclR v ξ)
    rw [map_mul, map_det_bc, hγf v, hX]
    by_cases hv : v ∈ S
    · simp only [b, if_pos hv, det_sc1, inv_mul_cancel_right]
    · simp only [b, if_neg hv, map_one, one_mul]
  have hfv : ∀ v, compFin F E v (r : AE F E) = ((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v]; rfl
  have hfi : ∀ v, compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) =
      (((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v, ← map_inv]; rfl
  have hi : ∀ w, infEmb (B.emb w) (compInf F E w (r : AE F E)) = Complex.I := by
    intro w
    have hX : Units.map (compInf F E w).toMonoidHom X = Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) :=
      Units.ext (UnitA.compInf_inclR w ξ)
    have h1 : Units.map (compInf F E w).toMonoidHom r = Matrix.GeneralLinearGroup.det (c w) *
        Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) := by
      rw [map_mul, map_det_bc, hγi w, hX]
    have h2 : compInf F E w (r : AE F E) = (e w).symm (Complex.I / (B.emb w).1 ξ) * inclR (F := F) w.Completion ξ := by
      have := congrArg Units.val h1
      simpa [c, det_sc1] using this
    rw [h2, map_mul]
    have h3 : infEmb (B.emb w) ((e w).symm (Complex.I / (B.emb w).1 ξ)) = Complex.I / (B.emb w).1 ξ :=
      (e w).apply_symm_apply _
    have h4 : infEmb (B.emb w) (inclR (F := F) w.Completion ξ) = (B.emb w).1 ξ := by
      change infEmb (B.emb w) ((1 : w.Completion) ⊗ₜ[F] ξ) = _
      rw [infEmb_tmul, map_one, one_mul]
    rw [h3, h4, div_mul_cancel₀ _ (hτ w)]
  refine ⟨r, ?_, fun v => ?_, fun w => ?_⟩
  ·
    have key : -(cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      refine GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) (fun v => ?_)
      · have hz : sigR w.Completion σ (compInf F E w (r : AE F E)) = -compInf F E w (r : AE F E) := by
          apply (e w).injective
          change infEmb (B.emb w) _ = infEmb (B.emb w) _
          rw [← infEmb_sigR hc, hi w, map_neg, hi w, Complex.conj_I]
        have hu : compInf F E w (r : AE F E) * compInf F E w ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compInf_cA, hz, neg_mul, neg_neg, hu]
      · have hz : sigR (Fv F v) σ (compFin F E v (r : AE F E)) = -compFin F E v (r : AE F E) := by
          rw [hfv v]
          by_cases hv : v ∈ S
          · simp only [if_pos hv]; exact hu3 v
          · simp only [if_neg hv, xv]
            rw [UnitA.sigR_inclR, hσξ, map_neg]
        have hu : compFin F E v (r : AE F E) * compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compFin_cA, hz, neg_mul, neg_neg, hu]
    have : cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) = -1 := by
      rw [← neg_neg (cA σ (r : AE F E) * _), key]
    calc cA σ (r : AE F E) = cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) * (r : AE F E) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = -(r : AE F E) := by rw [this, neg_one_mul]
  · rw [hfv v, hfi v]
    by_cases hv : v ∈ S
    · simp only [if_pos hv]; exact ⟨hu1 v, hu2 v⟩
    · simp only [if_neg hv]; exact hS v hv
  · change ‖infEmb (B.emb w) (compInf F E w (r : AE F E))‖ = 1
    rw [hi w, Complex.norm_I]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hn hs hb hJ
  have hB := d.ok.good
  have hσ : ∀ z, σ (σ z) = z := UnitA.sig_sig hB.cm
  refine ⟨fun x => ?_, _root_.PositivityTheory.SiegelWeilFormula.Ldexb.val_pull_k h hJ hb⟩
  obtain ⟨Y₀, b₀, K₀, a₀, hb₀, he₀, hK₀, ha₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_standard_hermitian_space hB hn
  obtain ⟨ε, he⟩ := hb.1
  have hK : IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j) := _root_.PositivityTheory.SiegelWeilFormula.Ald.kStd_k F E σ d n h Y b j hb hJ
  rcases hs with ⟨-, hY⟩ | ⟨-, hY⟩
  ·
    have hε : ε = -1 := eps_neg_unit (eps_neg hn hσ hY he)
    subst hε
    obtain ⟨r, hr, hrf, hri⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.exists_skewUnit_k hB
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ r ?_ hrf hri hK₀ ha₀.iwa hK x
    rw [hr]; push_cast; ring
  ·
    have hε : ε = 1 := eps_unit (eps_one hn hσ hY he)
    subst hε
    refine iwa_transport (B := d.B) hσ hb hb₀ he he₀ 1 ?_ (fun v => ?_) (fun w => ?_) hK₀ ha₀.iwa hK x
    · simp
    · simp only [Units.val_one, inv_one, map_one]; exact ⟨one_mem _, one_mem _⟩
    · simp
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.hgtPull_k
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldYF
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
open PositivityTheory.SiegelWeilFormula.Ald.YFA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem yFrame_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := _root_.GlobalTheory.T.exists_trace_zero_element F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldJ
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.JHomValK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def jHom_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) :
    G2 σ Y →* GL (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (MulAut.conj (bA d.b)).toMonoidHom.comp ((blkGL h).comp
    ((MulAut.conj (bA (F := F) b)⁻¹).toMonoidHom.comp (UG (cA σ) (dbl (incM F Y.J))).subtype))
theorem jHom_val_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 = incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype,
    Units.val_mul, bA_val, bA_inv_val, blkGL, Units.coe_map, blkHom, MonoidHom.coe_mk, OneHom.coe_mk, inFrame_eq]
theorem jHom_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (e1 : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε) (e2 : b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) (g : G2 σ Y) :
    _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  have hG1 : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = incM F (jeps d.n ε) := by
    rw [← e1, ← incM_gram, incM_dbl]; rfl
  have hG2 : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ).toRingHom = incM F (jeps n ε) := by
    rw [← e2, ← incM_gram, incM_dbl]; rfl
  have hg : (g.1.1)ᵀ * dbl (incM F Y.J) * (g.1.1).map (cA σ).toRingHom = dbl (incM F Y.J) := g.2
  have hM := (unitary_conj_iff (cA σ).toRingHom _ _ _ _ g.1.1 (incM_mul_inv b) (incM_inv_mul b) hG2).1 hg
  rw [← inFrame_eq] at hM
  show (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1.map (cA σ).toRingHom = dbl (incM F d.Y.J)
  rw [unitary_conj_iff (cA σ).toRingHom _ _ _ _ _ (incM_mul_inv d.b) (incM_inv_mul d.b) hG1, _root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
  have eQP : incM F (d.b⁻¹).1 * (incM F d.b.1 * blk h (inFrame b g) 1 * incM F (d.b⁻¹).1) * incM F d.b.1 =
      blk h (inFrame b g) 1 := by
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  rw [eQP, incM_jeps, jepsR_blk h, ← incM_jeps, ← incM_jeps, blk_transpose, blk_map _ _ _ _ (map_zero _), blk_mul,
    blk_mul, hM]
  congr 1
  simp [Matrix.map_one _ (map_zero _) (map_one _)]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem jEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b).codRestrict _ (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_mem_k d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 * incM F d.b.1 = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem ldEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.ldEx_of_leaves_k _root_.PositivityTheory.SiegelWeilFormula.Ald.yFrame_k _root_.PositivityTheory.SiegelWeilFormula.Ald.jEx_k _root_.PositivityTheory.SiegelWeilFormula.Ald.kStd_k _root_.PositivityTheory.SiegelWeilFormula.Ald.hgtPull_k _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_k
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitMain
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
theorem tUnit_k : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k := by
  intro F E _ _ _ _ _ σ d ν hν x Φ hΦ Φ' hΦ'
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.T_chart_k d
  have hpres : ∀ φ ∈ schA F d.κ, d.om x φ ∈ schA F d.κ := fun φ hφ => d.ok.dbl.weil.2.1.pres x φ hφ
  have hunit := d.ok.dbl.weil.2.1.unit
  obtain ⟨hμ, hint⟩ := _root_.PositivityTheory.SiegelWeilFormula.KTunit.map_haar_k d τ ν hν
  set μ := ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) with hμdef
  have h1 : ∀ Ψ ∈ d.sch, ∀ Ψ' ∈ d.sch, ∫ X, d.T Ψ X * star (d.T Ψ' X) ∂ν =
      (C * star C) * ∫ y, S0 Ψ y * star (S0 Ψ' y) ∂μ := by
    intro Ψ hΨ Ψ' hΨ'
    rw [← integral_const_mul, ← hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hT _ hΨ, hT _ hΨ', star_mul']
    change _ = C * star C * (S0 Ψ (fun k => d.crd X (τ k)) * star (S0 Ψ' fun k => d.crd X (τ k)))
    ring
  rw [h1 _ (hpres Φ hΦ) _ (hpres Φ' hΦ'), h1 _ hΦ _ hΦ']
  congr 1
  obtain ⟨c, hc0, hctop, hcn⟩ := hop.norm μ μ hμ hμ
  have hp' : ∀ φ ∈ schA F d.κ, (S0 ∘ₗ d.om x ∘ₗ S0') φ ∈ schA F d.κ := fun φ hφ =>
    hop.pres _ (hpres _ (hop.pres' φ hφ))
  have hT' : ∀ φ ∈ schA F d.κ, ∫⁻ y, ‖(S0 ∘ₗ d.om x ∘ₗ S0') φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
    intro φ hφ
    have e1 := hcn _ (hpres _ (hop.pres' φ hφ))
    have e2 := hcn _ (hop.pres' φ hφ)
    rw [hop.right φ hφ] at e2
    have e3 := hunit μ hμ x _ (hop.pres' φ hφ)
    simp only [LinearMap.comp_apply]
    rw [e1, e2, e3]
  have := GlobalTheory.DblUnitaryBox.integral_mul_star_eq μ hμ (S0 ∘ₗ d.om x ∘ₗ S0') hp' hT' (hop.pres Φ hΦ) (hop.pres Φ' hΦ')
  simpa only [LinearMap.comp_apply, hop.left _ hΦ, hop.left _ hΦ'] using this
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwuMain
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.TowU
namespace PositivityTheory.SiegelWeilFormula.TW.Twu
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit
theorem uniq_k : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k := by
  classical
  intro F E _ _ _ _ _ σ d ν hν Λ hΛ hinv
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.T_chart_k d
  by_cases hC : C = 0
  · refine ⟨0, fun Φ hΦ => ?_⟩
    have h0 : d.T Φ = 0 := funext fun X => by rw [hT Φ hΦ X, hC, zero_mul]; rfl
    rw [(_root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij F E σ d).2.2 Φ hΦ h0, map_zero, zero_mul]
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  letI : MeasurableSpace (d.κ → AF F) := borel _
  obtain ⟨hμ, hint⟩ := _root_.PositivityTheory.SiegelWeilFormula.KTunit.map_haar_k d τ ν hν
  obtain ⟨c, hc⟩ := translation_invariant_functional_haar d.B.ψ hψ d.κ (ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)) hμ (Λ ∘ₗ S0') (hop.adm' Λ hΛ) (by
    intro a φ hφ
    have e0 := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ a)
    have ea : (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ a) (τ k)) = a := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_cinv_k d τ a
    rw [ea] at e0
    rw [← schr_zero_right, ← e0, LinearMap.comp_apply, LinearMap.comp_apply, rhoS' _ φ hφ]
    exact hinv _ _ (hop.pres' φ hφ))
  refine ⟨c / C, fun Φ hΦ => ?_⟩
  have h1 := hc (S0 Φ) (hop.pres Φ hΦ)
  rw [LinearMap.comp_apply, hop.left Φ hΦ] at h1
  rw [h1, ← hint]
  have e2 : ∫ Z, d.T Φ Z ∂ν = C * ∫ Z, S0 Φ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ Z) ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Z => hT Φ hΦ Z)
  rw [e2]
  field_simp
end PositivityTheory.SiegelWeilFormula.TW.Twu
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvUpTo
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem w_cols_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) *
      Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (X Z : Mx F E d.m d.n) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k) : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw1, hBx, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    all_goals rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hr := l_rho_om h w (X * (incM F d.b.1.toCols₂)ᵀ) (Φ := Φ) hΦ
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) =
    d.l (d.om w (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ) Φ)) at hr
  rw [hr, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(_root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvThetaW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isW_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
theorem thetaW_k : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d w (_root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tWeyl_of_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k :=
  _root_.PositivityTheory.SiegelWeilFormula.TW.tWeyl_of_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k (_root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.upTo_of_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twu.uniq_k) hP _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.thetaW_k
theorem siegelWeilStd_pre_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_mid_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
    (_root_.PositivityTheory.SiegelWeilFormula.KFP.kFinPoly_of_k hT _root_.PositivityTheory.SiegelWeilFormula.Tunit.tUnit_k _root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT))
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.ldEx_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds) hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end
