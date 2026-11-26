module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.SmGL.SphCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem valuation_le_one_iff_adicValuation_le_one (x : v.adicCompletion F) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    (valuation (v.adicCompletion F)) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  have : Valuation.Compatible
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one

private theorem residueFieldCard_adicCompletion_lemma :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = _root_.Formalism.UG.qV F v := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hmem : ∀ x : v.adicCompletion F,
      x ∈ 𝒪[v.adicCompletion F] ↔ x ∈ v.adicCompletionIntegers F := fun x => by
    simpa [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers] using
      valuation_le_one_iff_adicValuation_le_one v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x, (hmem x).1 x.2⟩
      invFun := fun x => ⟨x, (hmem x).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold _root_.GlobalTheory.SplitWeil.resCard
  rw [← _root_.Formalism.UG.P.tjcosets_card_residue v]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv

theorem _root_.GlobalTheory.SmGL.SphCompletion.ord_completion (x : (v.adicCompletion F)ˣ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SmGL.ord (v.adicCompletion F) x =
      -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have h := _root_.GlobalTheory.LGrp.BorelCompletion.nabs_completion v x
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow, residueFieldCard_adicCompletion_lemma] at h
  have hq : (1 : ℝ) < _root_.Formalism.UG.qV F v := by
    rw [← residueFieldCard_adicCompletion_lemma v]
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard _
  have := zpow_right_injective₀ (by linarith) hq.ne' h
  omega

theorem _root_.GlobalTheory.SmGL.SphCompletion.KO_completion (n : ℕ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) = _root_.Formalism.UG.GLint (Fin n) (_root_.Formalism.UG.Ov F v) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  haveI := _root_.Formalism.UG.P.tjcosets_isLocalRing v
  ext g
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, _root_.Formalism.UG.P.tjcosets_mem_K_iff]
  simp only [Valuation.mem_integer_iff, _root_.Formalism.UG.P.cartan_mem_Ov, valuation_le_one_iff_adicValuation_le_one]

private theorem natCast_zpow_neg_cpow_eq_cpow_mul (q : ℕ) (m : ℤ) (n : ℕ) (i : Fin n) :
    (((q : ℝ) ^ (-m) : ℝ) : ℂ) ^ ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      (q : ℂ) ^ (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      ((((n : ℝ) - 1 - 2 * (i : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) =
      (((-m : ℝ) * (((n : ℝ) - 1 - 2 * (i : ℝ)) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (zpow_nonneg hq _), ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hq, Real.rpow_mul hq, ← Real.rpow_intCast]
  push_cast
  rfl

theorem _root_.GlobalTheory.SmGL.SphCompletion.law_completion (n : ℕ) (α : Fin n → ℂˣ)
    (b : _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n)) (c : ℂ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    (_root_.GlobalTheory.SmGL.deltaHalf (v.adicCompletion F) (fun _ : Fin n => Unit)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
      ((_root_.GlobalTheory.SmGL.ofChar
          (_root_.GlobalTheory.SmGL.torusChar fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))).comp
        (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm.toMonoidHom)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) c =
      _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 * c := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  set t := _root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b with ht
  have hdet : ∀ i, ((Matrix.GeneralLinearGroup.det (t i) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = (b.1 : Matrix _ _ _) i i := by
    intro i
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact _root_.GlobalTheory.SmGL.leviProj_apply _ (_root_.GlobalTheory.SmGL.points (Fin n)) b i () ()
  have hsymm : ∀ i, (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm t i =
      Matrix.GeneralLinearGroup.det (t i) := fun i => rfl
  rw [_root_.GlobalTheory.SmGL.deltaHalf_apply]
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.ofChar_apply, smul_eq_mul,
    MulEquiv.coe_toMonoidHom, _root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.SmGL.unrChar_apply,
    hsymm, Units.coe_prod, _root_.GlobalTheory.SmGL.val_absPow]
  unfold _root_.Formalism.UG.chiDelta
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hord : _root_.GlobalTheory.SmGL.ord (v.adicCompletion F)
      (Matrix.GeneralLinearGroup.det (t i)) = _root_.Formalism.UG.ordV F v ((b.1 : Matrix _ _ _) i i) := by
    rw [_root_.GlobalTheory.SmGL.SphCompletion.ord_completion, _root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq, hdet]
  rw [_root_.GlobalTheory.SmGL.modExp_fin _ (fun _ => Fintype.card_unit),
    _root_.GlobalTheory.LGrp.nabs_eq_zpow, hord, residueFieldCard_adicCompletion_lemma, mul_comm]
  rw [Units.val_zpow_eq_zpow_val, natCast_zpow_neg_cpow_eq_cpow_mul]

theorem _root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (φ : GL (Fin n) k → ℂ) :
    (∃ f ∈ _root_.GlobalTheory.PRep.fixed (_root_.GlobalTheory.SmGL.prinSeries χ)
        (_root_.GlobalTheory.SplitWeil.KO k (Fin n)), f.1.1 = φ) ↔
      (∀ (b : _root_.GlobalTheory.SmGL.borel k (Fin n)) g, φ (b * g) =
        (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
              (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) (φ g)) ∧
      ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n), ∀ x, φ (x * g) = φ x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed] at hf
    refine ⟨fun b g => _root_.GlobalTheory.SmGL.parInd_law _ _ f b g, fun g hg x => ?_⟩
    have := congrArg (fun f' => f'.1.1 x) (hf g hg)
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x f).symm.trans this
  · rintro ⟨hlaw, hinv⟩
    let f₀ : _root_.GlobalTheory.PRep.indSpace (_root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points (Fin n)))
        ((_root_.GlobalTheory.SmGL.twist
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
            (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
          (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit))).comp
          (_root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points (Fin n)))) :=
      ⟨φ, fun b g => hlaw b g⟩
    have hfix : ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
        _root_.GlobalTheory.PRep.ind _ _ g f₀ = f₀ := fun g hg => by
      ext x
      exact hinv g hg x
    have hsm : f₀ ∈ _root_.GlobalTheory.PRep.smoothPart (_root_.GlobalTheory.PRep.ind _ _) := by
      apply _root_.GlobalTheory.SmGL.mem_smoothPart_of_nhds
      refine Filter.mem_of_superset
        (_root_.GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (_root_.GlobalTheory.SplitWeil.KO k (Fin n)).one_mem)
        fun g hg => hfix g hg
    refine ⟨⟨f₀, hsm⟩, ?_, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed]
    intro g hg
    ext x
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x _).trans (hinv g hg x)

theorem _root_.GlobalTheory.SmGL.SphCompletion.isSpherical_iff : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂˣ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ),
    letI := _root_.GlobalTheory.LocalData.complRel v; haveI := _root_.GlobalTheory.LocalData.isLocalField v;
    (_root_.Formalism.UG.IsSpherical F v (fun i => (α i : ℂ)) φ ↔
      ∃ f ∈ _root_.GlobalTheory.PRep.fixed
          (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))
          (_root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n)), f.1.1 = φ) := by
  intro F _ _ v n α φ
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hlaw := _root_.GlobalTheory.SmGL.SphCompletion.law_completion v n α
  have hone : _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) 1 = 1 := by
    unfold _root_.Formalism.UG.chiDelta
    simp [_root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq]
  have hborel : ∀ b : GL (Fin n) (v.adicCompletion F),
      _root_.Formalism.UG.IsUpperB F v b ↔ b ∈ _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n) := by
    intro b
    rw [_root_.GlobalTheory.SmGL.mem_borel]
    rfl
  rw [_root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff,
    _root_.GlobalTheory.SmGL.SphCompletion.KO_completion]
  unfold _root_.Formalism.UG.IsSpherical
  constructor
  · intro h
    refine ⟨fun b g => ?_, fun g hg x => ?_⟩
    · rw [hlaw b (φ g)]
      simpa only [mul_one] using h b g 1 ((hborel _).2 b.2) (one_mem _)
    · simpa only [one_mul, hone] using h 1 x g ((hborel 1).2 (one_mem _)) hg
  · rintro ⟨hL, hI⟩ b g k hb hk
    rw [hI k hk, ← hlaw ⟨b, (hborel b).1 hb⟩ (φ g)]
    exact hL ⟨b, (hborel b).1 hb⟩ g

end GlobalTheory.SmGL.SphCompletion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCharExp

theorem exists_zpow_of_trivial (ψ : ℂˣ →* Circle) (hc : Continuous ψ)
    (h : ∀ s : ℂˣ, starRingEnd ℂ (s : ℂ) = s → ψ (s * s) = 1) :
    ∃ k : ℤ, ∀ z : ℂˣ, ((ψ z : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by
  have hu : Continuous (Circle.toUnits : Circle →* ℂˣ) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact (continuous_subtype_val.comp (continuous_inv (G := Circle))).congr fun u => by simp [Function.comp, Circle.coe_inv]
  obtain ⟨k, hk⟩ := GlobalTheory.circle_hom_eq_zpow (ψ.comp Circle.toUnits) (hc.comp hu)
  refine ⟨k, fun z => ?_⟩
  have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  have h1 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs : ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  let u : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    simp [Submonoid.unitSphere, h0.ne']⟩
  have hu' : (u : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
  have e : z = Circle.toUnits u * (Units.mk0 _ hs * Units.mk0 _ hs) := by
    apply Units.ext
    show (z : ℂ) = (u : ℂ) * (((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ) * ((Real.sqrt ‖(z : ℂ)‖ : ℝ) : ℂ))
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0.le, hu', div_mul_cancel₀ _ h1]
  have e2 : ψ z = u ^ k := by
    rw [e, map_mul, h _ (Complex.conj_ofReal _), mul_one]
    exact hk u
  rw [e2, ← hu', Circle.coe_zpow]

variable {D : D7} {θ : InfFam D}

theorem ext_of_chart {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {a b : AE D}
    (h1 : finPart D a = finPart D b) (h2 : ∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) : a = b := by
  rw [← sub_eq_zero]
  refine h.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => ?_
  rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]

theorem exists_real_hom {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) :
    ∃ e : (D.what₂.Tau → ℂ) →* AE D, Continuous e ∧ (∀ z, finPart D (e z) = 1) ∧
      ∀ z τ, θ τ (infPart D (e z)) = z τ := by
  have a1 : ∀ z, finPart D (1 + σ (z - 1)) = 1 := fun z => by rw [RingHom.map_add (f := _), h.fin, add_zero, RingHom.map_one]
  have a2 : ∀ z τ, θ τ (infPart D (1 + σ (z - 1))) = z τ := fun z τ => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), h.comp, RingHom.map_one, RingHom.map_one]; simp
  refine ⟨{ toFun := fun z => 1 + σ (z - 1)
            map_one' := by rw [sub_self, σ.map_zero, add_zero]
            map_mul' := fun z w => ext_of_chart h (by rw [RingHom.map_mul, a1, a1, a1, mul_one]) fun τ => by
              rw [RingHom.map_mul, RingHom.map_mul, a2, a2, a2, Pi.mul_apply] }, ?_, a1, a2⟩
  exact continuous_const.add (h.cont.comp (continuous_id.sub continuous_const))

theorem map_sq_eq_one {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (y : (AE D)ˣ)
    (hy : cA D (y : AE D) = y) : χ (y * y) = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := hχ
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
  have e : idF D (GlobalTheory.VolHeckeCompare.normU D y) = y * y := by
    refine (hN y).trans (Units.ext ?_)
    show (y : AE D) * cA D (y : AE D) = (y : AE D) * y
    rw [hy]
  rw [← e, h η hη, hη.2.2.1 y, one_pow]

theorem exists_hasInfExp : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau),
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  intro D θ χ n τ hθ hχ hr
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, ec, e1, e2⟩ := exists_real_hom h
  let f : ℂ →* AE D := e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have fc : Continuous f := ec.comp (continuous_mulSingle (A := fun _ : D.what₂.Tau => ℂ) τ)
  have f1 : ∀ z, finPart D (f z) = 1 := fun z => e1 _
  have f2 : ∀ z τ', θ τ' (infPart D (f z)) = (Pi.mulSingle τ z : D.what₂.Tau → ℂ) τ' := fun z τ' => e2 _ τ'
  obtain ⟨k, hk⟩ := exists_zpow_of_trivial (χ.comp (Units.map f)) (hχ.1.comp (fc.units_map f)) fun s hs => by
    rw [MonoidHom.comp_apply, MonoidHom.map_mul]
    refine map_sq_eq_one hr _ (ext_of_chart h ?_ fun τ' => ?_)
    · have e3 : finPart D (cA D (f s)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (f s)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (f s)
      show finPart D (cA D (f s)) = finPart D (f s)
      rw [e3, f1, RingHom.map_one]
    · show θ τ' (infPart D (cA D (f s))) = θ τ' (infPart D (f s))
      rw [GlobalTheory.FockCompare.comp_cA hθ, f2]
      by_cases ht : τ' = τ
      · rw [ht, Pi.mulSingle_eq_same, hs]
      · rw [Pi.mulSingle_eq_of_ne ht, RingHom.map_one]
  refine ⟨(k : ℚ) / 2, k, by ring, ⟨θ, hθ⟩, fun θ' hθ' x x1 x2 => ?_⟩
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  let z : ℂˣ := Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  have hz : (z : ℂ) = θ τ (infPart D (x : AE D)) := rfl
  have ex : Units.map f z = x := by
    refine Units.ext (ext_of_chart h ((f1 z).trans x1.symm) fun τ' => (f2 z τ').trans ?_)
    by_cases ht : τ' = τ
    · rw [ht, Pi.mulSingle_eq_same, hz]
    · rw [Pi.mulSingle_eq_of_ne ht, x2 τ' ht]
  have := hk z
  rwa [MonoidHom.comp_apply, ex, hz] at this

end GlobalTheory.SplitCharExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mult_value_left_cont_level :
    ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ, ∀ T ∈ Mult θ M J χ, ∀ v, (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ Continuous (T v) ∧ ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro D V S θ M J χ T hT v
  induction hT using Submodule.span_induction with
  | mem x hx =>
    exact ⟨(hx.aut v).left, (hx.aut v).cont, hx.lev v⟩
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_, fun k _ g => ?_⟩
    · simp
    · simp only [MultilinearMap.zero_apply]
      exact continuous_zero
    · simp
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · simpa only [MultilinearMap.add_apply] using hx.2.1.add hy.2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2.2 k hk g, hy.2.2 k hk g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun γ hγ g => ?_, ?_, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 γ hγ g]
    · simpa only [MultilinearMap.smul_apply] using hx.2.1.const_smul c
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2.2 k hk g]
      ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem comm_fin_real {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GinfC V) : a * b = b * a := by
  have h1 : (GfC V).Normal := MonoidHom.normal_ker _
  have h2 : (GinfC V).Normal := MonoidHom.normal_ker _
  exact Subgroup.commute_of_normal_of_disjoint (GfC V) (GinfC V) h1 h2
    (Subgroup.disjoint_def.2 fun {x} hx hy => GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hx hy) a b ha hb

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact (GinfC V).one_mem

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V :=
  atTau_mem θ V τ _

def rTrL (κ : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := LinearMap.funLeft ℂ ℂ fun g => g * κ

theorem rTrL_apply (κ : GA D V) (φ : GA D V → ℂ) : rTrL V κ φ = rTr V κ φ := rfl

variable {κ : GA D V}

theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, comm_fin_real V hκ (oneP_mem θ V τ X t)]

theorem RderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ φ) = rTr V κ (RderC θ V τ Z φ) := by
  unfold RderC
  rw [Rder_rTr θ V hκ, Rder_rTr θ V hκ]
  rfl

theorem foldr_comm {α : Type} (T : α → α) (l : List (α → α)) (hl : ∀ f ∈ l, ∀ x, f (T x) = T (f x)) (x : α) :
    l.foldr (fun f acc => f acc) (T x) = T (l.foldr (fun f acc => f acc) x) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons]
    rw [ih fun g hg => hl g (List.mem_cons_of_mem _ hg), hl f List.mem_cons_self]

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  unfold gelf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← rTrL_apply V κ (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [rTrL_apply]
  refine foldr_comm (rTr V κ) _ ?_ φ
  intro f hf x
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
  exact RderC_rTr θ V hκ τ _ x

theorem foldr_Rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih, Rder_rTr θ V hκ]

theorem isAutFun_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (rTr V κ φ) := by
  have := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const)⟩
  · simp only [rTr]
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, hinv⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GA D V => κ⁻¹ * k * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : κ⁻¹ * k * κ⁻¹⁻¹ ∈ U := hk
      have hf : κ⁻¹ * k * κ⁻¹⁻¹ ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hkf) ((GfC V).inv_mem ((GfC V).inv_mem hκ))
      simp only [rTr]
      rw [← hinv _ hk' hf (g * κ)]
      congr 1
      group

theorem isAutFunSm_rTr : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ,
    IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  intro D θ V κ hκ φ h
  refine ⟨isAutFun_rTr V hκ h.toIsAutFun, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · have e : (fun t : Fin k → ℝ => rTr V κ φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) =
        fun t : Fin k → ℝ => φ (g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
      funext t
      have hm : (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
        refine (GinfC V).list_prod_mem fun x hx => ?_
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
        exact oneP_mem θ V _ _ _
      simp only [rTr]
      rw [mul_assoc, mul_assoc, comm_fin_real V hκ hm]
    rw [e]
    exact h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφ, hst⟩ := h.zfin
    refine ⟨W.map (rTrL V κ), inferInstance, ⟨φ, hφ, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨gelf θ V τ k f, hst τ k f hf, (gelf_rTr θ V hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_rTr θ V hκ]
    simp only [rTr]
    rw [mul_assoc, ← comm_fin_real V hκ hg, ← mul_assoc]
    exact hC g hg

end GlobalTheory.FinTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  first | exact @GlobalTheory.FinTranslate.isAutFunSm_rTr | exact GlobalTheory.FinTranslate.isAutFunSm_rTr | (intros; apply GlobalTheory.FinTranslate.isAutFunSm_rTr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_rat_left_and_eigen_right : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f) ∧ ∀ k k' (c : ℂ), om (k, k') f = c • f → ∀ g h, thetaKO om (g * k) (h * k') f = c * thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  refine ⟨fun γ hγ γ' hγ' g h => ?_, fun k k' c hc g h => ?_⟩
  ·

    have hprod : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres (g, h) f hf)
  ·
    have hprod : ((g * k, h * k') : GA D S × GA D T) = (g, h) * (k, k') := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply, hc, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_continuous_and_rat_invariant : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → Continuous (fun p : GA D S × GA D T => thetaKO om p.1 p.2 f) ∧ ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f := by
  intro D ψ S T χS χT om H f hf
  refine ⟨H.om_cont f hf 0, ?_⟩
  intro γ hγ γ' hγ' g h
  have h1 : om (γ * g, γ' * h) = om (γ, γ') * om (g, h) := by
    rw [← map_mul]; rfl
  unfold thetaKO
  rw [h1]
  exact H.om_aut γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem fundamentalDomain_setIntegral_mul_right :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ k : G, Measure.map (fun g => g * k) μ = μ → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ → IntegrableOn (fun g => f (g * k)) 𝓕 μ ∧ ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  intro G _ _ _ _ Γ _ μ _ 𝓕 h𝓕 k hk f hf hi
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h𝓕.integrableOn_iff h2 hinv]
    exact (hmp.integrableOn_comp_preimage hemb).2 hi
  · rw [h𝓕.setIntegral_eq h2 hinv]
    exact hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApproxAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspApproxCompact

theorem isCuspFun_of_approx (D : D7) (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (ha : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ : GA D V → ℂ, Continuous ψ ∧
      (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧ ∀ h ∈ C, ‖f h - ψ h‖ < δ) :
    IsCuspFun V f := by
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g := by
    have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    exact continuous_subtype_val.mul continuous_const
  have hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K) :=
    hK.image hcont
  have h1 := hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g
  have hfin : μ 𝓕 < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have hM0 : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕 := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψl, hψcusp, hψ⟩ := ha _ hC δ hδ
    have h0 := (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g
    have hfi := hint f hf hl W hW μ hμ 𝓕 h𝓕 g
    have hψi := hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢
    have e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ := by
      rw [integral_sub hfi hψi, h0, sub_zero]
    rw [e]
    refine norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc n
    have hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V := by
      rw [GlobalTheory.AutFunCompare.GQ_eq]
      exact Subgroup.mem_subgroupOf.1 hγ
    have ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) =
        f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) -
          ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']
    rw [ee]
    exact (hψ _ ⟨_, hk, rfl⟩).le
  by_contra hne
  have hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ := norm_pos_iff.2 hne
  have := key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

end GlobalTheory.CuspApproxCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfForallApprox
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLocApprox

theorem integral_eq_zero_of_forall_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {v : X → ℂ} {w : X → ℝ}
    (hw : Integrable w μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ u : X → ℂ, Integrable u μ ∧ ∫ x, u x ∂μ = 0 ∧ ∀ x, ‖u x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  by_cases hv : Integrable v μ
  swap
  · exact integral_undef hv
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨u, hu, h0, hn⟩ := h ε hε
    have e : ∫ x, (u x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub hu hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

variable {D : D7} {V : HSp D}

def LocApprox (V : HSp D) (f : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (ψ : Fin n → GA D V → ℂ),
    (∀ l, Continuous (ψ l) ∧ (∀ γ ∈ GQ V, ∀ g, ψ l (γ * g) = ψ l g) ∧ IsCuspFun V (ψ l)) ∧
    ∀ x ∈ C, ‖f x - ∑ l, ψ l x‖ < ε

theorem leftInv_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := by
  intro γ hγ g
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, ψ, hψ, happ⟩ := h {γ * g, g} (Set.toFinite _).isCompact (ε / 2) (by positivity)
  have e : ∑ l, ψ l (γ * g) = ∑ l, ψ l g := Finset.sum_congr rfl fun l _ => (hψ l).2.1 γ hγ g
  have h1 := happ (γ * g) (by simp)
  have h2 := happ g (by simp)
  rw [dist_eq_norm]
  have e' : f (γ * g) - f g = (f (γ * g) - ∑ l, ψ l (γ * g)) - (f g - ∑ l, ψ l g) := by rw [e]; ring
  rw [e']
  linarith [norm_sub_le (f (γ * g) - ∑ l, ψ l (γ * g)) (f g - ∑ l, ψ l g)]

theorem isCuspFun_of_locApprox {f : GA D V → ℂ} (h : LocApprox V f) : IsCuspFun V f := by
  have hl := leftInv_of_locApprox h
  rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) →
      IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl'
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl' μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g :=
    continuous_subtype_val.mul continuous_const
  have hw : Integrable (fun _ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (1 : ℝ)) (μ.restrict 𝓕) := by
    simpa using (hint (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl).norm
  refine integral_eq_zero_of_forall_approx (μ := μ.restrict 𝓕) (v := fun n => f (n.1 * g)) hw fun ε hε => ?_
  obtain ⟨m, ψ, hψ, happ⟩ := h _ (hK.image hcont) ε hε
  refine ⟨fun n => ∑ l, ψ l (n.1 * g), integrable_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1, ?_,
    fun n => ?_⟩
  · rw [integral_finsetSum _ fun l _ => hint _ (hψ l).1 (hψ l).2.1]
    exact Finset.sum_eq_zero fun l _ =>
      (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ l).2.2 W hW μ hμ 𝓕 h𝓕 g
  · obtain ⟨γ, hγ, hk⟩ := hKs n
    have e1 : f (n.1 * g) = f ((γ * n).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl _ hγ _).symm
    have e2 : ∀ l, ψ l (n.1 * g) = ψ l ((γ * n).1 * g) := fun l => by
      have hl' := (hψ l).2.1
      rw [GlobalTheory.AutFunCompare.GQ_eq] at hl'
      rw [Subgroup.coe_mul, mul_assoc]; exact (hl' _ hγ _).symm
    show ‖∑ l, ψ l (n.1 * g) - f (n.1 * g)‖ ≤ ε * 1
    rw [e1, Finset.sum_congr rfl fun l _ => e2 l, mul_one, norm_sub_rev]
    exact (happ _ ⟨_, hk, rfl⟩).le

end GlobalTheory.CuspLocApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem norm_residueChar_eq_one {E : Type} [Field E] [NumberField E] (PP : Pl E) (f : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ) :
    ‖((f x : ℂˣ) : ℂ)‖ = 1 := by

  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hpow : ((f x : ℂˣ) : ℂ) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow hx.orderOf_pos.ne'

theorem norm_levChi_flagL_eq_one :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
      ∀ κ ∈ levG V β (flagL L), ‖levChi V β (flagL L) κ‖ = 1 := by
  intro D V β L κ _

  have hP : ∀ x, ext1 (flagL L).P.H (flagL L).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs
    · rfl
    · rfl

  rw [levChi, levFn, hP, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod,
    norm_prod, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  refine ⟨(GfC V).mul_mem hκ.1 hκ'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hκ.2.1 hκ'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ.2.1 hκ'.2.1, hκ.2.2, hκ'.2.2]

theorem levChi_flag_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ.2.1 hκ'.2.1, Units.val_mul]

theorem levChi_flag1 (κ : GA D V) : levChi V β (flag1L L) κ = levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_flag1]

theorem isLift_one_of_mem {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) : IsLevelLift V β L 1 κ := by
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  have h : Formalism.L2.DIV.rTup β L (finE V κ) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)) := hκ.2.2
  exact Subgroup.mem_bot.mp h

theorem act_one {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : actG0 V β L 1 F = F := by
  have h1 : (1 : GA D V) ∈ levG V β (flag1L L) := Subgroup.one_mem _
  have hl := isLift_one_of_mem h1
  funext h
  rw [level_action_spec hF ⟨1, hl⟩ 1 hl h, hF 1 h1 h, levChi_flag1]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) 1
  field_simp

theorem act_hasType {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) : HasType V β (flag1L L) (actG0 V β L g F) := by
  intro k hk h
  obtain ⟨κ, hκ⟩ := hex
  have hl := isLift_one_of_mem hk
  have hkκ : IsLevelLift V β L g (k * κ) := by simpa using isLift_mul hl hκ
  rw [level_action_spec hF ⟨κ, hκ⟩ κ hκ (h * k), level_action_spec hF ⟨κ, hκ⟩ (k * κ) hkκ h, levChi_flag_mul hl hκ,
    levChi_flag1, mul_assoc h k κ]
  have := levChi_ne_zero (V := V) (β := β) (flagL L) k
  have := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  field_simp

theorem act_mul {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {g g' : G0 L.Pg L.r}
    (hex : ∃ κ, IsLevelLift V β L g κ) (hex' : ∃ κ, IsLevelLift V β L g' κ) :
    actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  obtain ⟨κ, hκ⟩ := hex
  obtain ⟨κ', hκ'⟩ := hex'
  have hm := isLift_mul hκ hκ'
  funext h
  rw [level_action_spec hF ⟨_, hm⟩ _ hm h, level_action_spec (act_hasType hF ⟨κ', hκ'⟩) ⟨κ, hκ⟩ κ hκ h,
    level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (h * κ), levChi_flag_mul hκ hκ', mul_assoc h κ κ', mul_inv, mul_assoc]

theorem levelGroupAction_isAction : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), LiftsExist V β L → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (actG0 V β L 1 F = F ∧ ∀ g, HasType V β (flag1L L) (actG0 V β L g F)) ∧ ∀ g g', actG0 V β L (g * g') F = actG0 V β L g (actG0 V β L g' F) := by
  intro D V β L hL F hF
  exact ⟨⟨act_one hF, fun g => act_hasType hF (hL g)⟩, fun g g' => act_mul hF (hL g) (hL g')⟩

end GlobalTheory.FlagAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasType_of_mem_mult : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), ∀ T ∈ Mult θ M (levG V β L : Set (GA D V)) (levChi V β L), ∀ v, HasType V β L (T v) := by
  intro D V S θ M β L T hT v
  induction hT using Submodule.span_induction generalizing v with
  | mem x hx => exact fun κ hκ h => hx.lev v κ hκ h
  | zero => intro κ _ h; simp
  | add x y _ _ hx hy =>
    intro κ hκ h
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hx v κ hκ h, hy v κ hκ h, mul_add]
  | smul a x _ hx =>
    intro κ hκ h
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hx v κ hκ h, mul_left_comm]

end GlobalTheory
end
