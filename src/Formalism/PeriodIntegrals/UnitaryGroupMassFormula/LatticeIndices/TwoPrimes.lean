module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem two_primes (h2 : Module.finrank F E = 2) (l : ℕ) [hl : Fact l.Prime]
    (hsplit : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    ∃ Q Q' : Ideal (𝓞 E), Q.IsMaximal ∧ Q'.IsMaximal ∧ Q ≠ Q' ∧ Q.LiesOver p.asIdeal ∧
      Q'.LiesOver p.asIdeal := by
  have := p.isMaximal
  have : Fintype (p.asIdeal.primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 E)
  have hrk : Module.finrank (𝓞 F) (𝓞 E) = 2 := (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm.trans h2
  rw [hrk] at hsum
  have hterm : ∀ q : p.asIdeal.primesOver (𝓞 E),
      (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) ≤ 1 := by
    intro q
    have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
    have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
    have hq0 : (q : Ideal (𝓞 E)) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _
    let w : HeightOneSpectrum (𝓞 E) := ⟨q, hqp, hq0⟩
    have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      have := (Ideal.mem_of_liesOver (q : Ideal (𝓞 E)) p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
      simpa using this
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one l hsplit w hw
    change (q : Ideal (𝓞 E)).ramificationIdx ℤ = 1 at he
    change (q : Ideal (𝓞 E)).inertiaDeg ℤ = 1 at hf
    have h1 := Ideal.ramificationIdx_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    have h2 := Ideal.inertiaDeg_above_le (R := ℤ) p.asIdeal (q : Ideal (𝓞 E))
    rw [he] at h1
    rw [hf] at h2
    calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
      _ = 1 := rfl
  have hcard : 2 ≤ Fintype.card (p.asIdeal.primesOver (𝓞 E)) := by
    calc 2 = ∑ q : p.asIdeal.primesOver (𝓞 E),
          (q : Ideal (𝓞 E)).ramificationIdx (𝓞 F) * (q : Ideal (𝓞 E)).inertiaDeg (𝓞 F) := hsum.symm
      _ ≤ ∑ _q : p.asIdeal.primesOver (𝓞 E), 1 := Finset.sum_le_sum fun q _ => hterm q
      _ = _ := by simp
  obtain ⟨q, q', hqq⟩ := Fintype.one_lt_card_iff.1
    (show 1 < Fintype.card (p.asIdeal.primesOver (𝓞 E)) by omega)
  have hqp : (q : Ideal (𝓞 E)).IsPrime := q.2.1
  have hqp' : (q' : Ideal (𝓞 E)).IsPrime := q'.2.1
  have hqo : (q : Ideal (𝓞 E)).LiesOver p.asIdeal := q.2.2
  have hqo' : (q' : Ideal (𝓞 E)).LiesOver p.asIdeal := q'.2.2
  refine ⟨q, q', hqp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _),
    hqp'.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _), fun h => hqq (Subtype.ext h), hqo, hqo'⟩

end MassDataIdxEmb

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem embP_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : EmbP X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := (resArith_holds X p).2.1
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨Q, Q', hQ, hQ', hne, hQo, hQ'o⟩ :=
    MassDataIdxEmb.two_primes (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.deg2 (gOf p) hsplit p.1 hmem
  exact MassDataIdxEmb.emb_of_two X.B.I.cm.deg2 p.1 Q Q' hne

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def StAdaptB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (e : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))
      (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ ((Matrix.reindex e e (jm1 X.B.I.J θ))ᵀ *ᵥ
        (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm)) = l b • Pi.single (pf b) 1) ∧
      ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
        ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
          (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
            - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
          ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
            ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) * Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) * (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

theorem isUnit_det_split_form (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    IsUnit (jm1 X.B.I.J θ).det := by
  have h := (unit_JR X p).map (th1 X p θ)
  rw [RingHom.map_det] at h
  exact h

theorem stFrameB_of (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : StFrameB X u p := by
  obtain ⟨θ, hθ, e, Q, l, hl, hy1, hy2, K, hK, ψ, hψ, hker, hred⟩ := h
  refine ⟨K, hK, ψ, hψ, hker, 1, fun x => ?_⟩
  let g1 : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p) :=
    Q * glRed (algebraMap (Op X p) (FpX X p)) (ψ x) * Q⁻¹
  have hg1 : (g1 : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) := by
    simp only [g1, Units.val_mul, hred x, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hinj : Function.Injective (algebraMap (Op X p) (FpX X p)) := Subtype.val_injective
  rw [MassDataIdxStIm.mem_Ssub_iff_sG X.B.I.cm.sig X.B.I.J θ hθ e (isUnit_det_split_form X p θ) (frameOf X u) Q l hl
    hy1 hy2 (x : HAp X p) g1 hg1, inv_one, one_mul, mul_one,
    MassDataIdxStIm.mem_sG_iff_map _ hinj (ψ x)]
  simp only [g1, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem parabolic_image_of_adapted (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : ParabolicReductionImage X u p := parabolic_image_of_frame X u p (stFrameB_of X u p h)

end Loc

end MassDataIdxSteps
end
end
