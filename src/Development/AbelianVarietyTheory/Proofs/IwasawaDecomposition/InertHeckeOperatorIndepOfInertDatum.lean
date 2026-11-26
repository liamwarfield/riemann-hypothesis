module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Formalism.LocalToGlobal.Columns.MtHeckeSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem indepDatum_memGU_iff (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : GL (Fin n) K) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ Formalism.UG.GU σ' n ↔ M ∈ Formalism.UG.GU σ n := by
  show Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) = Formalism.UG.antiJ K n ↔
    Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K) =
      Formalism.UG.antiJ K n
  have e : Formalism.UG.cT σ' (((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K)) * Formalism.UG.antiJ K n *
      ((M : Matrix (Fin n) (Fin n) K)).map (g : K →+* K) =
      (Formalism.UG.cT σ (M : Matrix (Fin n) (Fin n) K) * Formalism.UG.antiJ K n * (M : Matrix (Fin n) (Fin n) K)).map
        (g : K →+* K) := by
    rw [Matrix.map_mul, Matrix.map_mul, antiJ_map, cT_map (g : K →+* K) σ σ' hg]
  rw [e]
  constructor
  · intro h
    exact Matrix.map_injective g.injective (h.trans (antiJ_map (g : K →+* K) n).symm)
  · intro h
    rw [h, antiJ_map]

theorem indepDatum_intRange (g : K ≃+* K) (hint : ∀ x, x ∈ Formalism.UG.intL K → g x ∈ Formalism.UG.intL K) {n : ℕ}
    (M : GL (Fin n) K) (hM : M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range) :
    Formalism.UG.bc (n := Fin n) (g : K →+* K) M ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL K).subtype).range := by
  obtain ⟨p, rfl⟩ := hM
  refine ⟨Formalism.UG.bc (n := Fin n) ((g : K →+* K).restrict (Formalism.UG.intL K) (Formalism.UG.intL K)
    (fun x hx => hint x hx)) p, ?_⟩
  ext i j
  rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem indepDatum_bc_e (Dv Dv' : InertDatum L n v w)
    (Y : GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))) :
    Formalism.UG.bc (n := Fin n) (Dv'.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
              w.adicCompletion L) Y =
      Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
        w.adicCompletion L →+* w.adicCompletion L)
        (Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+*
          w.adicCompletion L) Y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (gEquiv_e Dv Dv' _).symm

def indepDatumK (Dv Dv' : InertDatum L n v w) : GL (Fin n) (w.adicCompletion L) :=
  (Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) Dv.P)⁻¹ * Dv'.P

theorem indepDatum_loc (Dv Dv' : InertDatum L n v w) (x : GAf L n) :
    Dv'.loc x = (indepDatumK Dv Dv')⁻¹ * Formalism.UG.bc (n := Fin n) ((gEquiv Dv Dv' :
      w.adicCompletion L ≃+* w.adicCompletion L) : w.adicCompletion L →+* w.adicCompletion L) (Dv.loc x) *
        indepDatumK Dv Dv' := by
  simp only [InertDatum.loc, indepDatumK, map_mul, map_inv, indepDatum_bc_e Dv Dv']
  group

theorem indepDatumK_memGU (Dv Dv' : InertDatum L n v w) : indepDatumK Dv Dv' ∈ Formalism.UG.GU Dv'.σw n := by
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Formalism.UG.bc (n := Fin n) g Dv.P :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQdef
  set Qi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (((Formalism.UG.bc (n := Fin n) g Dv.P)⁻¹ :
    GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) with hQidef
  have hQ : Formalism.UG.cT Dv'.σw Q * Q = Formalism.UG.antiJ (w.adicCompletion L) n := by
    have hmap : Q = (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)).map g := rfl
    rw [hmap, cT_map g Dv.σw Dv'.σw (gEquiv_comm Dv Dv'), ← Matrix.map_mul, Dv.Panti, antiJ_map]
  have h1 : Q * Qi = 1 := by rw [hQdef, hQidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q = 1 := by rw [← Formalism.UG.cT_mul, h1, Formalism.UG.cT_one]
  show Formalism.UG.cT Dv'.σw (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [← hQ, Formalism.UG.cT_mul]
  calc Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * Formalism.UG.cT Dv'.σw Qi *
        (Formalism.UG.cT Dv'.σw Q * Q) * (Qi * (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)))
      = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Formalism.UG.cT Dv'.σw Qi * Formalism.UG.cT Dv'.σw Q) * (Q * Qi) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv'.σw (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
          (Dv'.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = Formalism.UG.cT Dv'.σw Q * Q := by rw [Dv'.Panti, hQ]

theorem indepDatumK_memKU (Dv Dv' : InertDatum L n v w) :
    (⟨indepDatumK Dv Dv', indepDatumK_memGU Dv Dv'⟩ : Formalism.UG.GU Dv'.σw n) ∈ Formalism.UG.KU Dv'.σw n := by
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨indepDatumK_memGU Dv Dv', ?_⟩
  obtain ⟨p1, hp1⟩ := indepDatum_intRange (gEquiv Dv Dv') (fun x hx => (gEquiv_intL Dv Dv' x).1 hx) _ Dv.Pint
  obtain ⟨p2, hp2⟩ := Dv'.Pint
  refine ⟨p1⁻¹ * p2, ?_⟩
  rw [map_mul, map_inv, hp1, hp2]
  rfl

theorem indepDatum_hval (Dv Dv' : InertDatum L n v w) (h' : Formalism.UG.GU Dv'.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv'.σw n) h') (x : GAf L n) :
    Dv'.hval h' (Dv'.loc x) =
      Dv.hval (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) (Dv.loc x) := by
  have hk := indepDatumK_memGU Dv Dv'
  have hloc := indepDatum_loc Dv Dv' x
  set g : w.adicCompletion L →+* w.adicCompletion L := ((gEquiv Dv Dv' : w.adicCompletion L ≃+* w.adicCompletion L) :
    w.adicCompletion L →+* w.adicCompletion L) with hgdef
  unfold InertDatum.hval
  by_cases hy : Dv.loc x ∈ Formalism.UG.GU Dv.σw n
  · have hgy : Formalism.UG.bc (n := Fin n) g (Dv.loc x) ∈ Formalism.UG.GU Dv'.σw n :=
      (indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') _).2 hy
    have hy' : Dv'.loc x ∈ Formalism.UG.GU Dv'.σw n := by
      rw [hloc]; exact mul_mem (mul_mem (inv_mem hk) hgy) hk
    rw [dite_eq_left hy', dite_eq_left hy]
    have hb := hbi (⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩ : Formalism.UG.KU Dv'.σw n)⁻¹
      ⟨⟨indepDatumK Dv Dv', hk⟩, indepDatumK_memKU Dv Dv'⟩
      (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n ⟨Dv.loc x, hy⟩)
    refine Eq.trans (congrArg h' ?_) hb
    apply Subtype.ext
    change Dv'.loc x = _
    rw [hloc]
    rfl
  · have hy' : Dv'.loc x ∉ Formalism.UG.GU Dv'.σw n := by
      intro h
      apply hy
      rw [← indepDatum_memGU_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv')]
      have he : Formalism.UG.bc (n := Fin n) g (Dv.loc x) =
          indepDatumK Dv Dv' * Dv'.loc x * (indepDatumK Dv Dv')⁻¹ := by
        rw [hloc]; group
      rw [he]
      exact mul_mem (mul_mem hk h) (inv_mem hk)
    rw [dite_eq_right hy', dite_eq_right hy]

theorem heckeFunI_indepDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W]
    (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W,
    heckeFunI L n U Dv' h' f =
      heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  intro L _ _ _ n v w Dv Dv' U W _ _ h' hbi f
  funext g
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
  · rw [dite_eq_left hc, dite_eq_left hc, indepDatum_hval Dv Dv' h' hbi]
  · rw [dite_eq_right hc, dite_eq_right hc]

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv Dv' : InertDatum L n v w) (U : Subgroup (GAf L n)) (W : Type) [AddCommGroup W] [Module ℂ W] (h' : GU Dv'.σw n → ℂ), IsBiInv (KU Dv'.σw n) h' → ∀ f : GAf L n → W, heckeFunI L n U Dv' h' f = heckeFunI L n U Dv (fun y => h' (guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') n y)) f := by
  first | exact @GlobalTheory.SatInd.heckeFunI_indepDatum | exact GlobalTheory.SatInd.heckeFunI_indepDatum | (intros; apply GlobalTheory.SatInd.heckeFunI_indepDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem val_mul_nsmul {Q ι : Type} [AddCommGroup Q] [Fintype ι] {g : ℕ} [NeZero g] (β : Q) (hβ : g • β = 0)
    (x y : ι → ZMod g) : (∑ i, x i * y i).val • β = ∑ i, (x i).val • (y i).val • β := by
  have h1 : (∑ i, x i * y i) = ((∑ i, (x i).val * (y i).val : ℕ) : ZMod g) := by
    push_cast
    simp
  rw [h1, ZMod.val_natCast]
  have h2 : ∀ n : ℕ, (n % g) • β = n • β := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n g, add_nsmul, mul_comm, mul_nsmul', hβ, nsmul_zero, add_zero]
  rw [h2, ← Finset.sum_nsmul_assoc]
  simp [mul_smul]

theorem basisChange_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] (f : Q →+ Q)
    (β υ : ι → Q) (hβ : ∀ i, g • β i = 0) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j = ∑ i, (P i j).val • β i) (hf : ∀ i, f (β i) = ∑ j, (M j i).val • β j) (j : ι) :
    f (υ j) = ∑ m, (N m j).val • υ m := by
  have e1 : f (υ j) = ∑ l, ((M * P) l j).val • β l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hυ, map_sum]
    simp only [map_nsmul, hf, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e1, ← hPN]
  simp only [hυ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem basisChange_mod {V ι : Type} [AddCommGroup V] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g]
    (W : AddSubgroup V) (f : V →+ V) (hW : ∀ v ∈ W, f v ∈ W)
    (β υ : ι → V) (hβ : ∀ i, g • β i ∈ W) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j - ∑ i, (P i j).val • β i ∈ W) (hf : ∀ i, f (β i) - ∑ j, (M j i).val • β j ∈ W) (j : ι) :
    f (υ j) - ∑ m, (N m j).val • υ m ∈ W := by
  have key : ∀ a b : V, a - b ∈ W ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have h := basisChange_quot (QuotientAddGroup.map W W f (fun v hv => hW v hv))
    (fun i => QuotientAddGroup.mk' W (β i)) (fun i => QuotientAddGroup.mk' W (υ i))
    (fun i => by rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; exact hβ i)
    M P N hPN
    (fun j => by
      have := (key _ _).1 (hυ j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]; simp only [map_nsmul])
    (fun i => by
      have := (key _ _).1 (hf i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_nsmul] at this
      rw [← this]; rfl) j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

variable {D : D7} (X : HidaSetting D)

theorem inclE_smul_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E)
    (ha : ∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • y ∈ wLf X w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    have hm : (a : X.B.I.E) • l ∈ wLat X w := Submodule.subset_span ⟨a, ha, l, hl, rfl⟩
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • l) i) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem fmat_mulVec_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    {y : VA X.B.I} (hy : y ∈ wLf X w) : X.B.I.fmat k *ᵥ y ∈ wLf X w := by
  have hz : ∀ z ∈ wLat X w, ∀ c : 𝓞 X.B.I.E, X.B.I.fmat k *ᵥ incl X.B.I (c • z) ∈ wLf X w := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hz
      intro c
      have e : incl X.B.I (c • (a : X.B.I.E) • l) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • incl X.B.I (c • l) := by
        rw [smul_comm]
        funext i
        exact map_mul (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (a : X.B.I.E) ((c • l) i)
      rw [e, Matrix.mulVec_smul]
      refine inclE_smul_mem_wLf X w a ha ((hk _).1 ?_)
      exact Submodule.subset_span ⟨⟨_, X.B.I.L.smul_mem c hl⟩, rfl⟩
    | zero =>
      intro c
      have e : incl X.B.I (c • (0 : Fin X.B.I.n → X.B.I.E)) = 0 := by
        rw [smul_zero]; funext i; simp [incl]
      rw [e, Matrix.mulVec_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      intro c
      have e : incl X.B.I (c • (a + b)) = incl X.B.I (c • a) + incl X.B.I (c • b) := by
        rw [smul_add]; funext i; simp only [incl, Pi.add_apply, map_add (f := _)]
      rw [e, Matrix.mulVec_add]; exact add_mem (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_smul]; exact ha _
  induction hy using Submodule.span_induction with
  | mem z h =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := h
    have := hz l hl 1
    rw [one_smul] at this
    exact this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : X.B.I.fmat k *ᵥ (c • a) = c • (X.B.I.fmat k *ᵥ a) :=
      Matrix.mulVec_smul _ (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) a
    rw [e]; exact Submodule.smul_mem _ c ha

theorem isMatIn_basisChange : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  intro D X red b hf kv hg P u hu k hk j
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have h := basisChange_mod (g := D.host.g kv.1) (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
    (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
    (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
    (fun i => incl X.B.I (b kv i)) u
    (fun i => by
      have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
        ⟨_, hg, by simp⟩ (y := incl X.B.I (b kv i)) (Submodule.subset_span ⟨⟨_, (hf kv).1.1 i⟩, rfl⟩)
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
          ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
        simp [map_natCast]
      rw [e, Nat.cast_smul_eq_nsmul] at h1
      exact h1)
    ((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _) (P : Matrix _ _ _)
    (((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _)
    (by rw [← Units.val_mul, ← Units.val_mul]; congr 1; group)
    (fun j => by
      have := hu j
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this)
    (fun i => by
      have := (hf kv).2 k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this) j
  simp only [Nat.cast_smul_eq_nsmul]
  exact h

end GlobalTheory.Mem.SymFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixModPlace_basisChange_eq_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_basisChange | exact GlobalTheory.Mem.SymFrame.isMatIn_basisChange | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_basisChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInRat

variable {D : D7}

theorem toGf_injective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : Function.Injective (toGf P) := by
  intro a b h
  have h1 : finHom V (P.ψ a) = finHom V (P.ψ b) := congrArg Subtype.val h
  have h2 : Formalism.IndefR.Lev.finE V (P.ψ a) = Formalism.IndefR.Lev.finE V (P.ψ b) := by
    simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, h1]
  rw [hU, hU] at h2
  exact Subtype.ext h2

theorem toGf_surjective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Function.Surjective (toGf P) := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  obtain ⟨h, hh⟩ := P.onto k k1
  refine ⟨h, Subtype.ext ?_⟩
  show finHom V (P.ψ h) = finHom V x
  rw [hh, k2]

theorem af_nontrivial : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField (maximalRealSubfield D.host.E))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := ⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (ReciprocityTheory.Aut.evalAt D.host.E v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem inclL_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) := by
  haveI := af_nontrivial (D := D)
  haveI : Nontrivial (ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap (maximalRealSubfield D.host.E) (ReciprocityTheory.Aut.AFplus D.host.E)).injective
  exact (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E).injective

theorem inclA_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

def glL (n : ℕ) : GL (Fin n) D.host.E →* GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) :=
  Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom

theorem glL_injective (n : ℕ) : Function.Injective (glL (D := D) n) := fun a b h =>
  Units.ext (Matrix.map_injective inclL_injective (congrArg Units.val h))

theorem glL_mem (n : ℕ) (x : GL (Fin n) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E n) :
    glL (D := D) n x ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  have h : (x : Matrix (Fin n) (Fin n) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  have h2 := congrArg (fun M => Matrix.map M
    (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  show (x : Matrix (Fin n) (Fin n) D.host.E).map _ * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
    ((x : Matrix (Fin n) (Fin n) D.host.E).map _) = 1
  rw [← h2]
  congr 1

def toStd (n : ℕ) : ReciprocityTheory.Aut.GQ0 D.host.E n →* ReciprocityTheory.Aut.GQ D.host.E n where
  toFun x := ⟨⟨glL (D := D) n x.1, glL_mem n x.1 x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext1; ext1; exact map_one _
  map_mul' a b := by ext1; ext1; exact map_mul _ _ _

theorem toStd_bij (n : ℕ) : Function.Bijective (toStd (D := D) n) := by
  refine ⟨fun a b h => Subtype.ext (glL_injective n (congrArg (fun y => y.1.1) h)), fun γ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩

section V

variable {V : HSp D}

theorem cT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) M := rfl

theorem mem_UJ (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h : (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  show Formalism.UG.cT _ (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x = V.gram
  rw [hV, Matrix.mul_one, cT_eq]
  exact mul_eq_one_comm.1 h

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E)
    (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  rw [hV, Matrix.mul_one, cT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_HR (x : GL (Fin V.rank) D.host.E) (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  have h2 := GlobalTheory.UnitarySplit.map_cond (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (sigR (AF D.host.F) D.sp.cm.sig) (fun y => rfl) V.gram x.1
  rw [h] at h2
  exact h2.symm

def toV (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ0 D.host.E V.rank →* Formalism.L2.Theta.GQ V where
  toFun x := ⟨⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x.1, mem_HR x.1 (mem_UJ hV x.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 ⟨x.1, mem_UJ hV x.1 x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_mul _ _ _

theorem toV_bij (hV : V.gram = 1) : Function.Bijective (toV hV) := by
  refine ⟨fun a b h => Subtype.ext (Units.ext (Matrix.map_injective inclA_injective
    (congrArg (fun y : Formalism.L2.Theta.GQ V => Units.val (y.1 : HR (AF D.host.F) D.sp.cm.sig V.gram).1) h))), fun δ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 δ.2)
  exact ⟨⟨x, mem_rationalGL_of_unitaryGroupGram_unitGram hV x hx⟩, Subtype.ext (Subtype.ext he)⟩

def ratE (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V :=
  (MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm.trans (MulEquiv.ofBijective (toV hV) (toV_bij hV))

theorem ratE_toStd (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    ratE hV (toStd (D := D) V.rank x) = toV hV x :=
  congrArg (toV hV) ((MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm_apply_apply x)

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem finHom_eq_of_finE {g h : GA D V} (e : Formalism.IndefR.Lev.finE V g = Formalism.IndefR.Lev.finE V h) :
    finHom V g = finHom V h :=
  Units.ext (Matrix.map_injective swapAE_injective (congrArg Units.val e))

theorem finE_toV (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    Formalism.IndefR.Lev.finE V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) =
      km D V.rank (toStd (D := D) V.rank x).1 := by
  apply Units.ext
  ext i j
  show swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (x.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
  simp [Algebra.TensorProduct.map_tmul, swapAE, glL]
  rfl

theorem ratIso_ratE (hV : V.gram = 1) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : RatIso P (ratE hV) := by
  intro γ
  obtain ⟨x, rfl⟩ := (toStd_bij (D := D) V.rank).2 γ
  have hr := ratE_toStd hV x
  refine ⟨(congrArg (Bridge.ratF V) hr).trans (Subtype.ext ?_), fun γ₀ h => ?_⟩
  · exact finHom_eq_of_finE ((finE_toV hV x).trans (hU (toStd (D := D) V.rank x).1).symm)
  · have hx : x.1 = γ₀ := glL_injective V.rank (Units.ext h)
    have key : Bridge.IsRatMat V (toV hV x) γ₀ := by
      show Formalism.L2.Theta.matHom V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = Formalism.UG.bc (incA D) γ₀
      rw [← hx]
      rfl
    exact hr ▸ key

end V

theorem toGf_bij_ratIso : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank), V.gram = 1 → UnitFr P →
    Function.Bijective (toGf P) ∧ ∃ e, RatIso P e := by
  intro D V P hV hU
  exact ⟨⟨toGf_injective P hU, toGf_surjective P⟩, ratE hV, ratIso_ratE hV P hU⟩

end GlobalTheory.MtInRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TilQ

section ExtM

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A)

theorem extM_iC_iC (i j : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iC hN j) = g i j := by
  simp [TilX.extM, Br.iC]

theorem extM_iC_iL (i : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iL hN) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iC (j : Fin n) : TilX.extM hN g (Br.iL hN) (Br.iC hN j) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iL : TilX.extM hN g (Br.iL hN) (Br.iL hN) = 1 := by
  simp [TilX.extM, Br.iL]

end ExtM

section Single

variable {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1)

theorem prH_single_iC (j : Fin n) : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iC hN j) 1) = Pi.single j 1 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (fun e => h (Br.iC_inj hN e)), Pi.single_eq_of_ne h]

theorem prH_single_iL : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iL hN) 1) = 0 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply, Pi.single_eq_of_ne]
  · rfl
  · intro e
    have := congrArg Fin.val e
    simp [Br.iC, Br.iL] at this
    omega

end Single

theorem adAt_of_bc_one {B : Base} {n : ℕ} {k : GA B n} (P : HeightOneSpectrum (𝓞 B.host.E))
    (hk : bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) k = 1) (i j : Fin n) :
    adAt B.host.F P (k.1 i j) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion B.host.E)) i j := by
  have h2 : prV (E := B.host.E) (P.under (𝓞 B.host.F))
      (k.1 i j - (1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin n) _ => g.1 i j) hk
    simp only [Units.val_one] at h3
    have h4 : prV (E := B.host.E) (P.under (𝓞 B.host.F)) (k.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := TilX.adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp


set_option maxHeartbeats 1600000 in
theorem pt_tilF_gen : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  intro B X I hI hP l Z u a k t hk1 hk2 hk3 ht htP d g' g hg' hext
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  obtain ⟨p0, hp0, hN0⟩ := hk1
  have hPr := (base_fields_primes_ok B X).2.1
  have hN := N_m_succ B.R
  have hgw : ∀ w : (B.primes X).vGs, ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
    intro w
    have h1 : ∃ i, w.1 ∈ (B.primes X).vG i := by
      have h0 := w.2
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.1.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  have hpi1 : ∀ w : (B.primes X).vGs, (B.primes X).piT u - 1 ∈ w.1.asIdeal := by
    intro w
    obtain ⟨i, hi⟩ := hgw w
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    rw [hc]
    refine w.1.asIdeal.mul_mem_right _ ?_
    have hd : (B.primes X).g i ∣ (B.primes X).cond * ((B.primes X).g 0 * (B.primes X).g 1) ^ 2 := by
      refine dvd_mul_of_dvd_right (dvd_pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨c', hc'⟩ := hd
    rw [hc']
    push_cast
    exact w.1.asIdeal.mul_mem_right _ hi
  have hTw : ∀ w : (B.primes X).vGs, (B.T u : 𝓞 B.host.F) ∉ (w.1.under (𝓞 B.host.F)).asIdeal := by
    intro w hT
    obtain ⟨i, hi⟩ := hgw w
    have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.1.asIdeal := hT
      rw [map_natCast] at h2
      exact h2
    have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
      (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
    have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
      have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
          (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [← hab]; push_cast; ring
      have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
      rw [e', e]
      exact add_mem (w.1.asIdeal.mul_mem_left _ h1) (w.1.asIdeal.mul_mem_left _ hi)
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hkw : ∀ (w : (B.primes X).vGs) (i j : Fin (B.R.N B.R.m)),
      adAt B.host.F w.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j) = (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (w.1.adicCompletion B.host.E)) i j := by
    intro w i j
    refine adAt_of_bc_one w.1 ?_ i j
    rw [map_inv, hk2 _ (hTw w), inv_one]
  have hA := TilX.isPtOf_tilFr (hc := B.sp.cm) (ST := (B.primes X).vT u) hN (conj_piT_notMem hPr u) hpi1
    (hg'.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)) hp0.uni
    (by have := hp0.lat; rwa [hN0] at this) hkw hk3
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ht
  have hB := (isPtOf_mul_J0 B.host.F B.host.E B.sp.cm _ ((B.primes X).vT u) (B.primes X).vGs ∅ _ m.1 _
    (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)) 1).2.1 rfl hA m.2 (by rw [inv_one]; exact hm)
  obtain ⟨-, -, hiX, -⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have hgext : g = TilX.extGL hN g' := by
    refine Units.ext (TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
      (TilX.iXm_apply hiX hN) hext.1 ?_)
    have h2 := hext.2
    have hz : z0 X u = Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) := TilX.lastCoordinateUniformizerVector_eq_single u
    rw [hz] at h2
    exact h2
  have hQ := PerLaw.piT_notMem_Q hI u a
  have hQ0 : ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))), (B.primes X).piT u ∉ P.1.asIdeal := fun P => isEmptyElim P
  have e : (tilF I.sel (I.tup a) u d).deco =
      (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)).deco := by
    rw [tilF_deco I.sel (I.tup a) hPr u hQ d, tilFr_deco hN (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) hQ0, extTo_deco]
  rw [show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG (E := B.fields.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) ×
    GLQ B.fields.E (B.R.N B.R.m) ∅) = 1 from rfl, one_smul] at hB
  rw [hgext, ← mul_assoc]
  refine ⟨hB.uni, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact hB.lat
  · rw [e]; exact hB.f
  · rw [e]; exact hB.be
  · intro P i j
    have hTq : (B.T u : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
      intro hT
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.1.asIdeal := hT
      rw [map_natCast] at h2
      exact T_notMem_QE I.sel (I.tup a) u hPr hI.sel_ok (hI.T_mem u) P.1 P.2 h2
    have hkP := adAt_of_bc_one P.1 (hk2 _ hTq)
    have e1 : adAt B.host.F P.1 (((TilX.extGL hN g' * k * (J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m :
        GA B (B.R.N B.R.m)) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) i j) =
        adAt B.host.F P.1 (TilX.extM hN g'.1 i j) *
          adAt B.host.F P.1 ((((J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m : GA B (B.R.N B.R.m)) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) j j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j, map_mul, hkP, Matrix.one_apply_eq, mul_one]
          · rfl
          · intro l _ hl
            rw [map_mul, hkP, Matrix.one_apply_ne hl, mul_zero]
          · simp
      · intro l _ hl
        rw [map_mul, htP P l j, if_neg hl, map_zero, mul_zero]
      · simp
    rw [e1, htP P j j, if_pos rfl, tilF_fr I.sel (I.tup a) hPr u hQ d P]
    rcases GlobalTheory.TopStep.idx_cases hN i with ⟨i', rfl⟩ | rfl <;> rcases GlobalTheory.TopStep.idx_cases hN j with ⟨j', rfl⟩ | rfl
    · have h1 : ¬ ((Br.iC hN j').1 + 1 = B.R.N B.R.m) := by
        show ¬ (j'.1 + 1 = B.R.N B.R.m)
        have := j'.2
        omega
      rw [if_neg h1, map_one, mul_one, extM_iC_iC, hg'.fr P i' j']
      congr 1
      exact ((congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) _ (Pi.single (Br.iC hN j') 1)) i').trans
        (by rw [prH_single_iC])).symm
    · have h0 := (congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) (unitOf ((B.primes X).piT u)) (Pi.single (Br.iL hN) 1)) i').trans
        (by rw [prH_single_iL, map_zero])
      rw [extM_iC_iL, map_zero, zero_mul]
      exact (congrArg (algebraMap B.host.E _) h0).trans (map_zero _) |>.symm
    · rw [extM_iL_iC, map_zero, zero_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_of_ne, mul_zero, map_zero]
      intro e
      have := congrArg Fin.val e
      simp [Br.iC, Br.iL] at this
      omega
    · have h1 : (Br.iL hN).1 + 1 = B.R.N B.R.m := by
        show (B.R.N B.R.m - 1) + 1 = B.R.N B.R.m
        omega
      rw [if_pos h1, extM_iL_iL, map_one, one_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_same, mul_one,
        unitOf_val (hQ P)]

end GlobalTheory.Mem.Col2.TilQ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMulStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointOverX_has_adelicPoint_blockExtend_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  first | exact @GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen | exact GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen | (intros; apply GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def conjSplit (s : SplitPlace L) : SplitPlace L := ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsLocMap {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (T : σ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
    T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

end

def twEig (w : HeightOneSpectrum (𝓞 L)) {n : ℕ} (α : Fin n → ℂˣ) : Multiset ℂ :=
  (Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * ((normV w : ℕ) : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))

end GlobalTheory.HeckeFrob

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.SplitEtaIdem

theorem exists_isIdemAt_conjP : ∀ {D : D7} (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb),
    ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) := by
  intro D Pb Ut
  apply GlobalTheory.MovedIdem.exists_isIdemAt
  rw [Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.conjPrime_conjPrime]
  intro h
  exact Ut.hπP (h ▸ Ut.hπ)

end GlobalTheory.SplitEtaIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrimeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime : ∀ {D : D7} (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb), ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) := by
  first | exact @GlobalTheory.SplitEtaIdem.exists_isIdemAt_conjP | exact GlobalTheory.SplitEtaIdem.exists_isIdemAt_conjP | (intros; apply GlobalTheory.SplitEtaIdem.exists_isIdemAt_conjP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDelta
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDelta
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem cHkT_eq_of_isFrob : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  intro D T i b P hP σ hσ
  have hA := D.nd.plOm.2 P
  have key : ∀ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ →
      T.delta i τ = T.delta i σ := by
    intro τ hτ
    have hmem := inv_mul_mem_Ine_of_isFrob hσ hτ
    have h1 : T.delta i (σ⁻¹ * τ) = 1 := by
      by_contra hne
      exact hP (T.primes_subset_exceptional i ((T.delta_ram i P _ hA).1 ⟨_, hmem, hne⟩))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  unfold cHkT
  rw [dite_eq_left ⟨σ, hσ⟩, key _ (Exists.choose_spec (⟨σ, hσ⟩ : ∃ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ))]

end GlobalTheory.HeightCounting.FormsStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDeltaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob | exact GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob | (intros; apply GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob <;> assumption)
end
end
