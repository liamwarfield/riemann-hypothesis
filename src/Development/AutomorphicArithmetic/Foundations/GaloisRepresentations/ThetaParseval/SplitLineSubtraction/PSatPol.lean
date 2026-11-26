module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem satPol_val (q a : ℕ) (b : ℂˣ) (m : ℤ) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ)) ^ (-m) =
      ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ m * ((b : ℂ)⁻¹) ^ m := by
  have hx : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ = (q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [zpow_neg, ← inv_zpow, mul_inv, ← hx, mul_zpow]

theorem UpperTheory.Gal.TP.Sub.satPol_holds :
    SatPol := by
  intro E Ω _ _ _ _ _ A w h a B g
  rw [GlobalTheory.SatChar.charPol_satWD]
  unfold unrPol algSat
  simp only [bind, pure, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [satPol_val]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.twLoc_holds :
    TwLoc := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c
  have h := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => UpperTheory.V.Af.tw_val r c g)
  exact ⟨h.1, h.2.1⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.cpFacts_holds :
    CpFacts := by
  intro Γ k _ _ a b
  refine ⟨fun r s g => GlobalTheory.EigTwist.charpoly_sumRep r s g, ?_, ?_⟩
  · intro c g
    simp [cp, rk1, Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
  · rintro r r' ⟨u, hu⟩ g
    simp only [cp, hu, Units.val_mul]
    rw [Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj u (r g : Matrix (Fin a) (Fin a) k)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw tw_val)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem twJumps_holds : TwJumps := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c _ _ τ J m h1 h2
  exact (GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => tw_val r c g)).2.2.2 τ J m h1 h2

end UpperTheory.Gal.TP.Sub

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem cont_of_val {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (h : Continuous fun g => (r g : Matrix (Fin n) (Fin n) k)) : Continuous r := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((r g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun g => (r g : Matrix (Fin n) (Fin n) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  rw [e]
  exact h.comp continuous_inv

private theorem val_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k) := Units.continuous_val

private theorem sumRep_entry {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k)
    (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  have hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
  have hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j := finSumFinEquiv_symm_apply_castAdd j
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  rfl

theorem UpperTheory.Gal.TP.Sub.contLeft_holds :
    ContLeft := by
  intro Γ k _ _ _ _ _ _ a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hc
    apply cont_of_val r
    have hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) := val_cont.comp hc
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) :=
      (continuous_apply _).comp ((continuous_apply _).comp hm)
    refine he.congr fun g => ?_
    exact sumRep_entry r s g i j
  · rintro r r' ⟨u, hu⟩ hr
    have hf : (⇑r') = fun x => u * r x * u⁻¹ := funext hu
    rw [hf]
    exact (continuous_const.mul hr).mul continuous_const
  · intro r c hr hc
    apply cont_of_val
    have hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) = fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k) := by
      funext g
      exact UpperTheory.V.Af.tw_val r c g
    rw [hv]
    exact (Units.continuous_val.comp hc).smul (val_cont.comp hr)
  · intro c hc
    apply cont_of_val
    have hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) = fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k) := by
      funext g
      simp [rk1, Matrix.scalar_apply]
    rw [hv]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem scaleRoots_X_sub_C' (a d : ℂ) : (X - C a : ℂ[X]).scaleRoots d = X - C (a * d) := by
  rw [sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]

private theorem scaleRoots_unrPol (S : Multiset ℂ) (m : ℤ) (c : ℂ) :
    (unrPol S m).scaleRoots (c ^ (-m)) = unrPol (S.map (· * c)) m := by
  unfold unrPol
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih,
      scaleRoots_X_sub_C', mul_zpow]

theorem UpperTheory.Gal.TP.Sub.wDFacts_holds :
    WDFacts := by
  intro E Ω _ _ _ _ _ A w h x y
  induction x using WD.ind with | _ n a => ?_
  induction y using WD.ind with | _ m b => ?_
  refine ⟨?_, fun g => WD.charPol_lpSum _ _ g, ?_, ?_⟩
  · rw [WD.lpSum_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.sum]
    rintro ⟨hN, hρ⟩
    refine ⟨?_, fun σ => ?_⟩
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) hN
      simpa using hv
    · apply LinearMap.ext
      intro v
      have hv := congrArg (fun f => (f (v, 0)).1) (hρ σ)
      simpa [Representation.prod] using hv
  · rw [WD.lpChar_mk, WD.unr_mk, WD.unr_mk, WD.unr_mk]
    unfold WDRep.Unr
    simp only [WDRep.tensor]
    rintro ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], fun σ => ?_⟩
    rw [Representation.tprod_apply, ha' σ, hb' σ]
    simp
  · intro g S c hx hy
    rw [WD.charPol_mk] at hx hy
    rw [WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ]
    have hm : m = 1 := by
      have hd := congrArg Polynomial.natDegree hy
      rw [LinearMap.charpoly_natDegree] at hd
      unfold unrPol at hd
      simpa using hd
    subst hm
    have hb : b.ρ g = c ^ (-deg g) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
      have hct := LinearMap.aeval_self_charpoly (b.ρ g)
      rw [hy] at hct
      unfold unrPol at hct
      simp only [Multiset.map_singleton, Multiset.prod_singleton, map_sub, aeval_X, aeval_C] at hct
      rw [sub_eq_zero] at hct
      rw [hct, Algebra.algebraMap_eq_smul_one]
    have ht : c ^ (-deg g) ≠ 0 := by
      intro ht0
      have h0 : b.ρ g = 0 := by
        rw [hb, ht0, zero_smul]
      have h1 : b.ρ (g * g⁻¹) = 1 := by
        rw [mul_inv_cancel, map_one]
      rw [map_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    rw [hb, TensorProduct.map_smul_right, GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_smul_eq_scaleRoots _ ht,
      GlobalTheory.CompanionTheory.RelOpsLeaf.charpoly_map_one (by simp), hx, scaleRoots_unrPol]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharAbove
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charAbove_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.HeckeLAdicCharacterDeRham → GlobalTheory.Published.AlgebraicCharacterWD → PstOfDR → ContLeft → CharAbove := by
  intro H hD hW hP hC E Ω _ _ _ _ _ l _ ι art ha χ n μ h1 h2 h3 w hu P AI hT A h O _ _ _ Bw hj
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have d := hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj
  have hc : Continuous ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    ((hC (G E Ω) (Qbar l) 0 0).2.2.2 μ h2).comp continuous_subtype_val
  have hr := hP l P AI hT E Ω A O Bw 1 _ hc d.1
  have e := hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha'
  have hun := (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu
  refine ⟨?_, d.1, d.2, fun g => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, e, GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
    exact hun
  · have hv : (χ.loc w (a g) : ℂ) = ((χ.val w : ℂˣ) : ℂ) ^ (-deg g) := by
      have ho : GlobalTheory.SmGL.ord (w.adicCompletion E) (atFin w (unif w)) = 1 := by
        rw [GlobalTheory.SmGL.SphCompletion.ord_completion, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _ from unif_spec w]
        simp
      have h1 : ∀ x : (w.adicCompletion E)ˣ, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
        have h0 : GlobalTheory.SmGL.ord (w.adicCompletion E) (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 0 := by
          have hz : ∀ (y : (w.adicCompletion E)ˣ), GlobalTheory.SmGL.unrChar (w.adicCompletion E) (Units.mk0 2 two_ne_zero) y =
              (Units.mk0 (2:ℂ) two_ne_zero) ^ GlobalTheory.SmGL.ord _ y := fun _ => rfl
          let φ : (w.adicCompletion E)ˣ →* Multiplicative ℤ := MonoidHom.mk' (fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord _ y))
            fun y z => by rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
          have : φ (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow]
            simp [φ, ho, ← ofAdd_zsmul]
          exact this
        have := hun _ ((GlobalTheory.SmGL.ord_eq_zero_iff).1 h0)
        rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
        exact this
      rw [h1, ha'.ord_eq, Units.val_zpow_eq_zpow_val]
    rw [e, WD.charPol_eq_prod, GlobalTheory.LocLanglands.eig_lpOfChar]
    simp [unrPol, hv]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigSum
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem dg_mulVec {Γ k : Type} [Group Γ] [Field k] {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ)
    (u : Fin t → k) (i : Fin t) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec u i = (a i g : k) * u i := by
  simp [dg, Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.TP.Sub.eigSum_holds :
    EigSum := by
  intro Γ k _ _ m t r a c
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    let e : Fin t → k := Pi.single i 1
    let w : Fin (m + t) → k := fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e
    have hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0 := by
      funext y
      simp [w]
    have hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e := by
      funext y
      simp [w]
    refine ⟨w, ?_, ?_⟩
    · intro h
      have := congrFun hwr i
      rw [h] at this
      simp [e] at this
    · intro g
      funext x
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
      rcases y with y | y
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]
        have := congrFun hwl y
        simp only [Function.comp_apply] at this
        rw [this]
        simp
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]
        have := congrFun hwr y
        simp only [Function.comp_apply] at this
        rw [Pi.smul_apply, this, smul_eq_mul]
        by_cases hy : y = i
        · subst hy
          rw [hi]
        · simp [e, Pi.single_apply, hy]
  · intro hne hex
    obtain ⟨w, hw0, hw⟩ := hex
    rcases GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext hcon)
      apply hne j
      ext g
      have := congrFun (hv g) j
      rw [dg_mulVec, Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSplitLine
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

noncomputable section

namespace UpperTheory.Gal.TP.Sub

section SplitLineAux

variable {Γ k : Type} [Group Γ] [Field k] {m : ℕ}

private lemma sumRep_val (s : Γ →* GL (Fin m) k) (c : Γ →* kˣ) (g : Γ) :
    ((sumRep s (rk1 c) g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      (Matrix.fromBlocks (s g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private lemma rankOneRep_val (c : Γ →* kˣ) (g : Γ) (i j : Fin 1) :
    ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) i j = (c g : k) := by
  simp [rk1, Subsingleton.elim i j]

private def resHom (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (r (g * h) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k) =
      (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec
        ((r h : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') : Γ →* GL (Fin m) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix b b (resHom r hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }

private lemma subRep_val (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (g : Γ) :
    ((subRep r hinv b g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      LinearMap.toMatrix b b (resHom r hinv g) := rfl

private def colM {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    (v : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin m ⊕ Fin 1) k :=
  Matrix.of fun i => Sum.elim (fun j => (b j : Fin (m + 1) → k) i) (fun _ => v i)

private lemma intertw (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (c : Γ →* kˣ) (v : Fin (m + 1) → k)
    (hv : ∀ g, (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v = (c g : k) • v) (g : Γ) :
    (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v =
      colM b v * Matrix.fromBlocks (subRep r hinv b g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) := by
  ext i j
  rcases j with j | j
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inl j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i := rfl
    have h2 := b.sum_repr (resHom r hinv g (b j))
    have h4 : ((resHom r hinv g (b j) : W') : Fin (m + 1) → k) =
        (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k) := rfl
    have h3 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i =
        ∑ a, (b.repr (resHom r hinv g (b j))) a * (b a : Fin (m + 1) → k) i := by
      have h5 := congrArg (fun u : W' => (u : Fin (m + 1) → k) i) h2
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at h5
      rw [← h4, h5]
    rw [h1, h3, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [subRep_val, colM, LinearMap.toMatrix_apply, mul_comm]
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inr j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v) i := rfl
    rw [h1, hv g, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [colM, rankOneRep_val, mul_comm]

private lemma col_indep {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    {v : Fin (m + 1) → k} (hv0 : v ≠ 0) (hc : IsCompl (Submodule.span k {v}) W') :
    LinearIndependent k (Sum.elim (fun j => (b j : Fin (m + 1) → k)) (fun _ : Fin 1 => v)) := by
  refine LinearIndependent.sum_type
    (b.linearIndependent.map' W'.subtype (Submodule.ker_subtype W'))
    (LinearIndependent.of_subsingleton (0 : Fin 1) hv0) ?_
  refine Disjoint.mono ?_ ?_ hc.disjoint.symm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  · rw [Set.range_const]

end SplitLineAux

end UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.splitLine_holds : SplitLine := by
  intro Γ k _ _ m r hss c ⟨v, hv0, hv⟩
  have hW : IsInv r (Submodule.span k {v}) := by
    intro g x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Matrix.mulVec_smul, hv g, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  obtain ⟨W', hinv, hc⟩ := hss _ hW
  have hfr : Module.finrank k W' = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_span_singleton hv0, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin m) k W' := Module.finBasisOfFinrankEq k W' hfr
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) k := (colM b v).submatrix id finSumFinEquiv.symm
  have hQ : IsUnit Q := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have := (col_indep b hv0 hc).comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    convert this using 1
    ext j i
    rcases h : finSumFinEquiv.symm j with j' | j' <;> simp [Q, colM, Matrix.col, h]
  obtain ⟨q, hq⟩ := hQ
  refine ⟨subRep r hinv b, q⁻¹, fun g => ?_⟩
  have key : (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * Q =
      Q * (sumRep (subRep r hinv b) (rk1 c) g : GL (Fin (m + 1)) k) := by
    rw [sumRep_val]
    change _ * (colM b v).submatrix id finSumFinEquiv.symm =
      (colM b v).submatrix id finSumFinEquiv.symm * _
    rw [Matrix.submatrix_mul_equiv, ← intertw r hinv b c v hv g]
    ext i j
    rfl
  have key2 : r g * q = q * sumRep (subRep r hinv b) (rk1 c) g := Units.ext (by
    simpa [hq] using key)
  rw [inv_inv, mul_assoc, key2, ← mul_assoc, inv_mul_cancel, one_mul]
end
end
