module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfTrX
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IotaAlgInj
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DVIsDiffVal
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem dV_isDiffVal : IsDiffVal v (dV v) := by
  have h : ∃ d, IsDiffVal v d := diffExists v
  unfold dV
  rw [dite_eq_left h]
  exact h.choose_spec

theorem val_pow_le (k : ℕ) (x : 𝓞 F) (hx : x ∈ differentIdeal ℤ (𝓞 F) ^ k) :
    Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v (dV v) ^ k := by
  have hint : ∀ y : 𝓞 F, Valued.v (algebraMap F (Fv F v) (y : F)) ≤ 1 := by
    intro y
    have e := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v y
    have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := F) v y
    exact e.le.trans hle
  induction k generalizing x with
  | zero =>
    rw [pow_zero]
    exact hint x
  | succ k ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 := (dV_isDiffVal v).2.1 a ha
      have h2 := ih b hb
      rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul, pow_succ']
      exact mul_le_mul' h1 h2
    · rw [show ((a + b : 𝓞 F) : F) = (a : F) + (b : F) from rfl, map_add (f := _)]
      exact Valuation.map_add_le _ ha hb

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def OmVDdTr : Prop :=
  ∀ d : 𝓞 D.host.F, d ∈ differentIdeal ℤ (𝓞 D.host.F) ↔
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)

theorem iota_alg_inj : Function.Injective (fun x : X.B.I.F => X.ιE (algebraMap X.B.I.F X.B.I.E x)) :=
  X.ιE.injective.comp (algebraMap X.B.I.F X.B.I.E).injective

theorem pre_int (d : 𝓞 D.host.F) : ∃ x : 𝓞 X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  obtain ⟨a, ha⟩ := (X.ιE_F ((d : D.host.F) : D.host.E)).1 (d : D.host.F).2
  set f : X.B.I.F →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E) with hf
  have hd : IsIntegral ℤ (((d : D.host.F) : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe d).map ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom
  have ha' : f a = ((d : D.host.F) : D.host.E) := ha
  rw [← ha'] at hd
  have hai : IsIntegral ℤ a := (isIntegral_algHom_iff f.toIntAlgHom (iota_alg_inj X)).1 hd
  exact ⟨⟨a, (mem_integralClosure_iff ℤ _).2 hai⟩, ha⟩

theorem pow_tr (hT : OmVDdTr X) (k : ℕ) (d : 𝓞 D.host.F) (hd : d ∈ differentIdeal ℤ (𝓞 D.host.F) ^ k) :
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ k ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  induction k generalizing d with
  | zero =>
    obtain ⟨x, hx⟩ := pre_int X d
    exact ⟨x, by simp, hx⟩
  | succ k ih =>
    rw [pow_succ'] at hd
    refine Submodule.mul_induction_on
      (C := fun d : 𝓞 D.host.F => ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ (k + 1) ∧
        X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)) hd ?_ ?_
    · intro a ha b hb
      obtain ⟨x1, hx1, e1⟩ := (hT a).1 ha
      obtain ⟨x2, hx2, e2⟩ := ih b hb
      refine ⟨x1 * x2, by rw [pow_succ']; exact Submodule.mul_mem_mul hx1 hx2, ?_⟩
      have : ((x1 * x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) * (x2 : X.B.I.F) := rfl
      rw [this, map_mul, map_mul, e1, e2]; rfl
    · rintro a b ⟨x1, hx1, e1⟩ ⟨x2, hx2, e2⟩
      refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, ?_⟩
      have : ((x1 + x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) + (x2 : X.B.I.F) := rfl
      rw [this, map_add (f := _), map_add (f := _), e1, e2]; rfl

def Qi (v : PlX X) (c : Fv X.B.I.F v) : Ideal (𝓞 D.host.E) where
  carrier := {i | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (i : D.host.E)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((0 : 𝓞 D.host.E) : D.host.E)) ∈
      OEv (E := X.B.I.E) v
    simp only [map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro i j hi hj
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((i : D.host.E) + (j : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_add (f := _), map_add (f := _), mul_add]; exact Submodule.add_mem _ hi hj
  smul_mem' := by
    intro o i hi
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((o : D.host.E) * (i : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hi

theorem alg_int_mem (v : PlX X) (c : Fv X.B.I.F v) (hc : Valued.v c ≤ 1) :
    algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c ∈ OEv (E := X.B.I.E) v := by
  have e : algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c =
      (⟨c, hc⟩ : v.adicCompletionIntegers X.B.I.F) • (1 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e]; exact Submodule.smul_mem _ _ (one_mem_oev v)

theorem ddS_pow (k : ℕ) : ddS D ^ k = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (differentIdeal ℤ (𝓞 D.host.F) ^ k) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [Ideal.map_pow, FractionalIdeal.coeIdeal_pow]; rfl

theorem dd1 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ ddS D ^ k) :
    sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  rw [ddS_pow, FractionalIdeal.mem_coeIdeal] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F) ^ k) ≤
      Qi X v ((dV v)⁻¹ ^ k) := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    obtain ⟨x, hx, ex⟩ := pow_tr X hT k d hd
    show sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (X.ιE.symm ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E)) ∈ OEv (E := X.B.I.E) v
    have e1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E) = ((d : D.host.F) : D.host.E) := rfl
    rw [e1, ← ex, RingEquiv.symm_apply_apply, ← alg_alg]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) _ * _ ∈ _
    rw [← map_mul]
    refine alg_int_mem X v _ ?_
    rw [map_mul]
    show Valued.v ((dV v)⁻¹ ^ k) * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F)) ≤ 1
    rw [map_pow, map_inv₀]
    have h1 := val_pow_le v k x hx
    have h0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
    calc (Valued.v (dV v))⁻¹ ^ k * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F))
        ≤ (Valued.v (dV v))⁻¹ ^ k * Valued.v (dV v) ^ k := mul_le_mul' le_rfl h1
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  exact hle hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.NegNatUnit
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem negNat_unit (v : PlX X) (T : ℕ) (hT : ((T : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal) :
    ∃ u ∈ OEv (E := X.B.I.E) v, inclR (Fv X.B.I.F v) (-((T : ℕ) : X.B.I.E)) * u = 1 := by
  set t : Fv X.B.I.F v := ((T : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_⟩
  have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
        inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [← Algebra.smul_def]; rfl
  rw [e1, mul_left_comm, ← map_mul]
  have e2 : (-((T : ℕ) : X.B.I.E)) * (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) = ((T : ℕ) : X.B.I.E) := by
    push_cast; ring
  rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
    inv_mul_cancel₀ ht0, map_one]

theorem zi_val : (zi (D := D)).val = D.R.rS := by simp [zi]

theorem hR_comb (v : PlX X) (c : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (j : Fin (D.R.rS + 1 + D.R.rS)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (∑ i, c i • yTup X u' v i) =
      c (piv D.R.rS j) * inclR (Fv X.B.I.F v) (cD X u' j) := by
  rw [hR_sum_right]
  have hg : ∀ i, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (yTup X u' v i) =
      inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) := fun i =>
    congrFun (congrFun (omVGram_holds X u' v) j) i
  simp only [hR_smulE_right, hg, gramE_entry, apply_ite (inclR (Fv X.B.I.F v)), map_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem omVPrim_of (hM : OmVMem X u') (hZ : OmVZPrim X u') : OmVPrim X u' := by
  intro v
  refine ⟨hM v, fun c hc => ?_⟩
  have hne : ∀ i, i ≠ zi (D := D) → c i ∈ OEv (E := X.B.I.E) v := by
    intro i hi
    have hj : piv D.R.rS (piv D.R.rS i) = i := piv_invol D.R.rS i
    have hjz : (piv D.R.rS i).val ≠ D.R.rS := by
      intro h
      apply hi
      have : piv D.R.rS i = zi (D := D) := Fin.ext (by rw [h, zi_val])
      rw [← hj, this, pivot_castAdd_last]
    have h1 := hR_comb X u' v c (piv D.R.rS i)
    rw [hj, cD, if_neg hjz, map_one, mul_one] at h1
    rw [← h1]
    exact omVSD_fwd X v (hM v _) hc
  intro i
  by_cases hi : i = zi (D := D)
  · subst hi
    have hz : c (zi (D := D)) • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
      have e : c (zi (D := D)) • yTup X u' v (zi (D := D)) =
          (∑ i, c i • yTup X u' v i) - ∑ i ∈ Finset.univ.erase (zi (D := D)), c i • yTup X u' v i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (zi (D := D))), add_sub_cancel_right]
      rw [e]
      refine Submodule.sub_mem _ hc (Submodule.sum_mem _ fun i hi => lat_oev_smul X v ?_ (hM v i))
      exact hne i (Finset.ne_of_mem_erase hi)
    by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
    · exact hZ v hT _ hz
    · obtain ⟨u, hu, hu1⟩ := negNat_unit X v (Tw u') hT
      have h1 := hR_comb X u' v c (zi (D := D))
      rw [pivot_castAdd_last, cD, if_pos zi_val] at h1
      have h2 : c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ OEv (E := X.B.I.E) v := by
        rw [← h1]; exact omVSD_fwd X v (hM v _) hc
      have h3 : c (zi (D := D)) = (c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E))) * u := by
        rw [mul_assoc, hu1, mul_one]
      rw [h3]
      exact oev_mul v h2 hu
  · exact hne i hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVSD_holds : OmVSD X := omVSD_of X (omVSDBwd_holds X)

theorem omVPrim_of_dd (hD : OmVDdLoc X) : OmVPrim X u' :=
  omVPrim_of X u' (omVMem_of X u' (omVMemEF_of X u' hD)) (omVZPrim_holds X u')

theorem omVSD_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVSD X := omVSD_holds X

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

theorem host_el (x0 : 𝓞 X.B.I.F) : ∃ d0 : 𝓞 D.host.F, ((d0 : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := by
  have hmem : X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ∈ D.host.F := (X.ιE_F _).2 ⟨x0, rfl⟩
  set y : D.host.F := ⟨_, hmem⟩
  have hi : IsIntegral ℤ (X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F))) :=
    ((RingOfIntegers.isIntegral_coe x0).map (algebraMap X.B.I.F X.B.I.E).toIntAlgHom).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom
  have hy : IsIntegral ℤ y :=
    (isIntegral_algHom_iff ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom Subtype.val_injective).1 hi
  exact ⟨⟨y, (mem_integralClosure_iff ℤ _).2 hy⟩, rfl⟩

theorem dd2 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ (ddS D ^ k)⁻¹) :
    sc (E := X.B.I.E) v ((dV v) ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨x0, hx0, hv0⟩ := (dV_isDiffVal v).2.2
  obtain ⟨d0, hd0e⟩ := host_el X x0
  have hd0 : d0 ∈ differentIdeal ℤ (𝓞 D.host.F) := (hT d0).2 ⟨x0, hx0, hd0e.symm⟩
  set g : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d0 with hg_def
  have hgE : (g : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := hd0e
  set c : Fv X.B.I.F v := algebraMap X.B.I.F (Fv X.B.I.F v) (x0 : X.B.I.F) with hc_def
  have hvd0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv0; exact hvd0 hv0.symm
  have hg0 : (g : D.host.E) ≠ 0 := by
    rw [hgE]; intro h
    apply hc0
    have : algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F) = 0 := by
      rw [← map_zero X.ιE] at h; exact X.ιE.injective h
    rw [hc_def, (algebraMap X.B.I.F X.B.I.E).injective (this.trans (map_zero _).symm), map_zero]
  have hgk : (g : D.host.E) ^ k ∈ ddS D ^ k := by
    rw [ddS_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (d0 ^ k),
      Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hd0 k), by rw [map_pow, map_pow]⟩
  have hne : ddS D ^ k ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hgk
    exact hg0 (by by_contra hne0; exact (pow_ne_zero k hne0) hgk)
  have hprod : x * (g : D.host.E) ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hx hgk
    rwa [inv_mul_cancel₀ hne] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
  have key : X.ιE.symm x * (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ^ k = X.ιE.symm (o : D.host.E) := by
    have h1 : ((o : D.host.E)) = x * (g : D.host.E) ^ k := ho
    rw [h1, map_mul, map_pow, hgE, RingEquiv.symm_apply_apply]
  have key2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) *
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c ^ k) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key, map_mul, map_pow, map_pow, hc_def, alg_alg]
  have hu : Valued.v (dV v * c⁻¹) = 1 := by rw [map_mul, map_inv₀, ← hv0, mul_inv_cancel₀ (hv0 ▸ hvd0)]
  have hid : (dV v * c⁻¹) ^ k * c ^ k = dV v ^ k := by
    rw [mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc0), mul_one]
  have e : sc (E := X.B.I.E) v (dV v ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((dV v * c⁻¹) ^ k) *
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key2]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (dV v ^ k) * _ = _
    rw [← hid, map_mul]; ring
  rw [e]
  refine oev_mul v (alg_int_mem X v _ ?_) (incl_mem v (⟨X.ιE.symm (o : D.host.E),
    (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E))
  rw [map_pow, hu, one_pow]

theorem omVDdLoc_of (hT : OmVDdTr X) : OmVDdLoc X := by
  intro v a
  have hlt : ((a.castSucc : Fin (D.R.rS + 1)) : ℕ) < D.R.rS := by simp
  have halp : alp v D.R.rS a.castSucc = (dV v)⁻¹ ^ (D.R.rS - (a : ℕ)) := by
    unfold alp; rw [if_pos hlt]; simp
  have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    rw [Nat.cast_sub a.isLt.le]
  have haa : aaD D a = (ddS D ^ (D.R.rS - (a : ℕ)))⁻¹ := by
    unfold aaD; rw [hk, zpow_neg, zpow_natCast]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [haa, inv_inv] at hx; rw [halp]; exact dd1 X hT v _ x hx
  · rw [haa] at hx; rw [halp, inv_pow, inv_inv]; exact dd2 X hT v _ x hx

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

theorem mem_diff_iff {K : Type} [Field K] [NumberField K] (x : 𝓞 K) :
    x ∈ differentIdeal ℤ (𝓞 K) ↔ ∀ y : K, (∀ a : 𝓞 K, Algebra.trace ℚ K (y * a) ∈ (algebraMap ℤ ℚ).range) →
      IsIntegral ℤ ((x : K) * y) := by
  have h1 : x ∈ differentIdeal ℤ (𝓞 K) ↔ (x : K) ∈ IsLocalization.coeSubmodule K (differentIdeal ℤ (𝓞 K)) := by
    rw [IsLocalization.mem_coeSubmodule]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨x', hx', he⟩
      have : x' = x := Subtype.ext he
      rwa [← this]
  rw [h1, coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h y hy
    have h2 := h y (by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
      simpa [Algebra.traceForm_apply] using hy a')
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
    rw [← hb]
    exact RingOfIntegers.isIntegral_coe b
  · intro h y hy
    rw [Submodule.mem_traceDual] at hy
    have hint := h y (fun a => by simpa [Algebra.traceForm_apply] using hy _ (Submodule.mem_one.2 ⟨a, rfl⟩))
    exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

theorem diff_map {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K ≃+* K')
    (x : 𝓞 K) (x' : 𝓞 K') (hxx : e (x : K) = (x' : K')) (hx : x ∈ differentIdeal ℤ (𝓞 K)) :
    x' ∈ differentIdeal ℤ (𝓞 K') := by
  rw [mem_diff_iff] at hx ⊢
  intro y' hy'
  have htr : ∀ z : K, Algebra.trace ℚ K' (e z) = Algebra.trace ℚ K z := fun z =>
    Algebra.trace_eq_of_algEquiv e.toRatAlgEquiv z
  have hy : ∀ a : 𝓞 K, Algebra.trace ℚ K (e.symm y' * a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hi : IsIntegral ℤ (e (a : K)) := (RingOfIntegers.isIntegral_coe a).map (e : K →+* K').toIntAlgHom
    have h3 := hy' ⟨e a, (mem_integralClosure_iff ℤ K').2 hi⟩
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h3
  have h4 := (hx _ hy).map (e : K →+* K').toIntAlgHom
  change IsIntegral ℤ (e ((x : K) * e.symm y')) at h4
  rwa [map_mul, RingEquiv.apply_symm_apply, hxx] at h4

variable {D : D7} (X : HidaSetting D)

def eF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    (((X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
      (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => iota_alg_inj X (congrArg Subtype.val h), fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F (y : D.host.E)).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem eF_val (a : X.B.I.F) : ((eF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

theorem omVDdTr_holds : OmVDdTr X := by
  intro d
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := pre_int X d
    refine ⟨x, diff_map (eF X).symm d x ?_ hd, hx⟩
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [eF_val]; exact hx.symm)
  · rintro ⟨x, hx, hxd⟩
    exact diff_map (eF X) x d (Subtype.ext (by rw [eF_val]; exact hxd)) hx

theorem omVDdLoc_holds : OmVDdLoc X := omVDdLoc_of X (omVDdTr_holds X)

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVPrim_holds : OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_holds X)

theorem omVPrim_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_holds X u'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
