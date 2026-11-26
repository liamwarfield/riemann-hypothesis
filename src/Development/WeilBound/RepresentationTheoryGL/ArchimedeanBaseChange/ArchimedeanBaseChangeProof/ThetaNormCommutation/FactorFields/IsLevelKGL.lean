module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.IsLevelKGL
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinPol2P

theorem isLevel_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩

end PositivityTheory.Rg.BcB.G3.FinPol2P

open PositivityTheory.Rg.BcB.G3.FinPol2P in
theorem PositivityTheory.Rg.BcB.G3.finPol2_pf : FinPol2 := by
  intro E _ _ _ hU a b S hS φ hφc hφ1
  have hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w)) := fun w => (hφc w).image continuous_fst
  have hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w)) := fun w => (hφc w).image continuous_snd
  choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)
  choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)
  let good : Pl E → Prop := fun w => φ w = (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) :
    Set (GLw a w × GLw b w)).indicator 1
  let g₁ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₁ w
  let g₂ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₂ w
  have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁
    (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])
  have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂
    (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])
  refine (hfin₁.prod hfin₂).subset ?_
  rintro p ⟨h₁, h₂, hp⟩
  have key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧
      ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0)) := by
    intro w hw
    obtain ⟨y, hy, e₁, e₂⟩ := hp w hw
    rw [← e₁, ← e₂]
    by_cases hg : good w
    · simp only [g₁, g₂, if_pos hg, inv_one]
      have hy' : y ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
        have hy2 := hy
        rw [show φ w = _ from hg] at hy2
        by_contra hc
        exact hy2 (Set.indicator_of_notMem hc _)
      exact ⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1,
        GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩
    · simp only [g₁, g₂, if_neg hg]
      have hyt : y ∈ tsupport (φ w) := subset_tsupport _ hy
      exact ⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩
  exact ⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocGood
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocGoodP

theorem nrmL_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z : GLw n w) (hz : z ∈ GlobalTheory.LFun.KGL w (n := n)) : nrmL n w z ∈ GlobalTheory.LFun.KGL w (n := n) := by
  obtain ⟨-, -, hKθ, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  unfold nrmL
  split_ifs with hs
  · exact hz
  · have : thetaGL n (cj w) z = thL n w z := by unfold thL; rw [if_neg hs]
    rw [this]
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem hz (hKθ _ hz)

theorem commute_nrmL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z t : GLw n w) (ht : t ∈ twCent (thL n w) z) : t * nrmL n w z = nrmL n w z * t := by
  obtain ⟨-, hinv, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have ht' : t * z = z * thL n w t := ht
  by_cases hs : IsSplitAt w
  · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
    rw [hn1]; rw [hθ1] at ht'; simpa using ht'
  · have hn1 : nrmL n w z = z * thL n w z := by
      unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
    rw [hn1]
    calc t * (z * thL n w z) = z * thL n w t * thL n w z := by rw [← mul_assoc, ht']
      _ = z * thL n w (t * z) := by simp only [map_mul, mul_assoc]
      _ = z * thL n w (z * thL n w t) := by rw [ht']
      _ = z * thL n w z * t := by simp only [map_mul, hinv, mul_assoc]

end PositivityTheory.Rg.BcB.G3.LocGoodP

open PositivityTheory.Rg.BcB.G3.LocGoodP in
theorem PositivityTheory.Rg.BcB.G3.locGood_pf : LocGood := by
  intro E _ _ _ hU n P hP
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1,
    GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep
  intro z hzK hz
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1 := by
    rw [hz]; exact hgood
  have hNK := nrmL_mem hU n w z hzK
  refine ⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg
      refine ⟨t, ?_, k, hk, rfl⟩
      show t * z = z * thL n w t
      rw [hθ1]; exact ht
    · exact GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc
  · exact GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsOnto
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsOntoP

theorem only_rho {k : Type} [Field k] [CharZero k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type}
    [CommRing B] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (hs0 : s ≠ 0) (hcs : c s = -s)
    (x : GL (Fin n) k) (hx : x * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * x)
    (hk : x * δ * thetaGL n c x = δ) : ∃ u, x.val = ρ u := by
  obtain ⟨u, v, huv⟩ := hF.span x.val (by simpa only [Units.val_mul] using congrArg Units.val hx)
  have hA := ClsEqP.A_delta_theta hF hcs x u v huv
  have e : x.val * (δ * thetaGL n c x).val = (ρ u - s • ρ v) * (δ * thetaGL n c x).val := by
    have hk' : x.val * (δ.val * (thetaGL n c x).val) = δ.val := by
      have := congrArg Units.val hk
      simpa only [Units.val_mul, Matrix.mul_assoc] using this
    rw [Units.val_mul, hA, hk']
  have h0 : x.val = ρ u - s • ρ v := by
    have := congrArg (· * ((δ * thetaGL n c x)⁻¹).val) e
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
  have e2 : s • ρ v = -(s • ρ v) := by
    have := huv.symm.trans h0
    rw [sub_eq_add_neg] at this
    exact add_left_cancel this
  have e3 : (2 * s) • ρ v = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [e2]
    exact add_neg_cancel _
  have hv : ρ v = 0 := (smul_eq_zero.mp e3).resolve_left (mul_ne_zero two_ne_zero hs0)
  exact ⟨u, by rw [huv, hv, smul_zero, add_zero]⟩

end PositivityTheory.Rg.BcB.G3.ClsOntoP

namespace PositivityTheory.Rg.BcB.G3

theorem clsOnto_pf : ClsOnto := by
  intro k _ _ n c hc δ s hs0 hcs B _ d ρ hF hsep y hy
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable k n (δ * thetaGL n c δ) (y * thetaGL n c y)
    hy.symm hsep
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) k, y' = h * y * (thetaGL n c h)⁻¹ := ⟨_, rfl⟩
  have hy'N : y' * thetaGL n c y' = δ * thetaGL n c δ := by
    rw [hy']
    simp only [map_mul, map_inv, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc]
    calc h * y * (thetaGL n c h)⁻¹ * (thetaGL n c h * thetaGL n c y * h⁻¹) = h * (y * thetaGL n c y) * h⁻¹ := by
          group
      _ = δ * thetaGL n c δ := by rw [hh]; group
  have hT : thetaGL n c y' * y' = thetaGL n c δ * δ := by
    have := congrArg (thetaGL n c) hy'N
    simpa only [map_mul, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc] using this
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin n) k, a = y' * δ⁻¹ := ⟨_, rfl⟩
  have hcomm : a * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a := by
    calc a * (δ * thetaGL n c δ) = y' * (thetaGL n c δ * δ) * δ⁻¹ := by rw [ha]; group
      _ = y' * (thetaGL n c y' * y') * δ⁻¹ := by rw [hT]
      _ = (y' * thetaGL n c y') * (y' * δ⁻¹) := by group
      _ = (δ * thetaGL n c δ) * a := by rw [hy'N, ha]
  have hkey : a * δ * thetaGL n c a = δ := by
    rw [ha]
    simp only [map_mul, map_inv]
    calc y' * δ⁻¹ * δ * (thetaGL n c y' * (thetaGL n c δ)⁻¹) = (y' * thetaGL n c y') * (thetaGL n c δ)⁻¹ := by
          group
      _ = δ := by rw [hy'N]; group
  have hcomm' : a⁻¹ * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * a⁻¹ := by
    calc a⁻¹ * (δ * thetaGL n c δ) = a⁻¹ * ((δ * thetaGL n c δ) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (δ * thetaGL n c δ)) * a⁻¹ := by rw [hcomm]
      _ = (δ * thetaGL n c δ) * a⁻¹ := by group
  have hkey' : a⁻¹ * δ * thetaGL n c a⁻¹ = δ := by
    calc a⁻¹ * δ * thetaGL n c a⁻¹ = a⁻¹ * (a * δ * thetaGL n c a) * thetaGL n c a⁻¹ := by rw [hkey]
      _ = δ := by rw [map_inv]; group
  obtain ⟨u, hu⟩ := ClsOntoP.only_rho hF hs0 hcs a hcomm hkey
  obtain ⟨u', hu'⟩ := ClsOntoP.only_rho hF hs0 hcs a⁻¹ hcomm' hkey'
  have huu : u * u' = 1 := by
    apply hF.inj
    rw [map_mul, ← hu, ← hu', Units.mul_inv, map_one]
  let t : Bˣ := ⟨u, u', huu, by rw [mul_comm, huu]⟩
  have hta : Units.map ρ.toMonoidHom t = a := by
    apply Units.ext
    rw [ClsNormP.units_map_val, hu]
  refine ⟨t, h, ?_⟩
  have hpt : pt δ ρ t = y' := by
    rw [pt, hta, ha]; group
  rw [hpt, hy']
  group

end PositivityTheory.Rg.BcB.G3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocDict
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocDictP

theorem frame_transport {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B B' : Type}
    [CommRing B] [CommRing B'] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (e : B ≃+* B')
    (h : IsFrame c δ s d ρ) : IsFrame c δ s (e d) (ρ.comp e.symm.toRingHom) := by
  refine ⟨h.inj.comp e.symm.injective, ?_, ?_, ?_, ?_⟩
  · simpa using h.sq
  · exact fun a => h.adj (e.symm a)
  · exact fun a => h.comm (e.symm a)
  · intro x hx
    obtain ⟨a, b, hab⟩ := h.span x hx
    exact ⟨e a, e b, by simpa using hab⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs0 : s ≠ 0)
    (hsc : IsCMField.complexConj E s = -s) (z : E) :
    ∃ a b : (maximalRealSubfield E),
      z = algebraMap (maximalRealSubfield E) E a + s * algebraMap (maximalRealSubfield E) E b := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (z + IsCMField.complexConj E z) / 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat,
      add_comm]
  have hb : (z - IsCMField.complexConj E z) / (2 * s) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat,
      hsc]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change z = (z + IsCMField.complexConj E z) / 2 + s * ((z - IsCMField.complexConj E z) / (2 * s))
  field_simp
  ring

end PositivityTheory.Rg.BcB.G3.LocDictP

open PositivityTheory.Rg.BcB.G3.LocDictP in
theorem PositivityTheory.Rg.BcB.G3.locDict_pf (h1 : ClsNorm) (h2 : ClsOnto) (h3 : ClsEq) (h4 : BaseFrame) (h5 : InertBase)
    (h6 : SplitSq) (h7 : TensorCompl) : LocDict := by
  intro E _ _ _ hU s d hs0 hsc hd n δ hsep ι _ K _ _ _ ρ hfr w y hy
  have hdne : d ≠ 0 := by
    rintro rfl
    apply hs0
    have : s ^ 2 = 0 := by rw [← hd, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  by_cases hw : IsSplitAt w
  ·
    have hthL : thL n w = MonoidHom.id _ := by simp only [thL, if_pos hw]
    have hy' : y.val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
      have := hy; simp only [nrmL, if_pos hw] at this; exact this
    refine ⟨fun _ _ => 1, fun t => ⟨fun _ => ?_, fun _ => ?_⟩⟩
    · intro i u
      obtain ⟨r, hr⟩ := h6 E s d hs0 hsc hd w hw
      obtain ⟨e, he⟩ := h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
      have hq : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u =
          algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := by
        rw [← he, ← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← hr, mul_one,
          Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      have hti : ((t : ∀ i, K i) i) ≠ 0 := ((t.isUnit.map (Pi.evalRingHom K i)).ne_zero)
      have hT : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ i, K i) i) ≠ 0 := (_root_.map_ne_zero _).2 hti
      have hD : algebraMap (K i) (u.1.adicCompletion (K i)) (algebraMap (maximalRealSubfield E) (K i) d) ≠ 0 :=
        (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hdne)
      have hq0 : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hq; exact hD hq.symm
      refine ⟨(1 + (algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹) / 2,
        ((algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹ - 1) / (2 * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u), ?_⟩
      have : CharZero (u.1.adicCompletion (K i)) :=
        charZero_of_injective_algebraMap (algebraMap (K i) (u.1.adicCompletion (K i))).injective
      simp only [Units.val_one]
      rw [← hq]
      field_simp
      ring
    · have hinv : ∀ x : E, (IsCMField.complexConj E).toRingEquiv.toRingHom
          ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
      have hN := h1 E n _ hinv δ s hs0 hsc (∀ i, K i) _ ρ.toRingHom hfr t
      have hloc : locEl n w (pt δ ρ.toRingHom t) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
        simp only [locEl, if_pos hw, thE, hN]
      have hc1 : y.val.charpoly = (locEl n w (pt δ ρ.toRingHom t)).val.charpoly := by
        rw [hloc, hy']
        change _ = (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly
        rw [Matrix.charpoly_map]
      obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable _ n y _ hc1 (hy' ▸ hsep.map)
      exact ⟨h, by rw [hthL, MonoidHom.id_apply]; exact hh⟩
  ·
    have hI := GlobalTheory.ConjAtPlace.main E hU w
    have hcc : ∀ x, cj w (cj w x) = x := hI.2.1
    have hcE := (hI.2.2.2.1 hw).1
    have : CharZero (w.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    obtain ⟨j, hj1, hj2, hj3⟩ := h5 E hU s d hs0 hsc hd w hw
    obtain ⟨ρ', hρ'1, hρ'⟩ := h4 (maximalRealSubfield E) E
      ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) (w.adicCompletion E)
      (algebraMap E _) j (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) s d hj1 (fun x => hcE x) hj2 hs0 hsc
      (decomp E s hs0 hsc) hj3 n δ hsep (∀ i, K i) ρ hfr
    have hTC := fun i => h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
    choose e he using hTC
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E]
        (∀ i, K i)) ≃+* (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)),
        ∀ a : (∀ i, K i), Φ (1 ⊗ₜ a) = fun i u => algebraMap (K i) _ (a i) :=
      ⟨(Algebra.TensorProduct.piRight (maximalRealSubfield E) (maximalRealSubfield E) _ K).toRingEquiv.trans
        (RingEquiv.piCongrRight e), fun a => by
          funext i u
          simp [Algebra.TensorProduct.piRight_tmul, he]⟩
    have hfr'' := frame_transport Φ hρ'
    have hmapθ := GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E))
      (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) (fun x => (hcE x).symm) δ
    have hNδ : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly =
        atPl w (δ * thE E n δ).val.charpoly := by
      rw [← hmapθ, ← map_mul]
      change (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly = _
      rw [Matrix.charpoly_map]
    have hsep' : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly.Separable := by
      rw [hNδ]; exact hsep.map
    have hy' : (y * thetaGL n (cj w) y).val.charpoly = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly := by
      rw [hNδ]
      have := hy; simp only [nrmL, if_neg hw] at this; exact this
    have hs0' : algebraMap E (w.adicCompletion E) s ≠ 0 := (_root_.map_ne_zero _).2 hs0
    have hsc' : cj w (algebraMap E (w.adicCompletion E) s) = -algebraMap E (w.adicCompletion E) s := by
      rw [hcE, hsc, map_neg]
    obtain ⟨t0, g0, hg0⟩ := h2 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' hsep' y hy'
    refine ⟨fun i u => Units.map (Pi.evalMonoidHom _ u) (Units.map (Pi.evalMonoidHom _ i) t0), fun t => ?_⟩
    obtain ⟨T, hT⟩ : ∃ T : (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i))ˣ,
        (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) = Φ (1 ⊗ₜ (t : ∀ i, K i)) :=
      ⟨Units.map (Φ.toMonoidHom.comp
        (Algebra.TensorProduct.includeRight : (∀ i, K i) →ₐ[maximalRealSubfield E] _).toRingHom.toMonoidHom) t, rfl⟩
    have hpt : locEl n w (pt δ ρ.toRingHom t) = pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
        (ρ'.comp Φ.symm.toRingHom) T := by
      apply Units.ext
      simp only [locEl, if_neg hw, pt]
      change ((ρ t * δ.val).map (algebraMap E (w.adicCompletion E))) =
        ρ' (Φ.symm (T : _)) * (δ.val.map (algebraMap E (w.adicCompletion E)))
      rw [hT, RingEquiv.symm_apply_apply, hρ'1, Matrix.map_mul]
    have hthL : thL n w = thetaGL n (cj w) := by simp only [thL, if_neg hw]
    rw [hpt, hthL]
    have step1 : (∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T =
        g⁻¹ * y * thetaGL n (cj w) g) ↔ ∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
          (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
            (ρ'.comp Φ.symm.toRingHom) t0 * thetaGL n (cj w) g := by
      rw [hg0]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g0 * g, by rw [hg, map_mul]; group⟩
      · rintro ⟨g, hg⟩
        exact ⟨g0⁻¹ * g, by rw [hg, map_mul, map_inv]; group⟩
    rw [step1, h3 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' t0 T]
    have hTv : ∀ i u, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) i u =
        algebraMap (K i) _ ((t : ∀ i, K i) i) := fun i u => by rw [hT, hΦ]
    have hdv : ∀ i u, Φ (1 ⊗ₜ algebraMap (maximalRealSubfield E) (∀ i, K i) d) i u =
        algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := fun i u => by rw [hΦ]; rfl
    constructor
    · rintro ⟨U, V, hUV⟩ i u
      refine ⟨U i u, V i u, ?_⟩
      have := congrFun (congrFun hUV i) u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv] at this
      simpa using this
    · intro h
      choose a b hab using h
      refine ⟨fun i u => a i u, fun i u => b i u, ?_⟩
      funext i u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv]
      simpa using hab i u
end
end
