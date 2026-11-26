module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
noncomputable section

open scoped MatrixGroups Matrix Classical
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sXiCoh : SXiCoh := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy A _ π u u' h
  obtain ⟨a, ha, hu⟩ := h
  obtain ⟨hE, hadd, -⟩ := sApi Ω ε X l n
  refine ⟨fun t => Xi X l n N M₀ M w g x y (fun z => π z = t) a,
    fun t => sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy _ a ha, fun s t => ?_⟩
  have h1 := (sXiMul Ω ε X l n N M₀ M w g hL x y hxy (fun z => π z = t)).1 (u s) (u' s) (tw X (l ^ n) M₀ s a) a (hu s)
  have h2 := sXiTw Ω ε X l n N M₀ M w g hL x y (fun z => π z = t) a s
  have h3 : (fun z => π (z * cycM M s) = t) = fun z => π z = t * (π (cycM M s))⁻¹ := by
    funext z
    rw [map_mul, eq_mul_inv_iff_mul_eq]
  rw [h3] at h2
  exact hE.trans h1 (hadd _ _ _ _ (hE.refl _) (hadd _ _ _ _ h2 (hE.refl _)).2).1

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

private theorem cgr_solve {K : Type} [Field K] {m : ℕ} {f a b c d : Kˣ} (h : Cgr m f (a * b)) (h' : Cgr m f (c * d)) :
    Cgr m b (c * d / a) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  refine ⟨k' / k, ?_⟩
  rw [div_pow, div_mul_div_comm, ← hk', hk, eq_div_iff_mul_eq', mul_assoc, mul_left_comm]

theorem sBridge : SBridge := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz A _ _ π
  obtain ⟨eqv, hadd, -, hsum, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, -, isum, -⟩ := sInvApi Ω ε X l N w n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcyc := (sSlD Ω ε X N hN).2.2.2.2.2.2.2 M
  have cmul : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t := fun s t => (hcyc s).2.1 t
  have crep : ∀ t, cycM M (repM M t : Ω ≃ₐ[ℚ] Ω) = t := (hcyc 1).2.2.1
  have cfix : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1 := fun s => (hcyc s).2.2.2.1
  have hM := sXiMul Ω ε X l n N M₀ M w g hL x y hxy
  have hT := sXiTw Ω ε X l n N M₀ M w g hL x y
  have hI := sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy
  let B : (ZMod M)ˣ → X.Fn l := fun t =>
    Xi X l n N M₀ M w g x y (fun z => z = t) (u (repM M t)) + X.galB l (repM M t) β
  have hB : ∀ t, InvM X l N w n (B t) := fun t =>
    (iadd _ _ (hI _ _ (hu.eqv _)) (sGalAct Ω ε X l N w n hN _ β hβ).1).1
  have key : ∀ (s : Ω ≃ₐ[ℚ] Ω) (t : (ZMod M)ˣ), CgF X l n (shB X l M z s t)
      (Xi X l n N M₀ M w g x y (fun z => z = t) (u s) + (X.galB l s (B (t * (cycM M s)⁻¹)) - B t)) := by
    intro s t
    unfold shB
    simp only [B]
    generalize hτ : (repM M t : Ω ≃ₐ[ℚ] Ω) = τ
    generalize hτ' : (repM M (t * (cycM M s)⁻¹) : Ω ≃ₐ[ℚ] Ω) = τ'
    have c1 : cycM M τ = t := hτ ▸ crep _
    have c2 : cycM M τ' = t * (cycM M s)⁻¹ := hτ' ▸ crep _
    generalize hσ : τ⁻¹ * s * τ' = σ
    have e : τ * σ = s * τ' := by rw [← hσ]; group
    have hfix : σ ∈ fixMu Ω M := by
      rw [cfix]
      have h := congrArg (cycM M) e
      rw [cmul, cmul, c1, c2, mul_comm (cycM M s), inv_mul_cancel_right] at h
      exact mul_eq_left.1 h
    have h1 := hgal τ _ _ (hz σ hfix)
    rw [map_add (f := _), map_sub, ← hmul, e, hmul] at h1
    have h2 := hT (fun z => z = t) (u σ) τ
    have p2 : (fun z : (ZMod M)ˣ => z * cycM M τ = t) = fun z => z = 1 := by
      funext z
      rw [c1, mul_eq_right]
    rw [p2] at h2
    have h3 := (hM (fun z => z = t)).1 (tw X (l ^ n) M₀ τ (u σ)) (u s) (tw X (l ^ n) M₀ s (u τ')) (u τ)
      fun x y h => cgr_solve (hu.coc τ σ x y h) (e ▸ hu.coc s τ' x y h)
    have h4 := hT (fun z => z = t) (u τ') s
    have p4 : (fun z : (ZMod M)ˣ => z * cycM M s = t) = fun z => z = t * (cycM M s)⁻¹ := by
      funext z
      rw [eq_mul_inv_iff_mul_eq]
    rw [p4] at h4
    have h5 := eqv.trans (eqv.symm h2) (eqv.trans h3 (hadd _ _ _ _ (eqv.refl _) (hadd _ _ _ _ h4 (eqv.refl _)).2).1)
    have h6 := eqv.trans h1 (hadd _ _ _ _ h5 (eqv.refl _)).1
    convert h6 using 1
    rw [map_add (f := _)]
    abel
  refine ⟨fun t => ∑ v ∈ Finset.univ.filter (fun v => π v = t), B v, fun t => isum _ _ _ fun v _ => hB v, fun s t => ?_⟩
  have h := hsum _ (Finset.univ.filter (fun v => π v = t)) _ _ fun v _ => key s v
  have r : ∑ v ∈ Finset.univ.filter (fun v => π v = t * (π (cycM M s))⁻¹), B v =
      ∑ v ∈ Finset.univ.filter (fun v => π v = t), B (v * (cycM M s)⁻¹) := by
    symm
    refine Finset.sum_equiv (Equiv.mulRight (cycM M s)⁻¹) (fun v => ?_) fun v _ => rfl
    simp
  beta_reduce
  set_option synthInstance.maxHeartbeats 100000 in
    rw [r, (hM (fun _ => True)).2.2.2 (u s) A π t, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact h

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopCocG
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem pol_cont {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (w n : ℕ) (t : X.Fn l) (ht : PolMod X l w n t) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → CgF X l n (X.galB l s t) t := by
  obtain ⟨c, hc, htc⟩ := ht
  choose f _ hf using hc
  choose Ec hEc using fun i => GlobalTheory.KZ.GalCont.fix_fin X (f i : X.K)
  obtain ⟨Ez, hEz⟩ := GlobalTheory.KZ.GalCont.cyc_sub_one_mem (Ω := Ω) l n
  obtain ⟨-, -, -, -, hmap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, hsm, -⟩ := sApi Ω ε X l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s fun x hx => hs x (Finset.mem_union_left _ hx)
  rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hχ
  have hk : ∀ i, AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s) (c i)) =
      AdicCompletion.eval (idl l) (X.Kl l) n (c i) := by
    intro i
    have h1 := hmap (X.gal s) _ _ (hf i)
    have h2 : Units.map (X.gal s : X.K →* X.K) (f i) = f i :=
      Units.ext (hEc i s fun x hx => hs x (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
    rw [h2] at h1
    exact (show _ = _ from h1).trans (show _ = _ from hf i).symm
  have hgal : X.galB l s t u =
      X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hgal, htc, htc, map_sum, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_smul, map_sub, map_smul, hk, ← map_smul, ← map_sub]
  refine hsm _ _ _ ?_
  rw [← mul_sub]
  refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ _)) _
  rw [← sub_one_mul]
  exact hχ.mul_right _

theorem UpperTheory.V.Z.Kato.Nb.sTopCocG :
    UpperTheory.V.Z.Kato.Nb.STopCocG := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz
  obtain ⟨hE, hadd, -, -, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, icg, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨m1, m2, -⟩ := sXiMul Ω ε X l n N M₀ M w g hL x y hxy (fun z => z = 1)
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N (NeZero.pos N)
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact icg _ _ (hz σ hσ) (iadd _ _ (sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy _ _ (hu.eqv σ))
      (iadd _ _ (sGalAct Ω ε X l N w n (NeZero.pos N) σ β hβ).1 hβ).2).1
  · have h0 := m2 (u σ) 0
    rw [Nat.cast_zero, zero_smul] at h0
    have h1 := m1 (u (σ * τ)) (u σ) (tw X (l ^ n) M₀ σ (u τ)) (fun x y => u σ x y ^ 0) fun x y h => by
      simpa using hu.coc σ τ x y h
    have h2 := sXiTw Ω ε X l n N M₀ M w g hL x y (fun z => z = 1) (u τ) σ
    rw [(hcy M σ).2.2.2.1.1 hσ] at h2
    simp only [mul_one] at h2
    have h3 := hE.trans h1 (hadd _ _ _ _ (hE.refl _) (hadd _ _ _ _ h2 h0).2).1
    have h4 := hE.trans (hz _ (mul_mem hσ hτ)) (hadd _ _ _ _ h3 (hE.refl _)).1
    have h5 := (hadd _ _ _ _ (hz σ hσ) (hgal σ _ _ (hz τ hτ))).1
    refine hE.trans h4 (hE.symm ?_)
    convert h5 using 1
    rw [hmul, map_add (f := _), map_sub]
    abel
  · obtain ⟨T, hT⟩ := hu.loc
    obtain ⟨⟨t, ht, hβt⟩, -⟩ := hβ
    obtain ⟨E, hEt⟩ := pol_cont X l w n t ht
    refine ⟨T ∪ E, fun σ hσ τ hτ h => ?_⟩
    have h1 := m1 (u σ) (u τ) (u τ) (u τ) fun x y hh => by
      simpa using hT σ τ (fun a ha => h a (Finset.mem_union_left _ ha)) x y hh
    rw [sub_self, add_zero] at h1
    have h2 := hEt (τ⁻¹ * σ) fun a ha => by
      rw [AlgEquiv.mul_apply, h a (Finset.mem_union_right _ ha), ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h3 := hgal τ _ _ (hE.trans (hgal _ _ _ hβt) (hE.trans h2 (hE.symm hβt)))
    rw [← hmul, mul_inv_cancel_left] at h3
    exact hE.trans (hz σ hσ) (hE.trans (hadd _ _ _ _ h1 (hadd _ _ _ _ h3 (hE.refl β)).2).1 (hE.symm (hz τ hτ)))
end
