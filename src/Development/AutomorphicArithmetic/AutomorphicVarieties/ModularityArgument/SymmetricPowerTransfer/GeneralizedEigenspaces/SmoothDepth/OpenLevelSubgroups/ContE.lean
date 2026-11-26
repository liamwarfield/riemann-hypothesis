module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ContE
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.ContRep
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem cont_m {K T : Type} [Fintype K] [TopologicalSpace T] {d : ℕ} (n : K → ℕ) (γ : T → K → GL (Fin d) ℂ)
    (hγ : ∀ k i j, Continuous fun t => (γ t k : Matrix (Fin d) (Fin d) ℂ) i j) (x : MH d n) (f : MH d n →ₗ[ℂ] ℂ) :
    Continuous fun t => f (mRep d n (γ t) x) := by
  haveI : FiniteDimensional ℂ (MH d n) := finMH K d n
  let W : Submodule ℂ (Module.Dual ℂ (MH d n)) :=
    { carrier := {φ | Continuous fun t => φ (mRep d n (γ t) x)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, LinearMap.add_apply] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, LinearMap.zero_apply]
        exact continuous_const
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, LinearMap.smul_apply, smul_eq_mul] at *
        exact continuous_const.mul ha }
  have hev : ∀ y : K × Fin d → ℂ,
      (MvPolynomial.aeval y : MvPolynomial (K × Fin d) ℂ →ₐ[ℂ] ℂ).toLinearMap.comp (MH d n).subtype ∈ W := by
    intro y
    have hc : Continuous fun t => MvPolynomial.eval y ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ) := by
      simp only [eval_mRep]
      refine (MvPolynomial.continuous_eval (x : MvPolynomial (K × Fin d) ℂ)).comp ?_
      refine continuous_pi fun p => ?_
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (hγ p.1 j p.2)
    show Continuous fun t => (MvPolynomial.aeval y) ((mRep d n (γ t) x : MH d n) : MvPolynomial (K × Fin d) ℂ)
    convert hc using 2 with t
    exact DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
  have hb : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply MvPolynomial.funext
    intro y
    have := hv _ (hev y)
    have e : (MvPolynomial.aeval y) (v : MvPolynomial (K × Fin d) ℂ) = MvPolynomial.eval y (v : MvPolynomial (K × Fin d) ℂ) :=
      DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval y) _
    rw [Submodule.coe_zero, map_zero, ← e]
    exact this
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hb, Submodule.dualAnnihilator_bot]
  have hf : f ∈ W := htop ▸ Submodule.mem_top
  exact hf

theorem UpperTheory.V.Z.Sym.Wt.contRep :
    UpperTheory.V.Z.Sym.Wt.ContRep := by
  intro I _
  classical
  have entc : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => ((g k : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_val (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  have entci : ∀ (d : ℕ) (k : I) (i j : Fin d),
      Continuous fun g : I → GL (Fin d) ℂ => (((g k)⁻¹ : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro d k i j
    exact ((Units.continuous_coe_inv (M := Matrix (Fin d) (Fin d) ℂ)).comp (continuous_apply k)).matrix_elem i j
  refine ⟨fun j x f => ?_, fun n e x f => ?_⟩
  · have hsplit : (fun g => f (repG I j g x)) = fun g => ∑ S, f (Pi.single S (repG I j g x S)) := by
      funext g
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]
    rw [hsplit]
    refine continuous_finsetSum _ fun S _ => ?_
    have hent : ∀ (k : I × Bool) (i i' : Fin 3),
        Continuous fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
      intro k i i'
      have hfun : (fun g : I → GL (Fin 3) ℂ => ((dbl 3 g k : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i') =
          fun g => if k.2 = true then (((g k.1)⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i' i
            else ((g k.1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i i' := by
        funext g
        simp only [dbl, MonoidHom.coe_mk, OneHom.coe_mk]
        split_ifs <;> rfl
      rw [hfun]
      by_cases hk : k.2 = true
      · simp only [hk, if_true]
        exact entci 3 k.1 i' i
      · simp only [if_neg hk]
        exact entc 3 k.1 i i'
    exact cont_m (fun k : I × Bool => dg j S k.1) (fun g : I → GL (Fin 3) ℂ => dbl 3 g) hent (x S)
      (f ∘ₗ LinearMap.single ℂ (fun S => ↥(Bi 3 (dg j S))) S)
  · have hdet : ∀ v : I, Continuous fun g : I → GL (Fin 2) ℂ => Matrix.GeneralLinearGroup.det (g v) := by
      intro v
      refine Units.continuous_iff.mpr ⟨?_, ?_⟩
      · show Continuous fun g : I → GL (Fin 2) ℂ => ((Matrix.GeneralLinearGroup.det (g v) : ℂˣ) : ℂ)
        simp only [Matrix.GeneralLinearGroup.val_det_apply]
        exact ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
      · have h : ∀ g : I → GL (Fin 2) ℂ,
            (((Matrix.GeneralLinearGroup.det (g v))⁻¹ : ℂˣ) : ℂ) = (((g v)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det := by
          intro g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        simp only [h]
        exact ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) ℂ)).comp (continuous_apply v)).matrix_det
    have hd : Continuous fun g : I → GL (Fin 2) ℂ => detE 2 e g := by
      show Continuous fun g : I → GL (Fin 2) ℂ => ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e
      exact continuous_finsetProd _ fun v _ => (hdet v).zpow e
    simp only [repD_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact (Units.continuous_val.comp hd).mul
      (cont_m (fun _ : I => n) (fun g : I → GL (Fin 2) ℂ => g) (fun k i j => entc 2 k i j) x f)
end

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.contE :
    ∀ (I : Type) [Fintype I] (j : ℕ), (FiniteDimensional ℂ (Wt.VG I j) ∧ ContCoef (Wt.repG I j)) ∧
        (FiniteDimensional ℂ (Wt.VD I j) ∧ ∀ e : I → ℤ, ContCoef (repE j e)) := by
  intro I _ j
  obtain ⟨hG, hD⟩ := Wt.contRep I
  have hB : ∀ S : I → Bool, FiniteDimensional ℂ (Wt.Bi 3 (Wt.dg j S)) := fun S => Wt.finMH _ 3 _
  refine ⟨⟨Module.Finite.pi, fun x f => hG j x f⟩, ⟨Wt.finMH I 2 (fun _ => j), fun e x f => ?_⟩⟩
  have key : (fun g => f ((repE j e g) x)) = fun g =>
      ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) * f ((Wt.repD I j 0 g) x) := by
    funext g
    simp [repE, Wt.repD_apply, Wt.detE]
  rw [key]
  refine Continuous.mul (Units.continuous_val.comp ?_) (hD j 0 x f)
  exact continuous_finsetProd _ fun v _ =>
    ((Matrix.GeneralLinearGroup.continuous_det).comp (continuous_apply v)).zpow (e v)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocSub
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem torusChar_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {a b : Fin n → kˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  funext i
  ext x
  have e := DFunLike.congr_fun h (Pi.mulSingle i x)
  simp only [torusChar_apply] at e
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp),
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)] at e
  simpa using congrArg Units.val e

private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)

private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _

theorem UpperTheory.V.Z.Sym.Al.locSub :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
                 IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ ((Sig.Lev.iw k).J n) →
                 (∀ d, Sig.SDom d → Hi.dc τ ((Sig.Lev.iw k).J n) ((Sig.Lev.iw k).J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ) := by
  intro H k _ _ _ _ n ψ T _ _ τ hs hi v hv0 hvJ heig
  have hJ : (Sig.Lev.iw k).J n = UpperTheory.V.AlgebraTools.iwC k n ⊤ := (UpperTheory.V.Z.Sym.Sig.link k n).1
  rw [hJ] at hvJ heig
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.thetaEx k n ⊤ ℂ T τ hq
  let δ : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar ψ * δ⁻¹
  let w : Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤) := ⟨v, hvJ⟩
  have hw0 : w ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hsd : ∀ d, Sig.SDom d →
      (θ d : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ d : ℂ) • w := by
    intro d hd
    have hD : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
      rcases hij.eq_or_lt with rfl | h
      · exact le_rfl
      · exact (hd i j h).le
    rw [hθ d hD]
    refine Subtype.ext ?_
    have h1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ _ _ (Sig.dg d)
      ((UpperTheory.V.AlgebraTools.heckePairIwC k n ⊤).1 (Sig.dg d))).1 w
    exact h1.trans (heig d hd)
  have ht : ∀ t, (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ t : ℂ) • w := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Units.val_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_right_injective _ (Units.ne_zero (χ d)) h2
  have hne : (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) (χ t : ℂ)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨w, (Submodule.mem_iInf _).2 fun t => ?_, hw0⟩
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [ht t]
  obtain ⟨ψ', -, -, e, h2⟩ := UpperTheory.V.AlgebraTools.jqEmbed H.loc.bz k n ⊤ T τ hs hi θ hθ χ hne
  have hψ : ψ' = ψ := torusChar_injective (e.trans (by
    change torusChar ψ * δ⁻¹ * δ = torusChar ψ
    simp))
  exact hψ ▸ h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocEig
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

section LocEigAux

open UpperTheory.V.Hi UpperTheory.V.AlgebraTools

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

end LocEigAux
end
