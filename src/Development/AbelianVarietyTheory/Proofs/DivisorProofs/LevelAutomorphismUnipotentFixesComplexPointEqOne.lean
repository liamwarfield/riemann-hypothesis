module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphism

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelian
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.MoveOrder

theorem finite_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c γ ρ ν hpq hl hρ hm
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  obtain ⟨⟨ι, hι, -⟩, hmul, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  have h₀ : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  have key : ∀ k : ℕ, ∃ (ρk : Xo.X ⟶ Xo.X) (μ : SABMap Xo.univ.t Xo.univ.t ρk), IsIso ρk ∧
      IsLevMove ρk μ (liftLa («γ» ^ k)) LinearMap.id ∧
      μ.φ = (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[k] (𝟙 _) := by
    intro k
    induction k with
    | zero => exact ⟨𝟙 _, ι, inferInstance, by rw [pow_zero]; exact h₀, by rw [hι]; rfl⟩
    | succ k ih =>
      obtain ⟨ρk, μ, ik, hk, hφ⟩ := ih
      obtain ⟨κ, hκ, -⟩ := hmul ρk ρ μ ν
      refine ⟨ρk ≫ ρ, κ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, ?_⟩
      · rw [Category.assoc, hm.1, hk.1]
      · rw [pow_succ, GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub («γ» ^ k) «γ» a), hκ,
          ← Category.assoc, hk.2.1, Category.assoc, hm.2.1, Category.assoc]
      · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
            (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
        rw [e, hκ, ← Category.assoc, hk.2.2, Category.assoc, hm.2.2, Category.assoc]
      · rw [hκ, hφ, Function.iterate_succ_apply']
  refine ⟨orderOf «γ», orderOf_pos «γ», ?_⟩
  obtain ⟨ρn, μ, i, h, hφ⟩ := key (orderOf «γ»)
  rw [pow_orderOf_eq_one] at h
  rw [← hφ, (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h h₀).2, hι]

end GlobalTheory.MoveOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelianStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.MoveOrder.finite_order | exact GlobalTheory.MoveOrder.finite_order | (intros; apply GlobalTheory.MoveOrder.finite_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem unipAt_inv_liftLa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  intro E _ _ _ H Dw l I γ hI hU
  obtain ⟨m, hm⟩ := hU
  set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef
  set f := liftLa γ with hfdef
  set g := liftLa γ⁻¹ with hgdef
  have hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M := Submodule.smul_mono_left hI
  have hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ := by
    intro φ
    rw [← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hgf : ∀ x, g (f x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec (γ⁻¹) (f x)
    have h2 := liftLa_spec γ x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hgdef, h1, hfdef, h2]
    exact γ.symm_apply_apply _
  have hfg : ∀ x, f (g x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec γ (g x)
    have h2 := liftLa_spec (γ⁻¹) x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hfdef, h1, hgdef, h2]
    exact γ.apply_symm_apply _
  let A := M.mapQ M f (hpres f)
  let B := M.mapQ M g (hpres g)
  have hBA : B * A = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hgf x)
  have hAB : A * B = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hfg x)
  have hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La),
      M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x) := by
    intro φ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
  have hA0 : (A - 1) ^ m = 0 := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm x
  have hcomm : Commute B (1 - A) := by
    refine Commute.sub_right (Commute.one_right B) ?_
    exact (hBA.trans hAB.symm)
  have hB0 : (B - 1) ^ m = 0 := by
    have e : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
    rw [e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]
  refine ⟨m, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]

end GlobalTheory.OrbitSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInvStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnipotentModIdeal_liftLa_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  first | exact @GlobalTheory.OrbitSep.unipAt_inv_liftLa | exact GlobalTheory.OrbitSep.unipAt_inv_liftLa | (intros; apply GlobalTheory.OrbitSep.unipAt_inv_liftLa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmul
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.TateTorsion


open NumberField in
theorem _root_.GlobalTheory.TateTorsion.torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  intro E _ _ _ H Dw l k _ Q _ act e T eta I g hadd hone hnat heta hg hI hsq hle
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.prime_iff.mp hg).irreducible
  have hne : I ≠ ⊥ := by
    rintro rfl
    simp only [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  obtain ⟨B, hB⟩ : I ∣ Ideal.span {(g : 𝓞 E)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hgI)
  have hIB : I ⊔ B = ⊤ := by
    by_contra h
    have hBI : B ≤ I := (hmax.eq_of_le h le_sup_left).symm ▸ le_sup_right
    apply hsq
    have hgB : (g : 𝓞 E) ∈ I * B := hB ▸ Ideal.mem_span_singleton_self _
    rw [pow_two]
    exact Ideal.mul_mono_right hBI hgB
  have hIbar : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ :=
    eq_top_iff.mpr (l.coprime ▸ sup_le_sup_right hle _)
  have hIK : I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIB hIbar ⊢
    exact hIbar.mul_right hIB
  obtain ⟨i, hi, u, hu, hiu⟩ :=
    Submodule.mem_sup.mp (hIK ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * B)
  have huB : u ∈ B := Ideal.mul_le_right hu
  have huBar : u ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_le_left hu
  have hgN : g ∣ l.M := by
    have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr (hle hMb))
    have h' : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [hI, Ideal.absNorm_span_singleton, h', Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast] at h
    exact hg.dvd_of_dvd_pow h
  obtain ⟨m, hm⟩ := hgN
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; have := l.three_le; omega)
  have key : ∀ j ∈ I, (m : 𝓞 E) * u * j ∈ l.Mb := by
    intro j hj
    have h : u * j ∈ Ideal.span {(g : 𝓞 E)} := hB ▸ (mul_comm j u ▸ Ideal.mul_mem_mul hj huB)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    have h2 : (m : 𝓞 E) * u * j = r * (l.M : 𝓞 E) := by
      rw [mul_assoc, ← hr, hm]; push_cast; ring
    rw [h2]
    exact Ideal.mul_mem_left _ r hMb
  refine ⟨(m : 𝓞 E) * u, ?_, ?_⟩
  · intro c hc
    refine Submodule.smul_induction_on hc (fun j hj y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul]
      exact Submodule.smul_mem_smul (key j hj) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hz
  · intro x hx
    have hxg : x ^ g = 1 := by rw [← hnat]; exact hx _ hgI
    obtain ⟨b, hb⟩ := (T.onto g hg.pos x).mp hxg
    have hpow : ∀ (n j : ℕ) (a : Dw.La), T.ev n (j • a) = T.ev n a ^ j := by
      intro n j a
      induction j with
      | zero =>
        have h := T.add n 0 0
        rw [add_zero] at h
        simpa using h
      | succ j ih => rw [succ_nsmul, T.add, ih, pow_succ]
    have hux : act u x = x := by
      have h := hone x
      rwa [← hiu, hadd, hx i hi, one_mul] at h
    refine ⟨b, ?_⟩
    have hmem : ((m : 𝓞 E) * u) • b ∈
        l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ huBar) Submodule.mem_top
    rw [heta _ hmem, mul_comm, mul_smul, T.lin, Nat.cast_smul_eq_nsmul, hpow, hm,
      T.tower g m hg.pos hm0, hb, hux]

end GlobalTheory.TateTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIsometry_torsion_eq_level_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (T : TateIso Dw k Q act e) (eta : Dw.La → Q) (I : Ideal (𝓞 E)) (g : ℕ), (∀ a b x, act (a + b) x = act a x * act b x) → (∀ x, act 1 x = x) → (∀ (n : ℕ) x, act (n : 𝓞 E) x = x ^ n) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), eta a = T.ev l.M a) → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → l.Mb ≤ I → ∃ t : 𝓞 E, (∀ c ∈ I • (⊤ : Submodule (𝓞 E) Dw.La), t • c ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ ∀ x : Q, (∀ a ∈ I, act a x = 1) → ∃ c : Dw.La, x = eta (t • c) := by
  first | exact @GlobalTheory.TateTorsion.torsion_eq_level_smul | exact GlobalTheory.TateTorsion.torsion_eq_level_smul | (intros; apply GlobalTheory.TateTorsion.torsion_eq_level_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrank
open NumberField

namespace GlobalTheory


open TensorProduct in
theorem natCard_quot_maximal_smul_top_eq {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

theorem natCard_quot_smul_top_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La →
    ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g →
    Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧
      Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  intro E _ _ La _ _ hfin hproj I g hg hI
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact hg.prime.irreducible)
  have hne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hI
    exact hg.ne_zero hI.symm
  have hmax : I.IsMaximal := hprime.isMaximal hne
  have hR : Nat.card (𝓞 E ⧸ I) = g := by
    rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard := natCard_quot_maximal_smul_top_eq (R := 𝓞 E) (M := La) I
  rw [hR] at hcard
  refine ⟨?_, hcard.le⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hg.ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrankStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_quot_smul_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La → ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g → Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧ Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  first | exact @GlobalTheory.natCard_quot_smul_top_le_pow_finrank | exact GlobalTheory.natCard_quot_smul_top_le_pow_finrank | (intros; apply GlobalTheory.natCard_quot_smul_top_le_pow_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOne
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.UnipFree

theorem free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ «γ» : LevelAut Dw l, UnipAt I «γ» → ∀ y : FrPt Xo c ℂ, ptF (move Xo c «γ» y) = ptF y → «γ» = 1 := by
  intro E _ _ _ H Dw l Xo c hpq hA1 I g hN hMb «γ» hU y hy
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨ρ, ν, hiso, hm, hf⟩ := GlobalTheory.LevDesc.levR_move (Xo := Xo) (c := c) hpq hA «γ» y
  have hm' : IsLevMove ρ ν (liftLa «γ») LinearMap.id := hm
  have hx : y.x ≫ ρ = y.x := by
    have e := congrArg (· ≫ pullback.fst _ _) hy
    simp only [GlobalTheory.AllWt.ptF, pullback.lift_fst] at e
    rw [← hf.1]; exact e
  obtain ⟨hg, hnorm, hsq, hr⟩ := hN
  set x := y.x with hxdef
  set G := Xo.univ.t.G with hGdef
  let G0 : Over (Sp ℂ) := (Over.pullback x).obj G
  let act0 : OAct (𝓞 E) G0 := OAct.pullback x G Xo.univ.t.act
  have w : (pullback.fst G.hom x ≫ ν.φ) ≫ G.hom = pullback.snd G.hom x ≫ x := by
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc, hx]
  let α : G0 ⟶ G0 := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ ν.φ) (pullback.snd G.hom x) w)
    (pullback.lift_snd _ _ _)
  have hαf : α.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ ν.φ := pullback.lift_fst _ _ _
  have pA : IsGrpPullback G0 G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have c₁ : IsGrpPullback G0 G x (pullback.fst G.hom x ≫ ν.φ) := by
    have c₀ := IsGrpPullback.comp pA ν.cart
    rw [hx] at c₀
    exact c₀
  have hαm : IsMonHom α :=
    ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pA (𝟙 G) α (by simpa using hαf)
  have hact0 : ∀ a, (act0.act a).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (Xo.univ.t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have hact : ∀ a, act0.act a ≫ α = α ≫ act0.act a := fun a => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · calc (act0.act a ≫ α).left ≫ pullback.fst G.hom x
          = (act0.act a).left ≫ (α.left ≫ pullback.fst G.hom x) := by rw [Over.comp_left, Category.assoc]
        _ = ((act0.act a).left ≫ pullback.fst G.hom x) ≫ ν.φ := by rw [hαf, Category.assoc]
        _ = pullback.fst G.hom x ≫ ((Xo.univ.t.act.act a).left ≫ ν.φ) := by rw [hact0, Category.assoc]
        _ = pullback.fst G.hom x ≫ (ν.φ ≫ (Xo.univ.t.act.act a).left) :=
          congrArg (pullback.fst G.hom x ≫ ·) (ν.act a)
        _ = (α.left ≫ pullback.fst G.hom x) ≫ (Xo.univ.t.act.act a).left := by rw [hαf, Category.assoc]
        _ = α.left ≫ ((act0.act a).left ≫ pullback.fst G.hom x) := by rw [hact0, Category.assoc]
        _ = (α ≫ act0.act a).left ≫ pullback.fst G.hom x := by rw [Over.comp_left, Category.assoc]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      simp only [Over.comp_left, Category.assoc, h1]
  obtain ⟨n, hn, hνn⟩ := GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian E H Dw l Xo c «γ» ρ ν hpq hA1 hiso hm'
  have hαn : (fun f => f ≫ α)^[n] (𝟙 G0) = 𝟙 G0 := by
    have key : ∀ j, ((fun f => f ≫ α)^[j] (𝟙 G0)).left ≫ pullback.fst G.hom x =
        pullback.fst G.hom x ≫ (fun f : G.left ⟶ G.left => f ≫ ν.φ)^[j] (𝟙 _) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Over.comp_left, Category.assoc, hαf,
          ← Category.assoc, ih, Category.assoc]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key, hνn, Over.id_left, Category.id_comp, Category.comp_id]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      rw [h1]; simp

  have bw : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (u.left ≫ pullback.fst G.hom x) ≫ G.hom = (Over.mk x).hom := fun u => by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have e : u.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w u
    rw [e, Category.id_comp]; rfl
  let B : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (Over.mk x ⟶ G) := fun u => Over.homMk (u.left ≫ pullback.fst G.hom x) (bw u)
  have B_left : ∀ u, (B u).left = u.left ≫ pullback.fst G.hom x := fun u => rfl
  have B_inj : Function.Injective B := fun u v h => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun z => z.left) h
    · exact (Over.w u).trans (Over.w v).symm
  have B_mul : ∀ u v, B (u * v) = B u * B v := fun u v => by
    apply Over.OverMorphism.ext
    have e1 := pA.2 (𝟙_ _) u v (pushPt pA.1.w u) (pushPt pA.1.w v) rfl rfl
    have e2 := mul_left_congr (Category.id_comp x) (pushPt pA.1.w u) (pushPt pA.1.w v) (B u) (B v) rfl rfl
    exact e1.symm.trans e2
  let Bh : (𝟙_ (Over (Sp ℂ)) ⟶ G0) →* (Over.mk x ⟶ G) := MonoidHom.mk' B B_mul
  have B_act : ∀ u a, B (u ≫ act0.act a) = B u ≫ Xo.univ.t.act.act a := fun u a => by
    apply Over.OverMorphism.ext
    rw [B_left, Over.comp_left, Over.comp_left, B_left, Category.assoc, Category.assoc, hact0]
  have B_α : ∀ u, (B (u ≫ α)).left = (B u).left ≫ ν.φ := fun u => by
    rw [B_left, B_left, Over.comp_left, Category.assoc, hαf, Category.assoc]
  have B_one : B 1 = 1 := map_one Bh

  have tl : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  let β : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨-, TI, -, -, hTI⟩ := Xo.univ.geom ℂ x β y.x_over
  let et : Dw.La → (Over.mk x ⟶ G) := fun b => toUnit (Over.mk x) ≫ Xo.univ.eta b
  have et_add : ∀ a b, et (a + b) = et a * et b := fun a b => by
    simp only [et, Xo.univ.eta_add, MonObj.comp_mul]
  have et_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), et a = 1 := fun a ha => by
    simp only [et, Xo.univ.eta_ker a ha, MonObj.comp_one]
  have hadd : ∀ (a b : 𝓞 E) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (a + b) =
      (z ≫ Xo.univ.t.act.act a) * (z ≫ Xo.univ.t.act.act b) := fun a b z => by
    rw [Xo.univ.t.act.add, MonObj.comp_mul]
  have hone : ∀ z : Over.mk x ⟶ G, z ≫ Xo.univ.t.act.act 1 = z := fun z => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hnat : ∀ (k : ℕ) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (k : 𝓞 E) = z ^ k := by
    intro k z
    induction k with
    | zero =>
      have h0 := hadd 0 0 z
      rw [add_zero] at h0
      simpa using h0
    | succ k ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  obtain ⟨t, ht, htor⟩ := GlobalTheory.T.tateIsometry_torsion_eq_level_smul E H Dw l ℂ (Over.mk x ⟶ G) (fun a z => z ≫ Xo.univ.t.act.act a) _ TI et I g
    hadd hone hnat (fun a ha => hTI a ha) hg hnorm hsq hMb

  have tor_B : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → ∃ c' : Dw.La, B u = et (t • c') :=
    fun u hu => htor (B u) fun a ha => by rw [← B_act, hu a ha, B_one]
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.natCard_quot_smul_le_pow_finrank E Dw.La Dw.fin Dw.proj I g hg hnorm
  classical
  haveI : Fintype (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule (𝓞 E) Dw.La)))
  let S' : Finset (Over.mk x ⟶ G) := Finset.univ.image fun q => et (t • rep q)
  have et_t : ∀ c', et (t • c') ∈ S' := fun c' => by
    refine Finset.mem_image.2 ⟨Submodule.Quotient.mk c', Finset.mem_univ _, ?_⟩
    have e : rep (Submodule.Quotient.mk c') - c' ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)
    have e2 := ht _ e
    rw [smul_sub] at e2
    have e3 : et (t • rep (Submodule.Quotient.mk c')) =
        et (t • rep (Submodule.Quotient.mk c') - t • c') * et (t • c') := by
      rw [← et_add, sub_add_cancel]
    rw [e3, et_ker _ e2, _root_.one_mul]
  let T0 : Finset (𝟙_ (Over (Sp ℂ)) ⟶ G0) := S'.preimage B B_inj.injOn
  have hT0 : T0.card ≤ g ^ (Dw.p + Dw.q) := by
    calc T0.card ≤ S'.card :=
          Finset.card_le_card_of_injOn B (fun u hu => Finset.mem_preimage.1 hu) B_inj.injOn
      _ ≤ (Finset.univ : Finset (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La))).card := Finset.card_image_le
      _ = Nat.card (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ g ^ (Dw.p + Dw.q) := by rw [← Dw.rank]; exact hcard
  have hmemT : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → u ∈ T0 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    exact Finset.mem_preimage.2 (hc' ▸ et_t c')

  obtain ⟨m, hmU⟩ := GlobalTheory.T.isUnipotentModIdeal_liftLa_inv E H Dw l I «γ» hMb hU
  have hδ : ∀ b, et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et b := fun b => by
    have e1 := GlobalTheory.LevelActionLaws.liftLa_mul_sub «γ» «γ»⁻¹ b
    have e2 := GlobalTheory.LevelActionLaws.liftLa_one_sub (D := Dw) (l := l) b
    rw [mul_inv_cancel] at e1
    have e3 : liftLa «γ» (liftLa «γ»⁻¹ b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have e4 := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at e4
    have e5 : et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et (liftLa «γ» (liftLa «γ»⁻¹ b) - b) * et b := by
      rw [← et_add, sub_add_cancel]
    rw [e5, et_ker _ e3, _root_.one_mul]
  have B_step : ∀ u b, B u = et b → B (u ≫ α) = et (liftLa «γ»⁻¹ b) := fun u b hb => by
    apply Over.OverMorphism.ext
    rw [B_α, hb, ← hδ b]
    show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» (liftLa «γ»⁻¹ b))).left ≫ ν.φ =
      (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ»⁻¹ b)).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
  let φf : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (𝟙_ (Over (Sp ℂ)) ⟶ G0) := fun z => (z ≫ α) * z⁻¹
  have B_iter : ∀ j u b, B u = et b → B (φf^[j] u) = et (((liftLa «γ»⁻¹ - 1) ^ j) b) := by
    intro j
    induction j with
    | zero => intro u b hb; simpa using hb
    | succ j ih =>
      intro u b hb
      rw [Function.iterate_succ_apply']
      have h1 := ih u b hb
      set b' := ((liftLa «γ»⁻¹ - 1) ^ j) b
      show Bh ((φf^[j] u ≫ α) * (φf^[j] u)⁻¹) = _
      rw [map_mul, map_inv]
      show B (φf^[j] u ≫ α) * (B (φf^[j] u))⁻¹ = _
      rw [B_step _ _ h1, h1, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rw [eq_comm, eq_mul_inv_iff_mul_eq, ← et_add, sub_add_cancel]
  have hunip : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) →
      (fun z : 𝟙_ (Over (Sp ℂ)) ⟶ G0 => (z ≫ α) * z⁻¹)^[m] u = 1 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    apply B_inj
    rw [B_iter m u _ hc', B_one, map_smul]
    exact et_ker _ (ht _ (hmU c'))
  have hαid : α = 𝟙 G0 := GlobalTheory.T.exists_small_torsion_set_for_endomorphism E ℂ G0 act0 α n m g (Dw.p + Dw.q) I
    (IsSemiAbelian.pullback x G Xo.univ.t.semi) hαm hact hn hαn hg hnorm hsq hr ⟨T0, hT0, hmemT⟩ hunip

  have hαl : α.left = 𝟙 _ := by rw [hαid]; rfl
  have fix : ∀ s : Over.mk x ⟶ G, s.left ≫ ν.φ = s.left := fun s => by
    have hs : s.left ≫ G.hom = 𝟙 (Sp ℂ) ≫ x := by rw [Category.id_comp]; exact Over.w s
    have e0 : pullback.lift s.left (𝟙 _) hs ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
    rw [← e0, Category.assoc, ← hαf, hαl, Category.id_comp]
  have heq : ∀ a, liftLa «γ» a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
    refine GlobalTheory.LevelFree.eta_injective Xo x β y.x_over _ ?_
    have e1 : et (liftLa «γ» a) = et a := by
      apply Over.OverMorphism.ext
      rw [← fix (et (liftLa «γ» a))]
      show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» a)).left ≫ ν.φ =
        (toUnit (Over.mk x) ≫ Xo.univ.eta a).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
    have e2 : et (liftLa «γ» a) = et (liftLa «γ» a - a) * et a := by rw [← et_add, sub_add_cancel]
    rw [e1] at e2
    exact mul_eq_right.1 e2.symm
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e := liftLa_spec «γ» a
  simp only [Submodule.mkQ_apply] at e
  change «γ» (Submodule.Quotient.mk a) = Submodule.Quotient.mk a
  rw [← e]
  exact (Submodule.Quotient.eq _).2 (heq a)

end GlobalTheory.UnipFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ γ : LevelAut Dw l, UnipAt I γ → ∀ y : FrPt Xo c ℂ, ptF (move Xo c γ y) = ptF y → γ = 1 := by
  first | exact @GlobalTheory.UnipFree.free | exact GlobalTheory.UnipFree.free | (intros; apply GlobalTheory.UnipFree.free <;> assumption)
end
