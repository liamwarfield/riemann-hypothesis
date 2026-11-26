module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqMulOfValLtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitUnif

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_eq_mul (v : HeightOneSpectrum (𝓞 F)) (T b : 𝓞 F) (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2)
    (hb : b ∈ v.asIdeal) : ∃ c ∈ v.adicCompletionIntegers F,
      algebraMap F (v.adicCompletion F) (b : F) = algebraMap F (v.adicCompletion F) (T : F) * c := by
  have hT0 : T ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hle : v.intValuation b ≤ v.intValuation T := by
    have h3 := (v.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)
    refine h3.trans ?_
    by_contra h
    rw [not_le] at h
    apply h2
    rw [← v.intValuation_le_pow_iff_mem]
    have h0 : v.intValuation T ≠ 0 := v.intValuation_ne_zero _ hT0
    rw [← WithZero.exp_log h0] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega
  have hTF : (T : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hT0
  refine ⟨algebraMap F (v.adicCompletion F) ((b : F) / (T : F)), ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h := v.valuedAdicCompletion_eq_valuation' ((b : F) / (T : F))
    change Valued.v (((b : F) / (T : F) : F) : v.adicCompletion F) ≤ 1
    rw [h, map_div₀]
    have e1 : v.valuation F (b : F) = v.intValuation b := v.valuation_of_algebraMap b
    have e2 : v.valuation F (T : F) = v.intValuation T := v.valuation_of_algebraMap T
    rw [e1, e2]
    exact div_le_one_of_le₀ hle zero_le
  · rw [← map_mul, mul_div_cancel₀ _ hTF]

theorem incl_eq_mul [StarRing E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b ∈ P → b ∈ v.asIdeal) (T : 𝓞 F) (t t' : 𝓞 E)
    (ht' : (t' : E) = star (t : E)) (htt : t * t' = algebraMap (𝓞 F) (𝓞 E) T) (hco : IsCoprime t t') (ht : t ∈ P)
    (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2) (a : 𝓞 E) (ha : a ∈ P) :
    ∃ c ∈ intV E v, Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) * c := by
  have hO : ∀ r : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  have hF : ∀ x : F, Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E x) =
      (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) x := fun x => by
    change (algebraMap F E x) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  let a' : 𝓞 E := ⟨star (a : E), (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (RingHom.id ℤ) (starRingEnd E)
    (RingHom.ext_int _ _)⟩
  have ha' : (a' : E) = star (a : E) := rfl
  obtain ⟨b₀, hb₀⟩ := (hc.fixed ((t' * a + t * a' : 𝓞 E) : E)).1 (by
    change star ((t' : E) * (a : E) + (t : E) * star (a : E)) = (t' : E) * (a : E) + (t : E) * star (a : E)
    rw [ht', star_add, star_mul', star_mul', star_star, star_star, add_comm])
  have hint : IsIntegral ℤ b₀ := by
    rw [← isIntegral_algebraMap_iff (B := E), hb₀]
    exact RingOfIntegers.isIntegral_coe _
  let b : 𝓞 F := ⟨b₀, hint⟩
  have hb : algebraMap (𝓞 F) (𝓞 E) b = t' * a + t * a' := RingOfIntegers.ext hb₀
  obtain ⟨c, hc1, hc2⟩ := exists_eq_mul v T b h1 h2
    (hv b (by rw [hb]; exact add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ ht)))
  have hcV : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc1⟩, rfl⟩)
  obtain ⟨α, β, hαβ⟩ := hco
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι
  have e1 : ι t' * ι a + ι t * ι a' = ι t * ι t' * ((1 : E) ⊗ₜ[F] c) := by
    have l : ι t' * ι a + ι t * ι a' = ι (algebraMap F E (b : F)) := by
      rw [← map_mul ι, ← map_mul ι, ← map_add ι]
      exact congrArg ι hb₀.symm
    have r : ι t * ι t' = ι (algebraMap F E (T : F)) := by
      rw [← map_mul ι]
      exact congrArg (fun z : 𝓞 E => ι (z : E)) htt
    rw [l, r, hF, hF, hc2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have e2 : ι α * ι t + ι β * ι t' = 1 := by
    rw [← map_mul ι, ← map_mul ι, ← map_add ι, ← map_one ι]
    exact congrArg (fun z : 𝓞 E => ι (z : E)) hαβ
  refine ⟨ι α * ι a + ι β * (ι t' * ((1 : E) ⊗ₜ[F] c) - ι a'),
    add_mem (mul_mem (hO _) (hO _)) (mul_mem (hO _) (sub_mem (mul_mem (hO _) hcV) (hO _))), ?_⟩
  linear_combination (-(ι a)) * e2 + ι β * e1

end General


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eq_mul_of_val_lt_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (T : ℕ) (t t' : 𝓞 D.host.E), (t' : D.host.E) = star (t : D.host.E) → t * t' = (T : 𝓞 D.host.E) → IsCoprime t t' → t ∈ P.asIdeal → (T : 𝓞 D.host.F) ∈ p.v.asIdeal → (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2 → ∀ y : AE D, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) ∈ Formalism.BasicNotions.intV D.host.E p.v → valuation k (p.pr y) < 1 → ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  intro D k _ _ _ _ p P hP T t t' ht' htt hco ht h1 h2 y hy hval
  obtain ⟨π₀, hπ₀, -, -, hres⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP
  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h3 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h3
    exact h3.symm
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, Formalism.UG.P.afsplit_IE_int p.v _ hy⟩
  have hs : s ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := by
    rw [← Formalism.L2.DIV.resS_eq_zero_iff, hres]
    change valuation k (π₀ (Formalism.UG.P.afsplitIE p.v _)) < 1
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul, hπ₀]
    exact hval
  have hv : ∀ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ P.asIdeal → b ∈ p.v.asIdeal := fun b hb => by
    rw [GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under p hP]
    exact hb
  have key : ∀ z ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal, ∃ c ∈ intV D.host.E p.v,
      Formalism.UG.prV (E := D.host.E) p.v (z : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact incl_eq_mul D.sp.cm p.v P.asIdeal hv (T : 𝓞 D.host.F) t t' ht' (by rw [htt, map_natCast]) hco ht h1 h2 a ha
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc, ea⟩ := ha
      obtain ⟨d, hd, eb⟩ := hb
      exact ⟨c + d, add_mem hc hd, by rw [Subring.coe_add, map_add (f := _), ea, eb, mul_add]⟩
    | smul r a _ ha =>
      obtain ⟨c, hc, ea⟩ := ha
      exact ⟨Formalism.UG.prV (E := D.host.E) p.v r * c, mul_mem (Formalism.UG.P.afsplit_prV_int p.v _ r.2) hc, by
        rw [smul_eq_mul, Subring.coe_mul, map_mul, ea, mul_left_comm]⟩
  obtain ⟨c, hc, e⟩ := key s hs
  refine ⟨c, hc, ?_⟩
  rw [← e]
  exact (Formalism.UG.P.afsplit_prV_IE p.v _).symm

end GlobalTheory.LocMod.SplitUnif
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LastRow

theorem row_lt_of_smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M : Matrix (Fin n) (Fin n) k) (hb : b * b' = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hfix : g • Q = Q) (s : Fin n) :
    valuation k (M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, Q.fn x ≠ 0 := by
    by_contra h
    exact Q.fn_ne (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨y0, -, s0, hs0, ha0⟩ := (hQ x0.1 (Q.fn x0)).1 ⟨x0.2, rfl⟩
  have hu : residue 𝒪[k] s0 ≠ 0 := by
    intro h
    apply hx0
    rw [ha0, map_mul, h, zero_mul]
  let yE : Fin n → 𝒪[k] := Pi.single s 1
  have hyE : ∀ r, (yE r : k) = (Pi.single s 1 : Fin n → k) r := by
    intro r
    simp only [yE, Pi.single_apply]
    split_ifs <;> rfl
  have h1 : Q.HasVal (b' *ᵥ Pi.single s 1) (residue 𝒪[k] (s0 * yE r₀)) := by
    refine (hQ _ _).2 ⟨yE, fun r => ?_, s0, hs0, rfl⟩
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, hyE]
  have h2 : Q.HasVal (g • (b' *ᵥ (Pi.single s 1 : Fin n → k))) (residue 𝒪[k] (s0 * yE r₀)) := by
    rw [← hfix, GlobalTheory.LatPair.Pair.smul_hasVal, inv_smul_smul]
    exact h1
  obtain ⟨y1, hy1, s1, hs1, ha1⟩ := (hQ _ _).1 h2
  obtain rfl : s1 = s0 := Subtype.ext (hs1.trans hs0.symm)
  have hM : (y1 r₀ : k) = M r₀ s := by
    rw [hy1]
    change (b *ᵥ (g.val *ᵥ (b' *ᵥ (Pi.single s 1 : Fin n → k)))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg, Matrix.mulVec_single_one]
    rfl
  have h3 : residue 𝒪[k] (y1 r₀ - yE r₀) = 0 := by
    rw [map_mul, map_mul] at ha1
    rw [map_sub, mul_left_cancel₀ hu ha1, sub_self]
  have h4 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3))
  have h5 : ((y1 r₀ - yE r₀ : 𝒪[k]) : k) = M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s := by
    rw [AddSubgroupClass.coe_sub, hM, hyE, Pi.single_apply, Matrix.one_apply]
  rw [← h5]
  exact h4


set_option maxHeartbeats 1000000 in
theorem exists_gl {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {V : HSp D} (β : GlobalTheory.FinPl.Frame p V (Fin V.rank)) (κ : GA D V) :
    ∃ g : GL (Fin V.rank) k, (mt V κ).map p.pr = β.b * g.val * β.b' := by
  have hm : ∀ x y : GA D V, x * y = 1 → (mt V x).map p.pr * (mt V y).map p.pr = 1 := by
    intro x y h
    have e : mt V x * mt V y = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, h, map_one, Units.val_one]
    rw [← Matrix.map_mul, e]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ A A' : Matrix (Fin V.rank) (Fin V.rank) k, A * A' = 1 → (β.b' * A * β.b) * (β.b' * A' * β.b) = 1 := by
    intro A A' h
    calc (β.b' * A * β.b) * (β.b' * A' * β.b) = β.b' * (A * ((β.b * β.b') * A')) * β.b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [β.bb', Matrix.one_mul, h, Matrix.mul_one, β.b'b]
  refine ⟨⟨β.b' * (mt V κ).map p.pr * β.b, β.b' * (mt V κ⁻¹).map p.pr * β.b, hc _ _ (hm _ _ (mul_inv_cancel κ)),
    hc _ _ (hm _ _ (inv_mul_cancel κ))⟩, ?_⟩
  calc (mt V κ).map p.pr = (β.b * β.b') * (mt V κ).map p.pr * (β.b * β.b') := by rw [β.bb', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]


set_option maxHeartbeats 2000000 in
theorem entry_cong (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (T : ℕ)
    (t t' : 𝓞 D.host.E) (h1 : (t' : D.host.E) = star (t : D.host.E)) (h2 : t * t' = (T : 𝓞 D.host.E)) (h3 : IsCoprime t t')
    (h4 : t ∈ P.asIdeal) (h5 : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h6 : (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (r s : Fin n)
    (hi : Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E p.v)
    (hl : valuation k (((mt V κ).map p.pr) ((finCongr hn).symm r) ((finCongr hn).symm s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) k) ((finCongr hn).symm r) ((finCongr hn).symm s)) < 1) :
    ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  subst hn
  let y : AE D := mt V κ r s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s
  have hy : Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s := by
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h7 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← hy]
  refine GlobalTheory.LocMod.SplitUnif.eq_mul_of_val_lt_one D k p P hP T t t' h1 h2 h3 h4 h5 h6 y ?_ ?_
  · rw [hy]
    refine Subring.sub_mem _ hi ?_
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [y]
    rw [map_sub, h7]
    exact hl

end GlobalTheory.FamTrace.LastRow


end
