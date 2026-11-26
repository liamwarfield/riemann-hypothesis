module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.MinNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewVec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace UpperTheory.V.Z.Kato.NewVec

open UpperTheory.V.Sd

private theorem comp_zero {V : Type} [AddCommGroup V] [Module ℂ V] {U W : Submodule ℂ V} (hd : Disjoint U W) (T : Module.End ℂ V)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) {φ ψ : V} (hψ : ψ ∈ U) (hm : φ - ψ ∈ W) (h0 : T φ = 0) : T ψ = 0 := by
  refine Submodule.disjoint_def.1 hd _ (hU _ hψ) ?_
  have := W.neg_mem (hW _ hm)
  rwa [map_sub, h0, zero_sub, neg_neg] at this

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private theorem eop_mem {U : Submodule ℂ (TR.Sm ℚ 2)} (hU : TR.IsStable U) (v : InfinitePlace ℚ) (i j : Fin 2) :
    ∀ x ∈ U, TR.Eop v i j x ∈ U := fun x hx => hU (.lie _) x hx

private theorem eop_one (v : InfinitePlace ℚ) (φ : TR.Sm ℚ 2) :
    TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = TR.lie ℚ 2 (TR.oneL ℚ 2) φ := by
  classical
  rw [TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
  congr 2
  ext i j w
  obtain rfl : w = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp

theorem newVec : Published.CuspSemisimpleReal → Published.AdmissibleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k), ∃ (π₀ : TR.CuspSub ℚ 2) (ψ : TR.Sm ℚ 2), ψ ∈ π₀.V ∧ ψ ≠ 0 ∧ (∀ q : HeightOneSpectrum (𝓞 ℚ), ψ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))) ∧ ((∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = (Complex.I * (k : ℂ)) • ψ) ∧ (∀ v, TR.Eop v 0 0 ψ - TR.Eop v 1 1 ψ = Complex.I • (TR.Eop v 0 1 ψ + TR.Eop v 1 0 ψ)) ∧ (∀ v, TR.Eop v 0 0 ψ + TR.Eop v 1 1 ψ = 0)) ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M) := by
  intro hS hA k hk2 f
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  have hLift : LiftHol := by
    intro k M hM χ ω hω f hf
    obtain ⟨φ₀, hφ⟩ := liftEx k M hM f fun δ hδ =>
      SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
    obtain ⟨hl, hr, hs⟩ := liftSm k M hM f φ₀ hφ
    let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
    have hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ :=
      fun u hu => Subtype.ext (funext (hr u hu))
    have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
      isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)
    have hc := liftCent k M hM χ ω hω f hf φ₀ hφ
    have hlie := liftLie k M hM f f.holo' φ hφ
    obtain ⟨C, hC⟩ := archBd k M hM f
    have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK k M hM f φ hφ,
      zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2),
      fun g => ⟨C, 0, fun y => by
        obtain ⟨γ, h, u, hu, e⟩ := decomp M hM (g * TR.infGL ℚ 2 y)
        rw [pow_zero, mul_one, e]
        change ‖φ₀ _‖ ≤ C
        rw [hφ γ h u hu]
        exact hC _ h.det_ne_zero⟩⟩
    exact ⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc,
      fun v => (hlie v).1, fun v => (hlie v).2⟩, haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩
  obtain ⟨φ, hL, hH, hC⟩ := hLift k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨h1, -⟩ := holCap ℚ k _ ω hfin φ hH
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split ℚ 2 φ h0 (hS ℚ 2 φ hC ⟨0, by rw [h1, zero_smul]⟩)
  have hπ : TR.IsStable π.V := π.stable
  refine ⟨π, ψ.1, ψ.2, fun e => hψ (Subtype.ext e), fun q u hu => ?_, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩, fun w hw => ?_⟩
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (locSm ℚ q u - 1 : Module.End ℂ _) x ∈ U :=
      fun U hU x hx => U.sub_mem (hU (.fin (locGL ℚ 2 q u)) x hx) hx
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.level q u hu)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2))) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)) (U.smul_mem _ hx)
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.wt v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0)) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx))
        (U.smul_mem _ (U.add_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)))
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.low v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 + Eo v 1 1) x ∈ U :=
      fun U hU x hx => U.add_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)
    exact comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm ((eop_one v φ).trans h1)
  · have hc := (places w).2.2.2 f.M hM hw
    obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
    obtain ⟨c₀, h3⟩ := h2 _ _ hE
    have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
      fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
    rw [hc, neg_smul, add_neg_eq_zero] at h4
    obtain ⟨α, β, hv, hsum, hprod⟩ := satHol ℚ k _ ω φ hH h0 w _ hc h4
    exact ⟨α, β, satOfVec hA ℚ 2 π w ψ _ (satComp ℚ φ π ψ W hψ hW hd hm w _ hv), hsum, by rw [hprod, hval w hw]⟩

end UpperTheory.V.Z.Kato.NewVec
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MemKLevOneOfMemK1G
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevelInv

open UpperTheory.V.Af.GlobalFixedVectors Matrix

theorem fixed_of_loc {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (v : V) (ho : IsOpen {k | ρ k v = v}) :
    ∀ k ∈ KLev F 2 1, (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
  classical
  have key : ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 1 T, ρ k v = v) → ∀ k ∈ KLev F 2 1,
      (∀ w ∈ T, w ∉ S → GeneralLinearGroup.map (pLoc F w) k = 1) →
      (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
    intro S T hT
    induction S using Finset.induction_on with
    | empty => exact fun k hk h1 _ => hT k (mem_KAway.2 ⟨hk, fun w hw => h1 w hw (by simp)⟩)
    | insert w S hw ih =>
      intro k hk h1 h
      have h2 := ih (k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹) (mul_mem hk (inv_mem (loc_mem w hk)))
        (fun u hu huS => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simp [pLoc_locGL_of_ne huw, h1 u hu (by simp [huw, huS])])
        (fun u => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simpa [pLoc_locGL_of_ne huw] using h u)
      have h3 := h w
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h2
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (ho.mem_nhds (by simp))
  exact fun k hk h => key S S (fun k hk => hS hk) k hk (fun w hw hw' => absurd hw hw') h

theorem local_mem_principal_congruence {N : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hM : (N : w.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c)
    {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : GeneralLinearGroup.map (pLoc ℚ w) k ∈ UpperTheory.V.Sd.K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat ℚ →+* w.adicCompletionIntegers ℚ :=
    ((pLoc ℚ w).comp (Ohat ℚ).subtype).codRestrict (w.adicCompletionIntegers ℚ) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  let q := Ideal.quotientMap (I := Ideal.span {(N : ↥(Ohat ℚ))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
  have h0 : ![0, 1] ᵥ* (g.val.map (Ideal.Quotient.mk (Ideal.span {(N : ↥(Ohat ℚ))}))) = ![0, 1] := hg
  change ![0, 1] ᵥ* ((g.val.map p).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c))) = ![0, 1]
  funext j
  have h1 := congrArg q (congrFun h0 j)
  have h2 : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (p x) := fun x => rfl
  fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, h2] using h1

theorem mem_KLev_one_of_mem_K1G (N : ℕ) {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : k ∈ KLev ℚ 2 1 := by
  obtain ⟨g, -, rfl⟩ := hk
  refine ⟨g, ?_, rfl⟩
  haveI : Subsingleton (↥(Ohat ℚ) ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat ℚ))}) := Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact MonoidHom.mem_ker.2 (Units.ext (Subsingleton.elim _ _))

theorem nat_mem_loc {F : Type} [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) (c : ℕ) {N : ℕ}
    (h4 : (N : 𝓞 F) ∈ q.asIdeal ^ c) :
    (N : q.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers F) ^ c := by
  have h5 : q.asIdeal.map (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) ≤ IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (q.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (q.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (q.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q _).trans_lt ((q.valuation_lt_one_iff_mem x).2 h1)
    exact h2
  rw [← map_natCast (algebraMap (𝓞 F) (q.adicCompletionIntegers F))]
  have h6 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) h4
  rw [Ideal.map_pow] at h6
  exact Ideal.pow_right_mono h5 _ h6

theorem nat_mem {M : ℕ} {w q : HeightOneSpectrum (𝓞 ℚ)} (hM : 1 ≤ M) (hd : normV w ∣ M) (hq : q ≠ w) :
    ((M / normV w : ℕ) : q.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ^ lev M q := by
  obtain ⟨N, hN⟩ := hd
  obtain ⟨hp, hw, -, -⟩ := places w
  have e : M / normV w = N := by rw [hN, Nat.mul_div_cancel_left _ hp.pos]
  rw [e]
  have hM0 : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  have h1 : q.asIdeal ^ lev M q ∣ Ideal.span {(M : 𝓞 ℚ)} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hM0) q.associates_irreducible]
    exact le_rfl
  have h2 : Ideal.span {(M : 𝓞 ℚ)} = w.asIdeal * Ideal.span {(N : 𝓞 ℚ)} := by
    rw [hw, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hN]
  rw [h2] at h1
  have h3 : q.asIdeal ^ lev M q ∣ Ideal.span {(N : 𝓞 ℚ)} :=
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.2 (q.isMaximal.coprime_of_ne w.isMaximal
      fun h => hq (HeightOneSpectrum.ext h)))).dvd_of_dvd_mul_left h1
  have h4 : (N : 𝓞 ℚ) ∈ q.asIdeal ^ lev M q := Ideal.dvd_span_singleton.1 h3
  exact nat_mem_loc q _ h4

theorem inv_K1G : ∀ (M : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), 1 ≤ M → normV w ∣ M → ∀ φ : TR.Sm ℚ 2, IsOpen {u | TR.finRep ℚ 2 u φ = φ} → (∀ q, q ≠ w → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev M q))) → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ w) (UpperTheory.V.Sd.K1 w 0) → ∀ u ∈ K1G (M / normV w), TR.finRep ℚ 2 u φ = φ := by
  intro M w hM hd φ ho hq hw u hu
  refine fixed_of_loc _ φ ho u (mem_KLev_one_of_mem_K1G _ hu) fun q => ?_
  by_cases h : q = w
  · subst h
    exact hw _ (local_mem_principal_congruence q 0 (by simp) hu)
  · exact hq q h _ (local_mem_principal_congruence q _ (nat_mem hM hd h) hu)

end GlobalTheory.NewLevelInv

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MultisetEqOfProdEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevel

private theorem ev_not_dvd_norm {a : ℕ} (h : a ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem multiset_eq_of_prod_eq {c : ℂ} (hc : c ≠ 0) {B B' : Multiset ℂˣ}
    (h : (B.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod =
      (B'.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod) : B = B' := by
  have e : ∀ D : Multiset ℂˣ, (D.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod.roots =
      D.map fun b : ℂˣ => c * (b : ℂ) := fun D => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (D.map fun b : ℂˣ => c * (b : ℂ)), Multiset.map_map]
    rfl
  have h1 := (e B).symm.trans ((congrArg Polynomial.roots h).trans (e B'))
  exact Multiset.map_injective (fun a b hab => Units.ext (mul_left_cancel₀ hc hab)) h1

private theorem algSat_prod (q : ℕ) (t : ℂ) (B : Multiset ℂˣ) :
    ((algSat 2 q B).map fun b => Polynomial.X - Polynomial.C (t * b)).prod =
      (B.map fun b : ℂˣ => Polynomial.X -
        Polynomial.C ((t * (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) * (b : ℂ))).prod := by
  induction B using Multiset.induction_on with
  | empty => simp [algSat]
  | cons a B ih =>
    simp only [algSat, Multiset.map_cons, Multiset.prod_cons, Multiset.pure_def, Multiset.bind_def,
      Multiset.cons_bind, Multiset.singleton_add] at ih ⊢
    rw [ih, mul_assoc]

theorem spherical_of_normTwist : Published.StrongMultOneReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π π₀ : TR.CuspSub ℚ 2), (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧ ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) → (∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M)) → ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (Bs : Multiset ℂˣ), π.HasSat w Bs → ∃ B, π₀.HasSat w B := by
  intro hS k hk g j π π₀ hπ hπ₀ w Bs hBs
  have hk1 : 1 ≤ k := by omega
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ s
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ s
  have hM : g.M ≠ 0 := by have : 1 ≤ g.M := g.pos; omega
  have hiso : π.Iso (π₀.twist χ) := by
    refine hS ℚ 2 one_le_two π _ ?_
    filter_upwards [hπ, ev_not_dvd_norm hM] with q hq hd
    obtain ⟨B, hB, hpoly⟩ := hq
    obtain ⟨α, β, hv, hsum, hprod⟩ := hπ₀ q hd
    have htw := hv.twist (χ := χ) (hE.1 q)
    refine ⟨B, hB, ?_⟩
    have hq : Ideal.absNorm q.asIdeal = normV q := (places q).2.2.1
    have hq0 : (0 : ℝ) < normV q := by exact_mod_cast (places q).1.pos
    have hval : ((χ.val q : ℂˣ) : ℂ) = (((normV q : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [hE.2.1 q, hq, Complex.ofReal_cpow hq0.le]; simp
    set r : ℂ := (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have key : ∀ a : ℂˣ, ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) *
        ((a * χ.val q : ℂˣ) : ℂ) = r * a := fun a => by
      have : ((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
          (normV q : ℝ) ^ j * ((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV q : ℝ) ^ (-s)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        rw [hs]; push_cast; ring
      rw [hr, this, Units.val_mul, hval]; push_cast; ring
    have hrr : r * r = (normV q : ℂ) ^ (k - 1) := by
      rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
      push_cast; rfl
    have hc : ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast hq0.ne'))
        (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq0 _).ne')
    rw [algSat_prod] at hpoly
    have hBeq : B = Multiset.map (fun x => x * χ.val q) {α, β} := by
      refine multiset_eq_of_prod_eq hc ?_
      rw [hpoly, Newform.heckePoly]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
        Multiset.prod_singleton, key]
      rw [← hsum, ← hprod, ← hrr]
      simp only [Units.val_mul, Polynomial.C_mul, Polynomial.C_add]
      ring
    rw [hBeq]
    exact htw
  have h1 := (hiso.hasSat hBs).twist (χ := χ⁻¹) (HChar.UnrAt.inv (hE.1 w))
  rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h1
  exact ⟨_, h1⟩

end GlobalTheory.NewLevel

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.NewLevel

open UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 _root_.Formalism.L2.Host

private theorem level_zero_eq_maximal_compact (w : HeightOneSpectrum (𝓞 ℚ)) : UpperTheory.V.Sd.K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem locGL_comm' {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion ℚ))
    (k : GL (Fin 2) (w.adicCompletion ℚ)) : locGL ℚ 2 v g * locGL ℚ 2 w k = locGL ℚ 2 w k * locGL ℚ 2 v g := by
  refine UpperTheory.V.Af.GlobalFixedVectors.gl_ext fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem normV_surj' {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private noncomputable def LowS (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) :=
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2)))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 + Eo v 1 1))

private theorem mem_LowS {k : ℕ} {φ : TR.Sm ℚ 2} : φ ∈ LowS k ↔ ((∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (k : ℂ)) • φ) ∧
      (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) ∧
      (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0)) := by
  simp only [LowS, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply, sub_eq_zero, and_assoc]

private theorem lowS_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : φ ∈ LowS k) (u : GL (Fin 2) (Af ℚ)) : TR.finRep ℚ 2 u φ ∈ LowS k := by
  obtain ⟨h1, h2, h3⟩ := mem_LowS.1 h
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine mem_LowS.2 ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h1, map_smul]
  · rw [e, e, e, e, ← map_sub, h2, map_smul, map_add (f := _)]
  · rw [e, e, ← map_add (f := _), h3, map_zero]

theorem newLevel : Af.Hypotheses₂ → Published.CuspSemisimpleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π : TR.CuspSub ℚ 2),
    (∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) →
    ∀ (w : Pl) (Bs : Multiset ℂˣ), π.HasSat w Bs → ¬ normV w ∣ g.M := by
  intro P hS k hk g j π hπ w Bs hw hd
  have hM : 1 ≤ g.M := g.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨π₀, ψ, hψ, hψ0, hlev, hlow, hsat⟩ := UpperTheory.V.Z.Kato.NewVec.newVec hS P.admR k hk g
  obtain ⟨B, hB⟩ := GlobalTheory.NewLevel.spherical_of_normTwist P.smoR k hk g j π π₀ hπ hsat w Bs hw
  let L : Submodule ℂ (TR.Sm ℚ 2) :=
    LowS k ⊓ ⨅ q, ⨅ (_ : q ≠ w), Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))
  let U : Submodule ℂ π₀.V := L.comap π₀.V.subtype
  have hU : ∀ h, ∀ x ∈ U, π₀.locRep w h x ∈ U := by
    intro h x hx
    simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hx ⊢
    refine ⟨lowS_fin hx.1 _, fun q hq u hu => ?_⟩
    have h1 : TR.finRep ℚ 2 (locGL ℚ 2 q u) x.1 = x.1 := hx.2 q hq u hu
    change TR.finRep ℚ 2 (locGL ℚ 2 q u) (TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1) = TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1
    rw [← Module.End.mul_apply, ← map_mul, locGL_comm' hq, map_mul, Module.End.mul_apply, h1]
  have hU0 : U ≠ ⊥ := by
    intro h
    have hm : (⟨ψ, hψ⟩ : π₀.V) ∈ U := by
      simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
      exact ⟨mem_LowS.2 hlow, fun q _ => hlev q⟩
    rw [h, Submodule.mem_bot] at hm
    exact hψ0 (congrArg Subtype.val hm)
  obtain ⟨σ, hσ⟩ := (locCompR P ℚ 2 π₀ w).1
  have hiso := (locCompR P ℚ 2 π₀ w).2 σ hσ
  have hσf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := by
    refine hiso.hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w 2).2 ?_
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    exact ⟨y, hy0, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hy u hu⟩
  obtain ⟨x, hxU, hx0, hxf⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed σ.ρ σ.irred (π₀.locRep w) hiso.2 U hU hU0 _ hσf
  simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hxU
  obtain ⟨hxl, hxq⟩ := hxU
  obtain ⟨hwt, hlo, hone⟩ := mem_LowS.1 hxl
  have hx0' : (x : TR.Sm ℚ 2) ≠ 0 := fun e => hx0 (Subtype.ext e)
  have hp := (places w).1
  have hN : 1 ≤ g.M / normV w := Nat.div_pos (Nat.le_of_dvd hM hd) hp.pos
  have hNM : g.M / normV w ∣ g.M := Nat.div_dvd_of_dvd hd
  have hNne : g.M / normV w ≠ g.M := (Nat.div_lt_self hM hp.one_lt).ne
  have hcusp := π₀.cusp x.1 x.2
  have hfix : ∀ u ∈ K1G (g.M / normV w), TR.finRep ℚ 2 u x.1 = x.1 :=
    GlobalTheory.NewLevelInv.inv_K1G g.M w hM hd x.1 hcusp.1.level (fun q hq => hxq q hq) (by
      rw [level_zero_eq_maximal_compact]; exact fun u hu => congrArg Subtype.val (hxf u hu))
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Sd.Wc.centChar P ℚ π₀
  have hc : ∀ (z : Ideles ℚ) (g' : GA ℚ 2),
      x.1.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g') = ((ω.1 z : ℂˣ) : ℂ) * x.1.1 g' :=
    fun z g' => hω z x.1 x.2 g'
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Br.charOf _ hN ω x.1 hx0' hone hfix hc
  obtain ⟨f, hf, hL⟩ := UpperTheory.V.Br.deadel k _ hN χ ω hχ x.1 hcusp ⟨hwt, hlo, hone⟩ hfix hc
  haveI : NeZero (g.M / normV w) := ⟨by omega⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine hx0' (Subtype.ext (funext fun g' => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp _ hN g'
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : UpperTheory.V.Sd.IsHol k (lev (g.M / normV w)) ω x.1 :=
    ⟨hcusp.1, fun q u hu => hfix _ (kLocal _ hN q u hu), hc, hwt, hlo⟩
  refine hf0 (g.new _ hNM hNne f χ hf ?_)
  refine Filter.eventually_cofinite.2 ((Set.finite_le_nat g.M).subset fun q hq => ?_)
  simp only [Set.mem_setOf_eq] at hq
  push_neg at hq
  obtain ⟨hqp, hqe⟩ := hq
  by_contra hqM
  have hqd : ¬ q ∣ g.M := fun h => hqM (Nat.le_of_dvd hM h)
  obtain ⟨wq, rfl⟩ := normV_surj' hqp
  obtain ⟨α, β, hq2, hsum, -⟩ := hsat wq hqd
  have hqN : ¬ normV wq ∣ g.M / normV w := fun h => hqd (h.trans hNM)
  have hv : GlobalTheory.LFun.IsSatVecGL wq (UpperTheory.V.Sd.locSm ℚ wq) x.1 {α, β} :=
    (hq2.2 x (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal _ hN wq u (by
      rwa [(places wq).2.2.2 _ hN hqN, level_zero_eq_maximal_compact])))) hx0).map π₀.V.subtype (fun _ _ => rfl) hx0'
  obtain ⟨h1, -⟩ := UpperTheory.V.Br.eigOf k _ hk1 hN χ ω hχ f x.1 hL hhol wq α β hqN hv
  rw [hsum] at h1
  exact hqe h1

end GlobalTheory.NewLevel

end
