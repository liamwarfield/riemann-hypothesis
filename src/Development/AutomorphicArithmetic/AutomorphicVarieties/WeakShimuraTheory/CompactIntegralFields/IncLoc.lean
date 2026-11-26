module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SpaceEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.AbsPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuLoc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.NotDvdIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem over_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), ← hg, ← hg, map_inv₀, g.commutes]

private theorem not_dvd_index {Γ k : Type} [Group Γ] [Field k] [Finite k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]
    (φ : Γ →* (Fin 4 → kˣ)) : ¬ l ∣ φ.ker.index := by
  rw [Subgroup.index_ker]
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l (h.trans (Subgroup.card_subgroup_dvd_card _))
  have h1 : x = 1 := funext fun i => by
    have h2 : x i ^ l = 1 := by
      rw [← hx]
      exact congrFun (pow_orderOf_eq_one x) i
    have h3 : ((x i : k) - 1) ^ l = 0 := by
      rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h3))
  rw [h1, orderOf_one] at hx
  exact hl.out.one_lt.ne hx

private theorem clos_eq {X : Type} [Group X] (s t : Set X) (h1 : ∀ x ∈ s, x = 1 ∨ x ∈ t) (h2 : t ⊆ s) :
    Subgroup.normalClosure t = Subgroup.normalClosure s := by
  refine le_antisymm (Subgroup.normalClosure_mono h2) (Subgroup.normalClosure_le_normal fun x hx => ?_)
  rcases h1 x hx with rfl | h
  · exact one_mem _
  · exact Subgroup.subset_normalClosure h

open scoped Pointwise in
theorem UpperTheory.V.Ws.X1.linkT :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∃ (S : Finset (HeightOneSpectrum (𝓞 T.F))) (K : Subgroup (G T.F Ω)) (Γ : Type) (_ : Group Γ) (_ : TopologicalSpace Γ) (_ : IsTopologicalGroup Γ) (_ : CompactSpace Γ) (_ : T2Space Γ) (_ : TotallyDisconnectedSpace Γ) (π : G T.F Ω →* Γ) (ι : T.ι ≃ S), GC.GLink l S K π ∧ (∀ w ∈ S, ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) ∧ (∀ v, IsPlaceOver (T.pl v) (ι v).1) ∧ (T.fr ∅).Quo π := by
  intro Ω _ _ _ l hl c D T hT
  classical
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  obtain ⟨-, hfk, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI := hfk
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hro, -⟩ := facts D hD
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  let K : Subgroup (G T.F Ω) := D.rbar.ker.comap (resQ T.F)
  have hKo : IsOpen (K : Set (G T.F Ω)) := hro.preimage hcont
  have hKi : ¬ l ∣ K.index := by
    have h1 : K = (MonoidHom.pi fun i =>
        ((Units.map (residue c.O).toMonoidHom).comp (D.ps i)).comp (resQ T.F)).ker := by
      ext g
      show D.rbar (resQ T.F g) = 1 ↔ _
      rw [MonoidHom.mem_ker]
      refine ⟨fun h => funext fun i => Units.ext ?_, fun h => ?_⟩
      · simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrFun (congrFun h i) i
      · ext i j
        by_cases e : i = j
        · subst e
          simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrArg Units.val (congrFun h i)
        · simp [Raw.rbar, Raw.r0, diagRep, mapRep, e]
    rw [h1]
    exact not_dvd_index _
  have hfin : {v : HeightOneSpectrum (𝓞 T.F) | ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 T.F)})
      (mt Ideal.span_singleton_eq_bot.1 (Nat.cast_ne_zero.2 hl.out.ne_zero))).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hval : ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 T.F)}, IsPlaceOver A v →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal) := fun {A v} h => (places T.F Ω l A).2.2.1 v h
  let N := GC.tameN (S : Set (HeightOneSpectrum (𝓞 T.F))) K
  haveI : N.Normal := Subgroup.is_normal_topologicalClosure _
  haveI hNc : IsClosed (N : Set (G T.F Ω)) := Subgroup.isClosed_topologicalClosure _
  have h0 : ∀ u : T.ι, ∃ w : S, IsPlaceOver (T.pl u) w.1 := fun u => by
    obtain ⟨a1, a2, -⟩ := places T.F Ω l (T.pl u)
    obtain ⟨w, hw⟩ := a1 fun h => (a2 h).2 (T.ovl u)
    exact ⟨⟨w, (hS w).2 ((hval hw).1 (T.ovl u))⟩, hw⟩
  choose pl hp using h0
  have hbij : Function.Bijective pl := by
    refine ⟨fun a b h => ?_, fun w => ?_⟩
    · obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := T.F) (hp a) (h ▸ hp b)
      refine (T.cover (T.pl b) (T.ovl b)).unique ⟨g, fun x => ?_⟩ ⟨1, fun _ => Iff.rfl⟩
      show g • x ∈ T.pl b ↔ _
      rw [← hg]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w.1 := exists_isPlaceOver Ω w.1
      obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hval hA).2 ((hS _).1 w.2))
      exact ⟨u, Subtype.ext (eq_of_isPlaceOver (hp u) (over_move g hg hA))⟩
  refine ⟨S, K, G T.F Ω ⧸ N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (AlgebraTools.totallyDisconnected_quot _ N hNc).1, QuotientGroup.mk' N, Equiv.ofBijective pl hbij,
    GC.gLink_quot l hD.l_odd (fun v hv => (hS v).2 hv) inferInstance hKo hKi, fun w hw => (hS w).1 hw, hp,
    QuotientGroup.continuous_mk, QuotientGroup.mk'_surjective _, ?_⟩
  rw [QuotientGroup.ker_mk']
  refine congrArg Subgroup.topologicalClosure (clos_eq _ _ ?_ fun x hx => ?_)
  · rintro x ⟨A, hA, h1, h2⟩
    obtain ⟨a1, a2, -⟩ := places T.F Ω l A
    by_cases ht : A = ⊤
    · rw [(a2 ht).1, Subgroup.mem_bot] at h1
      exact Or.inl h1
    · obtain ⟨v, hv⟩ := a1 ht
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨v, fun h => hA l (Finset.mem_insert_self _ _) ((hval hv).2 ((hS v).1 h)), A, hv, h1, h2⟩
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, A, hA, h1, h2⟩ := hx
    refine ⟨A, fun p hp h => ?_, h1, h2⟩
    obtain rfl : p = l := by simpa using hp
    exact hv ((hS v).2 ((hval hA).1 h))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DefEx
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.defEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → Φ.noMu.Std l a ∧ Φ.noMu.IsRes ((residue Λ).comp a) c ∧ ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (P : PD Φ.ι Γ R), Φ.noMu.IsDef a c P := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c hc
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  have hok : Φ.noMu.Ok ((residue Λ).comp a) :=
    ⟨hS.ok.mul, hS.ok.kill, hS.ok.dist, hS.ok.two, hS.ok.lc⟩
  have hS' : Φ.noMu.Std l a :=
    ⟨hok, hS.char, hS.cont, hS.phi, hS.closed, hS.phiv, fun _ _ hs => hs.elim⟩
  have hpair : ∀ {R : Type} [CommRing R] (b : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair b P → Φ.noMu.IsPair b P :=
    fun b P h => ⟨h.mult, h.kill, h.nrm, h.low, h.flag, fun _ _ hs => hs.elim⟩
  have hc' : Φ.noMu.IsRes ((residue Λ).comp a) c :=
    ⟨hpair _ c hc.pair, ⟨hc.res.diag, hc.res.char, hc.res.shape⟩, hc.cont⟩
  refine ⟨hS', hc', ?_⟩
  obtain ⟨X⟩ := spaceEx Φ.noMu l a hS'
  have hid : ∀ x : ResidueField Λ, res Λ (ResidueField Λ) x = x := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    exact (res Λ (ResidueField Λ)).commutes y
  have hmap : c.map ↑(res Λ (ResidueField Λ)) = c := by
    apply PD.ext
    · ext g i j
      simp [PD.map, mapRep, hid]
    · funext v
      ext i j
      simp [PD.map, hid]
  have hmax : maximalIdeal (ResidueField Λ) = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  have hlift : Φ.noMu.Lifts a c c := ⟨hc'.pair, by rw [hmax]; exact hc.cont, hmap⟩
  obtain ⟨x, hx⟩ := X.univ (ResidueField Λ) c c hc' hlift
  have hres : Φ.noMu.IsRes ((residue Λ).comp a) (X.P.map ↑x) := by rw [hx]; exact hc'
  obtain ⟨R, i1, i2, i3, f, hdef, -, -⟩ := cmplEx Φ.noMu l a hS' X x hres
  rw [hx] at hdef
  exact ⟨R, i1, i2, i3, X.P.map ↑f, hdef⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DualZero
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem tri_zero {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (ht : Fin 4 → ℤ)
    (hinj : Function.Injective ht) (hb : ∀ i j, ht i - ht j < 4) (hr : ∀ g i j, ht i < ht j → r g i j = 0)
    (ω : Γ → k) (hω : ∀ i j, ∃ g, r g i i * r g⁻¹ j j ≠ ω g) (F : M4 k →ₗ[k] k)
    (hF : ∀ g Y, F (r g * Y * r g⁻¹) = ω g * F Y) : F = 0 := by
  have hexp : ∀ Y : M4 k, F Y = ∑ a, ∑ b, Y a b * F (Matrix.single a b 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : k) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hent : ∀ (A B : M4 k) (i j a b : Fin 4), (A * (Matrix.single i j 1 : M4 k) * B : M4 k) a b = A a i * B j b := by
    intro A B i j a b
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
  have main : ∀ n : ℕ, ∀ i j, 4 - (n : ℤ) ≤ ht i - ht j → F (Matrix.single i j 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro i j hij
      exfalso
      have := hb i j
      push_cast at hij
      omega
    | succ n ih =>
      intro i j hij
      by_cases hlt : 4 - (n : ℤ) ≤ ht i - ht j
      · exact ih i j hlt
      obtain ⟨g, hg⟩ := hω i j
      have hsum := hF g (Matrix.single i j 1)
      rw [hexp (r g * Matrix.single i j 1 * r g⁻¹)] at hsum
      simp only [hent] at hsum
      have inner : ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1)
          = r g i i * r g⁻¹ j j * F (Matrix.single i j 1) := by
        refine Finset.sum_eq_single j (fun b _ hbj => ?_) (fun h => absurd (Finset.mem_univ _) h)
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        · have hne : ht b ≠ ht j := fun e => hbj (hinj e)
          rw [ih i b (by push_cast at hij hlt ⊢; omega)]
          ring
      have outer : ∑ a, ∑ b, r g a i * r g⁻¹ j b * F (Matrix.single a b 1)
          = ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1) := by
        refine Finset.sum_eq_single i (fun a _ hai => ?_) (fun h => absurd (Finset.mem_univ _) h)
        apply Finset.sum_eq_zero
        intro b _
        by_cases hia : ht a < ht i
        · rw [hr g a i hia]
          ring
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        have hne : ht a ≠ ht i := fun e => hai (hinj e)
        rw [ih a b (by push_cast at hij hlt ⊢; omega)]
        ring
      rw [outer, inner] at hsum
      have e : (r g i i * r g⁻¹ j j - ω g) * F (Matrix.single i j 1) = 0 := by
        rw [sub_mul, hsum, sub_self]
      exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hg)
  apply LinearMap.ext
  intro Y
  rw [hexp Y, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [main 8 a b (by have := hb b a; push_cast; omega), mul_zero]

private theorem adj_conj {Γ k : Type} [Group Γ] [CommRing k] {r : Γ →* M4 k} (h : ∀ g, ∃ ν, IsGSp ν (r g)) (g : Γ)
    (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  obtain ⟨ν, hν⟩ := h g
  obtain ⟨μ, hμ⟩ := h g⁻¹
  have G := grp k
  have e1 : r g * r g⁻¹ = 1 := by rw [← r.map_mul, mul_inv_cancel, r.map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← r.map_mul, inv_mul_cancel, r.map_one]
  have a1 : adj (r g) = ν • r g⁻¹ := G.2.2.2.2.2.2.1 ν _ _ hν e1
  have a2 : adj (r g⁻¹) = μ • r g := G.2.2.2.2.2.2.1 μ _ _ hμ e2
  have hprod := G.2.2.2.2.2.2.2.1 ν μ _ _ hν hμ
  rw [e1] at hprod
  have e : adj (1 : M4 k) * 1 = (ν * μ) • (1 : M4 k) := hprod
  rw [G.2.2.2.2.1, Matrix.mul_one] at e
  have e00 := congrFun (congrFun e 0) 0
  simp at e00
  have hμν : μ * ν = 1 := by rw [mul_comm]; exact e00.symm
  rw [G.1, G.1, a1, a2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hμν, one_smul, Matrix.mul_assoc]

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ)
    (hm : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (i j : Fin 4) (g : Γ) :
    Φ.rt (wt i j) g = Φ.χ i g * Φ.χ j g⁻¹ := by
  have hd : Φ.χ 3 g = Φ.ν g * (Φ.χ 0 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 0 g)
  have hc : Φ.χ 2 g = Φ.ν g * (Φ.χ 1 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 1 g)
  rw [map_inv]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hc, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]; abel)

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.dualZero :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ (c : PD Φ.ι Γ k), Φ.Res a c → ∀ (h : ∀ g, ∃ x, IsGSp x (c.r g)) (ω : Γ → k), (∀ w, ∃ g, a (Φ.rt w g) ≠ ω g) → ∀ f : sp4 k →ₗ[k] k, (∀ g X, f (adSp c.r h g X) = ω g * f X) → f = 0 := by
  intro O Γ _ _ _ Φ k _ a hok c hres h ω hωw f hf
  have G := grp k
  have adj_add := G.2.2.1
  have adj_smul := G.2.2.2.1
  have adj_adj := G.2.1
  let AdjL : M4 k →ₗ[k] M4 k := { toFun := adj, map_add' := adj_add, map_smul' := adj_smul }
  have h2 : (2 : k) ≠ 0 := hok.two.ne_zero
  set t : k := (2 : k)⁻¹ with htdef
  have hsub : ∀ Y : M4 k, adj (Y - adj Y) = adj Y - Y := by
    intro Y
    have e := map_sub AdjL Y (adj Y)
    simp only [AdjL, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e, adj_adj]
  let π : M4 k →ₗ[k] sp4 k := LinearMap.codRestrict (sp4 k) (t • (LinearMap.id - AdjL)) (fun Y => by
    show adj (t • (Y - adj Y)) = -(t • (Y - adj Y))
    rw [adj_smul, hsub, ← smul_neg, neg_sub])
  have hπ : ∀ Y, ((π Y : sp4 k) : M4 k) = t • (Y - adj Y) := fun Y => rfl
  let F : M4 k →ₗ[k] k := f ∘ₗ π
  have hFc : ∀ g Y, F (c.r g * Y * c.r g⁻¹) = ω g * F Y := by
    intro g Y
    have e : π (c.r g * Y * c.r g⁻¹) = adSp c.r h g (π Y) := by
      apply Subtype.ext
      rw [adSp_val, hπ, hπ, adj_conj h g Y]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    show f (π _) = ω g * f (π Y)
    rw [e, hf]
  have hfix : ∀ X : sp4 k, π X = X := by
    intro X
    apply Subtype.ext
    rw [hπ]
    have hX : adj (X : M4 k) = -(X : M4 k) := X.2
    rw [hX, sub_neg_eq_add, ← two_smul k (X : M4 k), smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hω' : ∀ i j, ∃ g, c.r g i i * c.r g⁻¹ j j ≠ ω g := by
    intro i j
    obtain ⟨g, hg⟩ := hωw (wt i j)
    refine ⟨g, ?_⟩
    rw [hres.diag, hres.diag]
    rw [rt_wt Φ hok.mul i j g, Units.val_mul, map_mul] at hg
    exact hg
  have key : ∀ ht : Fin 4 → ℤ, Function.Injective ht → (∀ i j, ht i - ht j < 4) →
      (∀ g i j, ht i < ht j → c.r g i j = 0) → f = 0 := by
    intro ht hi hb hr
    have hF0 := tri_zero c.r ht hi hb hr ω hω' F hFc
    apply LinearMap.ext
    intro X
    have e : F X = 0 := by rw [hF0]; rfl
    calc f X = f (π X) := by rw [hfix X]
      _ = F X := rfl
      _ = 0 := e
  rcases hres.shape with ⟨hS, _⟩ | hS
  · refine key ![-3, -1, -2, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nP, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
  · refine key ![-3, -2, -1, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nM, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.RankAdjLe
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem rank_adj_le {k : Type} [Field k] (X : M4 k) : (adj X).rank ≤ X.rank := by
  have e : adj X = Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev) * Matrix.diagonal (fun i => (sgn i : k)) := by
    ext i j
    rw [adj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.transpose_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  calc _ ≤ (Matrix.diagonal (fun i => (sgn i : k)) * ((Matrix.transpose X).submatrix Fin.rev Fin.rev)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ ((Matrix.transpose X).submatrix Fin.rev Fin.rev).rank := Matrix.rank_mul_le_right _ _
    _ = X.rank := by
      rw [← Matrix.rank_transpose X]
      exact Matrix.rank_submatrix (Matrix.transpose X) Fin.revPerm Fin.revPerm

private noncomputable def cmp {k : Type} [Field k] (p : M4 k) :
    M4 k →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) where
  toFun X := p.mulVecLin.rangeRestrict ∘ₗ X.mulVecLin ∘ₗ (LinearMap.range p.mulVecLin).subtype
  map_add' X Y := by
    rw [Matrix.mulVecLin_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a X := by
    ext v i
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

private theorem cmp_zero {k : Type} [Field k] (p X : M4 k) (h : cmp p X = 0) : p * X * p = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun h ⟨Matrix.mulVec p w, w, rfl⟩)
  simpa [cmp] using h2

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.ccDim :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (h : ∀ g, ∃ x, IsGSp x (r g)), (2 : k) ≠ 0 → ∀ s : Γ, s * s = 1 → IsGSp (-1) (r s) → Module.finrank k (LinearMap.ker (adSp r h s - 1)) ≤ 4 := by
  intro k Γ _ _ r h h2 s hss hs
  set g := r s with hgdef
  have adj_mul := (grp k).1
  have adj_adj := (grp k).2.1
  have adj_add := (grp k).2.2.1
  have adj_smul := (grp k).2.2.2.1
  have adj_one := (grp k).2.2.2.2.1
  have hg2 : g * g = 1 := by rw [hgdef, ← r.map_mul, hss, r.map_one]
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hss).symm
  have hadj : adj g = -g := by
    have e : adj g * g = (-1 : k) • 1 := hs
    calc adj g = adj g * g * g := by rw [Matrix.mul_assoc, hg2, Matrix.mul_one]
      _ = -g := by rw [e]; simp
  set c : k := (2 : k)⁻¹ with hc
  have hc2 : c * 2 = 1 := inv_mul_cancel₀ h2
  set p : M4 k := c • (1 + g) with hp
  set q : M4 k := c • (1 - g) with hq
  have hpq : p + q = 1 := by
    rw [hp, hq, ← smul_add]
    have e : (1 + g) + (1 - g) = (2 : k) • (1 : M4 k) := by rw [two_smul]; abel
    rw [e, smul_smul, hc2, one_smul]
  have hadjp : adj p = q := by
    rw [hp, hq, adj_smul, adj_add, adj_one, hadj, sub_eq_add_neg]
  have hadjq : adj q = p := by rw [← hadjp, adj_adj]
  have hpq0 : p * q = 0 := by
    have e : (1 + g) * (1 - g) = 0 := by
      rw [add_mul, mul_sub, mul_sub, hg2]
      simp
    rw [hp, hq, smul_mul_assoc, mul_smul_comm, e]
    simp
  have hpp : p * p = p := by
    have e : p * p = p * (p + q) := by rw [mul_add, hpq0, add_zero]
    rw [e, hpq, mul_one]
  have hrk : p.rank ≤ 2 := by
    have h1 : q.rank ≤ p.rank := by rw [← hadjp]; exact rank_adj_le p
    have h1' : p.rank ≤ q.rank := by rw [← hadjq]; exact rank_adj_le q
    have hle : LinearMap.range q.mulVecLin ≤ LinearMap.ker p.mulVecLin := by
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hpq0, Matrix.zero_mulVec]
    have hmono := Submodule.finrank_mono hle
    have hsum := LinearMap.finrank_range_add_finrank_ker p.mulVecLin
    rw [Module.finrank_fin_fun] at hsum
    have eq1 : q.rank = Module.finrank k (LinearMap.range q.mulVecLin) := rfl
    have eq2 : p.rank = Module.finrank k (LinearMap.range p.mulVecLin) := rfl
    omega
  let K := LinearMap.ker (adSp r h s - 1)
  let ψ : K →ₗ[k] (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
    cmp p ∘ₗ (sp4 k).subtype ∘ₗ K.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨Y, hYsp⟩, hYk⟩ hY
    have hYa : adj Y = -Y := hYsp
    have hfix : g * Y * g = Y := by
      have e := LinearMap.mem_ker.mp hYk
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at e
      have e2 := congrArg Subtype.val e
      rw [adSp_val, hsi] at e2
      exact e2
    have hcomm : g * Y = Y * g := by
      calc g * Y = g * Y * (g * g) := by rw [hg2, Matrix.mul_one]
        _ = (g * Y * g) * g := by simp only [Matrix.mul_assoc]
        _ = Y * g := by rw [hfix]
    have hpY : p * Y = Y * p := by
      rw [hp, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hcomm]
    have hz : p * Y * p = 0 := cmp_zero p Y hY
    have hYp : Y * p = 0 := by
      rw [hpY, Matrix.mul_assoc, hpp] at hz
      exact hz
    have h0 : adj (0 : M4 k) = 0 := by simpa using adj_smul 0 0
    have hqY : q * Y = 0 := by
      have e := congrArg adj hYp
      rw [adj_mul, hadjp, hYa, h0, Matrix.mul_neg, neg_eq_zero] at e
      exact e
    have hq' : q = 1 - p := eq_sub_of_add_eq' hpq
    have hYq : Y * q = 0 := by
      rw [hq'] at hqY ⊢
      rw [Matrix.mul_sub, Matrix.mul_one, ← hpY]
      rw [Matrix.sub_mul, Matrix.one_mul] at hqY
      exact hqY
    have hY0 : Y = 0 := by
      calc Y = Y * (p + q) := by rw [hpq, Matrix.mul_one]
        _ = 0 := by rw [Matrix.mul_add, hYp, hYq, add_zero]
    apply Subtype.ext
    apply Subtype.ext
    exact hY0
  calc Module.finrank k K ≤ Module.finrank k (LinearMap.range p.mulVecLin →ₗ[k] LinearMap.range p.mulVecLin) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = p.rank * p.rank := by rw [Module.finrank_linearMap]; rfl
    _ ≤ 2 * 2 := Nat.mul_le_mul hrk hrk
    _ = 4 := rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.PresQuot
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.presQuot :
    ∀ (Λ R' R : Type) [CommRing Λ] [CommRing R'] [Algebra Λ R'] [CommRing R] [Algebra Λ R] (a b : ℕ) (τ : Type) [Finite τ] (g : R' →ₐ[Λ] R) (e : τ → R'), HasPres Λ R' a b → Function.Surjective g → RingHom.ker g = Ideal.span (Set.range e) → HasPres Λ R a (b + Nat.card τ) := by
  intro Λ R' R _ _ _ _ _ a b τ _ g e hP hg he
  obtain ⟨π, f, hπ, hk⟩ := hP
  obtain ⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ)) := ⟨Finite.equivFin τ⟩
  choose l hl using fun t => hπ (e t)
  refine ⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩
  have hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp⟩
      | right i => exact Or.inr ⟨σ.symm i, by simp⟩
    · rintro (⟨i, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨Fin.castAdd _ i, by simp⟩
      · exact ⟨Fin.natAdd _ (σ t), by simp⟩
  have hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g) := by
    ext x
    simp [RingHom.mem_ker]
  have hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact (hl t).symm
  rw [hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange,
    Ideal.span_union, sup_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuQuot
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ClosureComm
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem adj_up {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := fun i j h => by
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

private theorem adj_diag {R : Type} [CommRing R] (X : M4 R) (i : Fin 4) : adj X i i = X i.rev i.rev := by
  have h : sgn i * sgn i = 1 := by revert i; decide
  rw [adj_apply, h, one_smul]

private theorem gsp_diag {R : Type} [CommRing R] {ν : R} {n X : M4 R} (hn : IsGSp 1 n) (hX : IsGSp ν X)
    (hu : IsUp (adj n * X * n)) (i : Fin 4) : (adj n * X * n) i.rev i.rev * (adj n * X * n) i i = ν := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn
  have h2 : n * adj n = 1 := mul_eq_one_comm.1 h1
  have h3 : adj (adj n * X * n) * (adj n * X * n) = ν • (1 : M4 R) := by
    have hX' : adj X * X = ν • (1 : M4 R) := hX
    rw [hmul, hmul, hadj]
    calc adj n * (adj X * n) * (adj n * X * n) = adj n * (adj X * (n * adj n) * X) * n := by simp only [mul_assoc]
      _ = ν • (1 : M4 R) := by rw [h2, mul_one, hX', mul_smul_comm, mul_one, smul_mul_assoc, h1]
  have h4 := up_mul_diag (adj_up hu) hu i
  rw [adj_diag, h3] at h4
  simpa using h4.symm

private theorem closure_comm {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing R]
    (I : Ideal R) [IsHausdorff I R] (H : Subgroup Γ) (f : Γ → R) (h1 : f 1 = 1)
    (hm : ∀ s ∈ H, ∀ t ∈ H, f (s * t) = f s * f t) (hc : AdicCont I f) :
    ∀ c ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure, f c = 1 := by
  have hi : ∀ s ∈ H, f s * f s⁻¹ = 1 := fun s hs => by rw [← hm s hs _ (H.inv_mem hs), mul_inv_cancel, h1]
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ H ∧ f g = 1}
      one_mem' := ⟨H.one_mem, h1⟩
      mul_mem' := fun {s t} hs ht => ⟨H.mul_mem hs.1 ht.1, by rw [hm s hs.1 t ht.1, hs.2, ht.2, mul_one]⟩
      inv_mem' := fun {s} hs => ⟨H.inv_mem hs.1, by have := hi s hs.1; rwa [hs.2, one_mul] at this⟩ }
  have hK : ⁅H, H⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    have a1 := H.mul_mem hs ht
    have a2 := H.mul_mem a1 (H.inv_mem hs)
    rw [commutatorElement_def]
    refine ⟨H.mul_mem a2 (H.inv_mem ht), ?_⟩
    rw [hm _ a2 _ (H.inv_mem ht), hm _ a1 _ (H.inv_mem hs), hm _ hs _ ht]
    linear_combination (f t * f t⁻¹) * hi s hs + hi t ht
  intro c hcm
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun N => ?_
  have hcl := (hc N).isClosed_fiber (Ideal.Quotient.mk (I ^ N) 1)
  have : c ∈ {g | Ideal.Quotient.mk (I ^ N) (f g) = Ideal.Quotient.mk (I ^ N) 1} :=
    closure_minimal (fun g hg => by
      show Ideal.Quotient.mk (I ^ N) (f g) = _
      rw [(hK hg).2]) hcl hcm
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.1 this

private theorem conj_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (r : Γ → M4 R)
    (h : ∀ i j, AdicCont I fun g => r g i j) (A B : M4 R) (i j : Fin 4) : AdicCont I fun g => (A * r g * B) i j := by
  intro N
  have h0 : IsLocallyConstant fun g => (r g).map (Ideal.Quotient.mk (I ^ N)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun p : Fin 4 × Fin 4 => (h p.1 p.2 N).eventually_eq x
    filter_upwards [Filter.eventually_all.2 this] with y hy
    ext a b
    exact hy (a, b)
  have h2 := h0.comp fun X => (A.map (Ideal.Quotient.mk (I ^ N)) * X * B.map (Ideal.Quotient.mk (I ^ N))) i j
  convert h2 using 2 with g
  simp only [Function.comp_apply, ← Matrix.map_mul, Matrix.map_apply]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.muIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.noMu.Lifts a c P → (Φ.Lifts a c P ↔ ∀ v, P.ψ v 0 (ζ v) = 1 ∧ P.ψ v 1 (ζ v) = 1) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c _ ζ hζ hν R _ _ _ P hP
  refine ⟨fun h v => ⟨h.pair.mu v _ (hζ v).1 0, h.pair.mu v _ (hζ v).1 1⟩, fun h => ?_⟩
  obtain ⟨⟨hmult, hkill, hnrm, hlow, hflag, -⟩, hcont, hred⟩ := hP
  refine ⟨⟨hmult, hkill, hnrm, hlow, hflag, fun v s hs i => ?_⟩, hcont, hred⟩
  have hn : IsGSp 1 (P.n v) := (hlow v).1
  have n1 : adj (P.n v) * P.n v = 1 := by simpa [IsGSp] using hn
  have n2 : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.1 n1
  have hz : ζ v ∈ Φ.Gv v := (hS.mu v _ (hζ v).1).1
  have hsG : s ∈ Φ.Gv v := (hS.mu v _ hs).1
  have hrev : ∀ j : Fin 4, P.ψ v j.rev (ζ v) * P.ψ v j (ζ v) = 1 := fun j => by
    have := gsp_diag hn (hmult (ζ v)) (hflag v _ hz) j
    rw [RingHom.comp_apply] at this
    erw [hν v] at this
    rwa [map_one] at this
  have hzi : P.ψ v i (ζ v) = 1 := by
    have e0 := hrev 0
    have e1 := hrev 1
    rw [(h v).1, mul_one] at e0
    rw [(h v).2, mul_one] at e1
    fin_cases i
    exacts [(h v).1, (h v).2, e1, e0]
  have h1 : P.ψ v i 1 = 1 := by simp [PD.ψ, n1]
  have hm : ∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t := fun s hs t ht => by
    unfold PD.ψ
    rw [← up_mul_diag (hflag v s hs) (hflag v t ht), map_mul]
    refine congrFun (congrFun ?_ i) i
    calc adj (P.n v) * (P.r s * P.r t) * P.n v
        = adj (P.n v) * P.r s * (P.n v * adj (P.n v)) * P.r t * P.n v := by rw [n2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have hpow : ∀ n : ℕ, P.ψ v i (ζ v ^ n) = 1 := fun n => by
    induction n with
    | zero => rw [pow_zero, h1]
    | succ n ih => rw [pow_succ, hm _ (pow_mem hz n) _ hz, ih, hzi, mul_one]
  obtain ⟨n, hn'⟩ := (hζ v).2 s hs
  have hc := closure_comm (maximalIdeal R) (Φ.Gv v) (P.ψ v i) h1 hm
    (conj_cont _ (fun g => P.r g) hcont _ _ i i) _ hn'
  have := hm _ (mul_mem hsG (inv_mem (pow_mem hz n))) _ (pow_mem hz n)
  rwa [inv_mul_cancel_right, hc, hpow, mul_one] at this
end

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at hp
  · exact h.cont.map _ (fun x hx =>
      (res_eq_zero_iff Λ R' _).mp ((res_map f x).trans ((res_eq_zero_iff Λ R x).mpr hx)))
  · rw [PD.map_map]
    convert h.red using 2
    exact RingHom.ext fun x => res_map f x

private theorem lifts_noMu {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) : Φ.noMu.Lifts a c P :=
  ⟨⟨h.pair.mult, h.pair.kill, h.pair.nrm, h.pair.low, h.pair.flag, fun _ _ hs => hs.elim⟩, h.cont, h.red⟩

theorem UpperTheory.V.Ws.X1.muQuot :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.noMu.IsDef a c P' → ∃ (g : R' →ₐ[Λ] R) (e : Φ.ι × Fin 2 → R'), Function.Surjective g ∧ RingHom.ker g = Ideal.span (Set.range e) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd c hres ζ hζ hν R _ _ _ P hP R' _ _ _ P' hP'
  obtain ⟨g, hg, -⟩ := hP'.2 R P (lifts_noMu hP.1)
  have hPψ := (X1.muIff Φ l a hstd c hres ζ hζ hν R P (lifts_noMu hP.1)).mp hP.1
  let e : Φ.ι × Fin 2 → R' := fun p => P'.ψ p.1 (Fin.castLE (by norm_num) p.2) (ζ p.1) - 1
  let I : Ideal R' := Ideal.span (Set.range e)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨v, i⟩, rfl⟩
      have key : ∀ j : Fin 4, g (P'.ψ v j (ζ v)) = P.ψ v j (ζ v) := by
        intro j
        rw [← hg, PD.map_ψ]
        rfl
      fin_cases i
      · simp [e, key, (hPψ v).1]
      · simp [e, key, (hPψ v).2]
    · exact map_zero g
    · intro x y _ _ hx hy
      rw [map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 := hIg 1 (htop ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let π : R' →ₐ[Λ] R' ⧸ I := Ideal.Quotient.mkₐ Λ I
  haveI : IsCO Λ (R' ⧸ I) := co_quot Λ R' (R' ⧸ I) π (Ideal.Quotient.mkₐ_surjective Λ I)
  have hQn : Φ.noMu.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := lifts_map hP'.1 π
  have hQ : Φ.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := by
    refine (X1.muIff Φ l a hstd c hres ζ hζ hν (R' ⧸ I) _ hQn).mpr (fun v => ⟨?_, ?_⟩)
    · rw [PD.map_ψ]
      have hm : e (v, 0) ∈ I := Ideal.subset_span ⟨(v, 0), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
    · rw [PD.map_ψ]
      have hm : e (v, 1) ∈ I := Ideal.subset_span ⟨(v, 1), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
  obtain ⟨h, hh, -⟩ := hP.2 (R' ⧸ I) _ hQ
  obtain ⟨π', -, huniq⟩ := hP'.2 (R' ⧸ I) _ hQn
  have hhg : h.comp g = π := by
    rw [huniq (h.comp g) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hg, hh]),
      huniq π rfl]
  let gb : R' ⧸ I →ₐ[Λ] R := Ideal.Quotient.liftₐ I g hIg
  obtain ⟨i0, -, huniqP⟩ := hP.2 R P hP.1
  have hgb : gb.comp π = g := by
    ext x
    rfl
  have hid : gb.comp h = AlgHom.id Λ R := by
    rw [huniqP (gb.comp h) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hh, PD.map_map,
        ← AlgHom.comp_toRingHom, hgb, hg]),
      huniqP (AlgHom.id Λ R) (by beta_reduce; rw [← hg, PD.map_map]; rfl)]
  refine ⟨g, e, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective Λ I (h y)
    refine ⟨z, ?_⟩
    have hy := congrArg (fun f : R →ₐ[Λ] R => f y) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
    rw [← hz] at hy
    exact hy
  · apply le_antisymm
    · intro x hx
      have hx' : π x = 0 := by
        rw [← hhg, AlgHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hx'
    · intro x hx
      exact RingHom.mem_ker.mpr (hIg x hx)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_bot {S k : Type} [TopologicalSpace S] [CommRing k] {x : S → k} (h : AdicCont ⊥ x) : IsLocallyConstant x :=
  IsLocallyConstant.desc _ _ (h 1) ((Ideal.Quotient.mk_bijective_iff_eq_bot _).2 (pow_one _)).1

private theorem fin_res {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  obtain ⟨-, -, h1, -⟩ := dvrFacts l c.O
  haveI := h1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem inc_loc {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, ((residue c'.O).comp (inc h)) x = 0 := by
  have hi : (inc h).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) (inc h) ?_
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := (Subalgebra.inclusion h).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral x
  haveI := hi.isLocalHom (Subalgebra.inclusion_injective h)
  intro x hx
  exact (residue_eq_zero_iff _).2 (map_nonunit (inc h) x hx)

private theorem count {O Γ Γb : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb]
    (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ) (hstd : Φ.Std l a)
    (π : Γ →* Γb) (hQ : Φ.Quo π) (s : PD Φ.ι Γ (ResidueField Λ)) (hs : Φ.IsRes ((residue Λ).comp a) s)
    (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R) (hP : Φ.IsDef a s P)
    (tN : ∀ g ∈ Φ.N, Φ.ν g = 1) (tM : ∀ v, ∀ g ∈ Φ.Mu v, Φ.ν g = 1) (ζ : Φ.ι → Γ) (hζ : ∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v))
    (CC : Γ → Prop) (tC : ∀ g, CC g → g * g = 1 ∧ Φ.ν g = -1) (ω : Γ → ResidueField Λ)
    (tW : ∀ w, ∃ g, ((residue Λ).comp a) (Φ.rt w g) ≠ ω g) (d : ℕ)
    (ec : ∀ (ρ : Representation (ResidueField Λ) Γb (sp4 (ResidueField Λ))) (b : Φ.ι → Submodule (ResidueField Λ) (sp4 (ResidueField Λ))),
      IsOpen (ρ.ker : Set Γb) → (∀ v, ∀ g ∈ Φ.Gv v, ∀ X ∈ b v, ρ (π g) X ∈ b v) →
      (∀ f : sp4 (ResidueField Λ) →ₗ[ResidueField Λ] ResidueField Λ, (∀ g X, f (ρ (π g) X) = ω g * f X) → f = 0) →
      (∀ v, Module.finrank (ResidueField Λ) (b v) = 6) →
      (∀ g, CC g → Module.finrank (ResidueField Λ) (LinearMap.ker (ρ (π g) - 1)) ≤ 4) →
      Module.Finite (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) ∧
      Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) ρ b) + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 ρ b) + d * 6 ≤
        Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) ρ b) + d * 4) :
    ∃ m n : ℕ, HasPres Λ R m n ∧ n + 2 + 2 * d ≤ m + 2 * Nat.card Φ.ι := by
  have h2 : (2 : ResidueField Λ) ≠ 0 := hstd.ok.two.ne_zero
  obtain ⟨hstd', hs', R', _, _, _, P', hP'⟩ := X1.defEx Φ l a hstd s hs
  have hQ' : Φ.noMu.Quo π := ⟨hQ.cont, hQ.onto, hQ.ker⟩
  obtain ⟨rb, hrb, hrc⟩ := (X1.descend Φ π hQ (⊥ : Ideal (ResidueField Λ))).1 s.r hs.pair.kill hs.cont
  have hrb' : ∀ g, rb (π g) = s.r g := fun g => DFunLike.congr_fun hrb g
  have hb0 : ∀ g, ∃ x, IsGSp x (s.r g) := fun g => ⟨_, hs.pair.mult g⟩
  have hb : ∀ g, ∃ x, IsGSp x (rb g) := fun g => by
    obtain ⟨g, rfl⟩ := hQ.onto g
    rw [hrb']; exact hb0 g
  have had : ∀ g X, adSp rb hb (π g) X = adSp s.r hb0 g X := fun g X => Subtype.ext (by
    rw [adSp_val, adSp_val, ← map_inv, hrb', hrb'])
  obtain ⟨a1, a2⟩ := X1.adFacts rb hb
  obtain ⟨-, d2⟩ := X1.spDims (ResidueField Λ) h2
  obtain ⟨e1, e2⟩ := ec (adSp rb hb) (fun v => bor (s.n v)) (a1 fun i j => lc_bot (hrc i j)).1
    (fun v g hg X hX => a2 (s.n v) (π g) (hs.pair.low v).1 (by rw [hrb']; exact hs.pair.flag v g hg)
      (by rw [← map_inv, hrb']; exact hs.pair.flag v g⁻¹ (inv_mem hg)) X hX)
    (fun f hf => X1.dualZero Φ _ hstd.ok s hs.res hb0 ω tW f fun g X => by rw [← had]; exact hf g X)
    (fun v => (d2 _ (hs.pair.low v).1).1)
    (fun g hg => X1.ccDim rb hb h2 (π g) (by rw [← map_mul, (tC g hg).1, map_one]) (by
      have h1 := hs.pair.mult g
      rw [(tC g hg).2, Units.val_neg, Units.val_one, map_neg, map_one] at h1
      rw [hrb']
      exact h1))
  obtain ⟨m, p1, p2⟩ := X1.absPres Φ.noMu l a hstd' (fun _ => rfl)
    (fun g hg => by
      have h1 : Φ.noMu.ν g = 1 := tN g hg
      rw [h1, Units.val_one, map_one]) π hQ' s hs' R' P' hP' rb hb hrb e1
  obtain ⟨g, e, g1, g2⟩ := X1.muQuot Φ l a hstd s hs ζ hζ
    (fun v => by rw [tM v (ζ v) (hζ v).1, Units.val_one, map_one]) R P hP R' P' hP'
  refine ⟨_, _, X1.presQuot Λ R' R _ _ _ g e p1 g1 g2, ?_⟩
  have hc : Nat.card (Φ.ι × Fin 2) = 2 * Nat.card Φ.ι := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, mul_comm]
  rw [hc]
  have p3 : Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.H1C (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + 2 ≤
      m + Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH0 (adSp rb hb) fun v : Φ.ι => bor (s.n v)) := p2
  show Module.finrank (ResidueField Λ) (UpperTheory.V.Fr.coneH2 (Φ.loc π) (adSp rb hb) fun v => bor (s.n v)) + _ + 2 + 2 * d ≤ _
  omega

theorem UpperTheory.V.Ws.x1 :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (s : PD T.ι (G T.F Ω) (ResidueField c'.O)), (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) s →
      ∀ (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R] (P : PD T.ι (G T.F Ω) R), (T.fr ∅).IsDef (inc h) s P →
      ∃ (a b : ℕ) (π : MvPowerSeries (Fin a) c'.O →ₐ[c'.O] R) (f : Fin b → MvPowerSeries (Fin a) c'.O), Function.Surjective π ∧
        RingHom.ker π = Ideal.span (Set.range f) ∧ b + 2 + 2 * T.d ≤ a + 2 * Nat.card T.ι := by
  intro hp Ω _ _ _ l _ c D T hF hD c' h s hs R _ _ _ P hP
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := inferInstance
  haveI := fin_res c'
  have hstd := (UpperTheory.V.Ws.std hp D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  haveI := hstd.char
  obtain ⟨tN, tM, tC, tW⟩ := X1.thFacts D T hF hD
  obtain ⟨S, K, Γ, _, _, _, _, _, _, π, ι, hG, hS, hpl, hQ⟩ := X1.linkT D T hF
  have hpr : UpperTheory.V.GC.Hypotheses₂ := ⟨⟨hp.loc.lf, hp.loc.lt, hp.loc.le, hp.gf, hp.ge, hp.pt⟩, hp.uo, hp.gw⟩
  choose ζ hζ using fun v : T.ι => X1.muLoc hp T.F Ω l (T.pl v) (T.ovl v)
  have ec := fun ρ b => X1.ecG hpr T.F Ω l T.realF S K Γ π hG hS T.ι ι T.pl hpl (ResidueField c'.O) (sp4 (ResidueField c'.O)) ρ b 6 4
  have tW' := tW (ResidueField c'.O) ((residue c'.O).comp (inc h)) (inc_loc h)
  have key := count (T.fr ∅) l (inc h) hstd π hQ s hs R P hP tN tM ζ hζ IsCC tC
    (fun g => (UpperTheory.V.GC.cycF T.F Ω l (ResidueField c'.O) g : ResidueField c'.O)) tW' T.d
  obtain ⟨m, n, ⟨π', f, q1, q2⟩, q3⟩ := key ec
  exact ⟨m, n, π', f, q1, q2, q3⟩
