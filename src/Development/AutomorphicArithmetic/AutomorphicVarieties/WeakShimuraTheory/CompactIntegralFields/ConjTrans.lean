module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Labels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ExistsTameTowerOkTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.EltOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LatSix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SuppMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsResidualRepRestrictionOfLatticeShape
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.X2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LayerEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCo

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Chain3
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

open UpperTheory.V.Ws.Chn in
theorem UpperTheory.V.Ws.chain3 :
    CohomologyHyp → SeedIII → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → T₀.Three → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hC hS Ω _ _ _ l _ c D T₀ h3 hok hth htame ι 𝔞 c₀ hc₀
  have hG : D.Good := h3.1
  have hF : T₀.Fit := ⟨hok, Or.inr ⟨h3, hth.five, hth.sb, hth.psi⟩⟩
  have ha := red_zero 𝔞 c
  have ok0 : (T₀.fr ∅).Ok (𝔞.red c) := (std hC D T₀ hF ∅ c le_rfl).2 _ _ ha
  obtain ⟨w, s, hw, hsp, hs, hsM, hsA, hsB, hseed⟩ := hS Ω l c D T₀ h3 hok hth ι 𝔞
  obtain ⟨p0, hp0, hov0⟩ := UpperTheory.exists_residualRep_restriction_of_latticeShape D hG T₀ hF _ _ ha ok0 c₀ hc₀
  obtain ⟨-, hp0P, -⟩ := goodQ D hG T₀ hF _ _ ha _ c₀ p0 hc₀ (fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw) hov0 hp0 ∅
  obtain ⟨W1, p2, hW1, hW1s, hp2, hp2Q, hp2A, hp2E⟩ :=
    gysinPs hC D T₀ hF _ _ ha {w} (by simpa using ⟨hw, hsp⟩) s hs hsM
  obtain ⟨W2, p3, p4, hW2, hW2s, hp3, hp4, hp3Q, hp4Q, h30, h42, h34, h3E⟩ :=
    gysinAl hC D T₀ hF _ _ ha W1 hW1s p0 p2 (res_mono T₀ (Finset.empty_subset _) hp0) hp2 hp0P (qP hp2Q)
  obtain ⟨T₁, hL1, ht1, hd1⟩ := diesEx D hG T₀ htame hok W2 hW2s
  refine ⟨T₁, hL1, ht1, fun T hL _ => ?_⟩
  have hT : T₀.Le T := (leFit D hG T₀ T₁ hL1).2.2.2.2.2.2 T hL
  obtain ⟨lo, -, l3, -, lf, -, -⟩ := leFit D hG T₀ T hT
  have hd : ∀ w ∈ W2, Dies l w T.F := fun w hw => dies_mono hL.le (hd1 w hw)
  obtain ⟨c₁, h, Q, hQ, hovs⟩ := hseed T hT (lo hok) (l3 hth) (hd w (hW2 (hW1 (Finset.mem_singleton_self w))))
  refine ⟨c₁, h, Q, hQ, fun u hu hur => ?_⟩
  have okT : (T.fr ∅).Ok (𝔞.red c) := (std hC D T (lf hF) ∅ c le_rfl).2 _ _ ha
  have hq := seed_res T 𝔞 hQ
  replace hs := res_mono T₀ (hW1.trans hW2) hs
  replace hp0 := res_mono T₀ (Finset.empty_subset W2) hp0
  replace hp2 := res_mono T₀ hW2 hp2
  have R := fun x hx => restrT D hG T₀ T hT hF _ _ ha W2 hW2s hd x hx (Or.inl hth.five)
  obtain ⟨q0, hq0, o0⟩ := R p0 hp0
  obtain ⟨q2, hq2, o2⟩ := R p2 hp2
  obtain ⟨q3, hq3, o3⟩ := R p3 hp3
  obtain ⟨q4, hq4, o4⟩ := R p4 hp4
  have O := overFacts D hG T₀ T hT hF _ _ ha W2 ∅
  obtain ⟨-, -, -, a1, -, -, -, a2⟩ := O p0 p3 q0 q3 hp0 hp3 hq0 hq3 o0 o3
  obtain rfl : u = q0 := a2 c₀ _ hc₀.res.pair hov0 u hur hu
  obtain ⟨-, b0, b1, -, b2, -, b4, -⟩ := O p3 p4 q3 q4 hp3 hp4 hq3 hq4 o3 o4
  obtain ⟨-, c0, c1, c2, -, -, -, -⟩ := O p4 p2 q4 q2 hp4 hp2 hq4 hq2 o4 o2
  obtain ⟨-, d0, d1, -, d2, d3, -, -⟩ := O p2 s q2 _ hp2 hs hq2 hq o2 hovs
  obtain ⟨-, e0, -, -, -, -, e4, -⟩ := O s s _ _ hs hs hq hq hovs hovs
  have hlat : LatShape D T.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ := hT.pr ▸ hc₀
  have hrt : ∀ w ∈ roots, 𝔞.red c ((frQ D T.pr (resQ T₀.F T₀.g0)).rt w (resQ T₀.F T₀.g0)) ≠ 1 := by
    rw [hT.pr]; exact fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw
  obtain ⟨-, uP, ug⟩ := goodQ D hG T (lf hF) _ _ ha _ c₀ u hlat hrt hu hur ∅
  have P3 := b1 (qP hp3Q)
  have P4 := c1 (qP hp4Q)
  have P2 := d1 (qP hp2Q)
  have M3 := b0 _ (qM hp3Q.1)
  have M4 := c0 _ (qM hp4Q.1)
  have M2 := d0 _ (qM hp2Q.1)
  have Ms := e0 _ hsM
  have s03 := a1 hp0P (qP hp3Q) (samePs_symm h30)
  have s34 := b2 (qM hp3Q.1) (qM hp4Q.1) h34
  have s42 := c2 (qP hp4Q) (qP hp2Q) h42
  have s2s := d2 (qM hp2Q.1) hsM hp2A
  have A3 := (b4 (qM hp3Q.1)).1 h3E
  have As := (e4 hsM).1 hsA
  have E2 := d3 (qP hp2Q).1 hp2E
  have g0 : (T.fr ∅).Good (𝔞.red c) u :=
    ug.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have g3 : (T.fr ∅).Good (𝔞.red c) q3 :=
    ug.elim (fun x => Or.inl ⟨(samePs_ent hur hq3 uP.1 P3.1 s03).1 x.1, Or.inr A3⟩)
      fun x => Or.inr (Or.inr (Or.inl ⟨samePs_inV hq3 P3 s03 x.1, A3⟩))
  have g4 : (T.fr ∅).Good (𝔞.red c) q4 :=
    Or.inl ⟨(samePs_ent hq4 hq2 P4.1 P2.1 s42).2 E2, Or.inr ((sameAl_ent hq3 hq4 M3 M4 s34).1 A3)⟩
  have g2 : (T.fr ∅).Good (𝔞.red c) q2 := Or.inl ⟨E2, Or.inr ((sameAl_ent hq2 hq M2 Ms s2s).2 As)⟩
  have gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := Or.inr (Or.inl ⟨As, (e4 hsM).2 hsB⟩)
  exact ⟨g0, (((Relation.ReflTransGen.single ⟨g3, lineP _ _ okT _ _ hur hq3 uP P3 s03⟩).tail
    ⟨g4, lineM _ _ okT _ _ hq3 hq4 M3 M4 s34⟩).tail ⟨g2, lineP _ _ okT _ _ hq4 hq2 P4 P2 s42⟩).tail
    ⟨gs, lineM _ _ okT _ _ hq2 hq M2 Ms s2s⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NegSqPowNeOneOfOddOrder
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem complex_conjugations_conjugate {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {σ τ : G ℚ Ω} (hσ : IsCC σ) (hτ : IsCC τ) :
    ∃ g : G ℚ Ω, g * τ = σ * g := by
  obtain ⟨j, hj⟩ := hσ
  obtain ⟨j', hj'⟩ := hτ
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have key : ∀ x, j (AlgHom.restrictNormal' j'.toRatAlgHom Ω x) = j' x := fun x => AlgHom.restrictNormal_commutes j'.toRatAlgHom Ω x
  refine ⟨AlgHom.restrictNormal' j'.toRatAlgHom Ω, AlgEquiv.ext fun x => j.injective ?_⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, key, hj, hj', key]

private theorem fieldsEx {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (hpl : ∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ H) (cc : G ℚ Ω) (hcc : IsCC cc) (hm : cc ∈ H) :
    ∃ (K F : IntermediateField ℚ Ω) (_ : NumberField K) (_ : NumberField F) (_ : IsCMField K) (_ : IsTotallyReal F) (_ : IsAbelianGalois ℚ F)
    (J : Subgroup (G ℚ Ω)), Module.finrank ℚ K = 2 ∧ Even (Module.finrank ℚ F) ∧
    (∀ p ∈ S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ J) ∧ (∀ g : G ℚ Ω, g ^ 2 ∈ J) ∧ J ≤ K.fixingSubgroup ∧
    F.fixingSubgroup ≤ H ∧ F.fixingSubgroup ⊓ K.fixingSubgroup = H ⊓ J ∧ ∀ A : ValuationSubring Ω, Ine (F := ℚ) A ⊓ F.fixingSubgroup ≤ K.fixingSubgroup := by
  obtain ⟨p, η, h⟩ := quadEx Ω (-1) S hS
  obtain ⟨p', η', h'⟩ := quadEx Ω (-1) (insert p S) fun q hq => (Finset.mem_insert.1 hq).elim (fun e => e ▸ h.prime) (hS q)
  have hk : ∀ g, g ∈ (η * η'⁻¹).ker ↔ η g = η' g := fun g => by
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  have ho : IsOpen ((η * η'⁻¹).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (H₁ := η.ker ⊓ η'.ker) (fun g hg => (hk g).2 (Eq.trans hg.1 (Eq.symm hg.2))) (h.opn.inter h'.opn)
  obtain ⟨K, _, _, hK, dK⟩ := fixAb Ω η.ker h.opn (Abelianization.commutator_subset_ker _)
  obtain ⟨F, _, _, hF, dF⟩ := fixAb Ω (H ⊓ (η * η'⁻¹).ker) (hH.inter ho) (le_inf hc (Abelianization.commutator_subset_ker _))
  have hN : H.Normal := Subgroup.Normal.of_commutator_le _ hc
  refine ⟨K, F, inferInstance, inferInstance, (fixInf Ω K).2 (fun σ hσ e => ?_) (dK.trans h.idx), (fixInf Ω F).1 fun σ hσ => ?_, inferInstance,
    η.ker ⊓ η'.ker, dK.trans h.idx, ?_, fun q hq A hA => le_inf (h.split q hq A hA) (h'.split q (Finset.mem_insert_of_mem hq) A hA),
    fun g => ⟨?_, ?_⟩, hK ▸ inf_le_left, hF ▸ inf_le_left, ?_, fun A g hg => ?_⟩
  · rw [hK, MonoidHom.mem_ker, h.cc σ hσ] at e
    exact absurd e (by decide)
  · obtain ⟨g, hg⟩ := complex_conjugations_conjugate hσ hcc
    have e : σ = g * cc * g⁻¹ := by rw [hg, mul_inv_cancel_right]
    rw [hF]
    exact ⟨e ▸ hN.conj_mem cc hm g, (hk σ).2 ((h.cc σ hσ).trans (h'.cc σ hσ).symm)⟩
  · obtain ⟨A, hA⟩ := hpl p h.prime
    obtain ⟨g, hg, e⟩ := h.ram A hA
    have e' : η' g = 1 := h'.split p (Finset.mem_insert_self _ _) A hA (Ine_le_Dec A hg)
    have h2 : (η * η'⁻¹).ker.index = 2 := by
      rw [Subgroup.index_ker]
      have ht : (η * η'⁻¹).range = ⊤ := eq_top_iff.2 fun u _ => by
        rcases Int.units_eq_one_or u with rfl | rfl
        exacts [one_mem _, ⟨g, by simp [e, e']⟩]
      rw [ht, Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
    rw [dF, even_iff_two_dvd, ← h2]
    exact Subgroup.index_dvd_of_le inf_le_right
  · show η (g ^ 2) = 1
    rw [map_pow, Int.units_sq]
  · show η' (g ^ 2) = 1
    rw [map_pow, Int.units_sq]
  · rw [hF, hK]
    ext g
    exact ⟨fun ⟨⟨a, b⟩, d⟩ => ⟨a, d, ((hk g).1 b).symm.trans d⟩, fun ⟨a, b, d⟩ => ⟨⟨a, (hk g).2 (Eq.trans b (Eq.symm d))⟩, b⟩⟩
  · rw [hK]
    by_cases hA : A.valuation (p : Ω) < 1
    · have e := hg.2
      rw [hF] at e
      exact ((hk g).1 e.2).trans (h'.split p (Finset.mem_insert_self _ _) A hA (Ine_le_Dec A hg.1))
    · exact h.unr A hA hg.1

noncomputable section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem exists_lift_of_mem_fixing {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ g' : G F Ω, resQ F g' = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

private theorem restrict_mem_fixing_subgroup {F : IntermediateField ℚ Ω} (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  (F.mem_fixingSubgroup_iff _).2 fun x hx => g.commutes ⟨x, hx⟩

private theorem restrict_inertia_mem {F : IntermediateField ℚ Ω} [NumberField F] {A : ValuationSubring Ω} {g : G F Ω}
    (hg : g ∈ Ine (F := F) A) : resQ F g ∈ Ine (F := ℚ) A := ⟨hg.1, hg.2⟩

private theorem neg_sq_pow_ne_one_of_odd_order {R : Type} [CommRing R] {y : Rˣ} {m : ℕ} (hm : Odd m) (h : y ^ m = 1) (hy : y ≠ 1) (h2 : (-1 : Rˣ) ≠ 1)
    {n : ℕ} (h0 : 0 < n) (h4 : n ≤ 4) : (-y ^ 2) ^ n ≠ 1 := by
  intro e
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow, ← pow_mul] at e
    have h8 : (2 * n).Coprime m := by
      have : 2 * n ∣ 2 ^ 3 := by
        obtain ⟨k, rfl⟩ := hn
        have : k = 1 ∨ k = 2 := by omega
        rcases this with rfl | rfl <;> norm_num
      exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 3 ((Nat.coprime_two_left).2 hm))
    exact hy (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h8 (orderOf_dvd_of_pow_eq_one e) (orderOf_dvd_of_pow_eq_one h)))
  · have e2 : ((-y ^ 2) ^ n) ^ m = 1 := by rw [e, one_pow]
    rw [← pow_mul, (hn.mul hm).neg_pow, ← pow_mul, ← mul_assoc, mul_comm _ m, pow_mul, h, one_pow] at e2
    exact h2 e2

private abbrev bU (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O : c.O →* ResidueField c.O)

private def sgnP (pr : Bool) : ℤ := if pr then -1 else 1

private theorem reduction_cyclotomic_char_eq (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (chiO ℚ Ω l c.O g) = bU c (D.om g) :=
  Units.ext (hD.om_bar g).symm

private theorem reduction_alpha_eq_xi (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (D.al g) = bU c (D.ξ g) := by
  simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, reduction_cyclotomic_char_eq D hD, mul_inv_cancel, one_mul]

private theorem reduction_psi_eq_omega_pow (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (D.Psi g) = bU c (D.om g) ^ D.e * bU c (D.ψ g) := by
  simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, map_mul, map_pow, reduction_cyclotomic_char_eq D hD]

private theorem character_ratios_eq (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * (chi D pr 1 g)⁻¹ = D.al g ∧ chi D pr 0 g * (chi D pr 2 g)⁻¹ = D.Psi g ^ sgnP pr ∧
      chi D pr 0 g * (chi D pr 3 g)⁻¹ = D.al g * D.Psi g ^ sgnP pr := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, sgnP, mul_comm]

private def del (D : Raw Ω c) (pr : Bool) : G ℚ Ω →* (ResidueField c.O)ˣ :=
  (bU c).comp (D.al ^ 2 * (D.Psi ^ sgnP pr)⁻¹)

private theorem del_iff (D : Raw Ω c) (hD : D.Good) (pr : Bool) (g : G ℚ Ω) :
    g ∈ (del D pr).ker ↔ bU c (D.ξ g) ^ 2 = (bU c (D.om g) ^ D.e * bU c (D.ψ g)) ^ sgnP pr := by
  rw [MonoidHom.mem_ker, ← reduction_alpha_eq_xi D hD, ← reduction_psi_eq_omega_pow D hD]
  simp only [del, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, MonoidHom.zpow_apply, map_mul, map_inv,
    map_pow, map_zpow, mul_inv_eq_one]

private theorem reduced_character_quotient_eq (D : Raw Ω c) (hD : D.Good) (pr : Bool) {g : G ℚ Ω} (hg : g ∈ (del D pr).ker) (i : Fin 4) :
    bU c (chi D pr i g) = bU c (chi D pr 0 g) * (bU c (D.ξ g) ^ (i : ℕ))⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := character_ratios_eq D pr g
  have h := (del_iff D hD pr g).1 hg
  rw [← reduction_psi_eq_omega_pow D hD, ← map_zpow] at h
  have k1 := congrArg (bU c) h1
  have k2 := congrArg (bU c) h2
  have k3 := congrArg (bU c) h3
  simp only [map_mul, map_inv, reduction_alpha_eq_xi D hD, ← h] at k1 k2 k3
  fin_cases i
  · simp
  · simp [← k1]
  · simp [← k2]
  · show bU c (chi D pr 3 g) = _ * (_ ^ 3)⁻¹
    rw [pow_succ', ← k3]; simp

private theorem residual_root_character_eq_pow {D : Raw Ω c} (hD : D.Good) (T : Tower D) (hF : T.F.fixingSubgroup ≤ (del D T.pr).ker) (w : ℤ × ℤ) (g : G T.F Ω) :
    T.rb w g = ((bU c (D.ξ (resQ T.F g)) ^ (w.1 + 2 * w.2) : (ResidueField c.O)ˣ) : ResidueField c.O) := by
  obtain ⟨h1, h2, -⟩ := character_ratios_eq D T.pr (resQ T.F g)
  have h := (del_iff D hD T.pr _).1 (hF (restrict_mem_fixing_subgroup g))
  rw [← reduction_psi_eq_omega_pow D hD, ← map_zpow] at h
  have e : (T.fr ∅).rt w g = D.al (resQ T.F g) ^ w.1 * (D.Psi (resQ T.F g) ^ sgnP T.pr) ^ w.2 := by
    rw [← h1, ← h2]; rfl
  have e2 : bU c ((T.fr ∅).rt w g) = bU c (D.ξ (resQ T.F g)) ^ (w.1 + 2 * w.2) := by
    rw [e, map_mul, map_zpow, map_zpow _ _ w.2, ← h, reduction_alpha_eq_xi D hD, zpow_add, zpow_mul]; rfl
  rw [← e2]; rfl

private theorem residual_rep_trivial_iff (D : Raw Ω c) (g : G ℚ Ω) : D.rbar g = 1 ↔ bU c (D.al g) = 1 ∧ bU c (D.Psi g) = 1 := by
  have key : ∀ i j, D.rbar g i j = residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) := fun _ _ => rfl
  constructor
  · intro h
    have h1 := key 1 1
    have h2 := key 2 2
    rw [h, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at h1 h2
    exact ⟨Units.ext h2.symm, Units.ext h1.symm⟩
  · rintro ⟨h1, h2⟩
    have h3 : ∀ i, residue c.O (D.ps i g : c.O) = 1 := fun i => by
      have : bU c (D.ps i g) = 1 := by
        fin_cases i <;> simp [Raw.ps, Raw.th, h1, h2]
      exact congrArg Units.val this
    ext i j
    rw [key]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, h3]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, map_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.exists_tame_tower_ok_three :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∀ pr, LabOk D pr → ∃ T : Tower D, T.pr = pr ∧ T.Ok ∧ T.Three ∧ TameL l T.F := by
  intro Ω _ _ _ l hl c D hC pr hlab
  have hD := hC.1
  obtain ⟨h5, he, hSb, ⟨m, -, hlm, hm⟩, hIl⟩ := large₂.host3 D hC
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun g => (Ideal.Quotient.eq).1 (hD.om_bar g)⟩
  obtain ⟨-, -, -, o4, -, o6, o7, -⟩ := (omT Ω l c).2 D.om hom
  have hl2 : l.Coprime 2 := (Nat.coprime_primes hl.out Nat.prime_two).2 hD.l_odd
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right _)
  have h2e : ∀ g, D.om (g ^ 2) ^ D.e = 1 := fun g => by
    obtain ⟨k, hk⟩ := he
    rw [map_pow, ← pow_mul, hk, pow_mul, ← MonoidHom.pow_apply, hD.om_pow, MonoidHom.one_apply, one_pow]
  have hsq : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ^ 2 ∈ (del D pr).ker := fun A hA g hg => by
    obtain ⟨a1, a2⟩ := hIl A hA (pow_mem hg 2)
    rw [del_iff D hD, ← map_pow _ _ D.e, h2e, MonoidHom.mem_ker.1 a1, MonoidHom.mem_ker.1 a2]
    simp
  have hopen : IsOpen ((del D pr).ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := D.ξ.ker ⊓ D.ψ.ker ⊓ D.om.ker) ?_ ((hD.xi_open.inter hD.psi_open).inter o4)
    rintro g ⟨⟨a1, a2⟩, a3⟩
    rw [del_iff D hD, MonoidHom.mem_ker.1 a1, MonoidHom.mem_ker.1 a2, MonoidHom.mem_ker.1 a3]
    simp
  have hcc : D.cc ∈ (del D pr).ker := by
    rw [del_iff D hD, ← reduction_psi_eq_omega_pow D hD, hD.xi_odd, hD.Psi_even, ← map_pow]
    simp
  obtain ⟨K, F, _, _, _, _, _, J, hK, hev, hJS, hJ2, hJK, hFH, hFK, hunr⟩ :=
    fieldsEx (fun p hp => ⟨_, hD.pl_over p hp⟩) D.S hD.S_prime (del D pr).ker hopen (Abelianization.commutator_subset_ker _) D.cc hD.isCC hcc
  have hL : ∀ g, g ∈ (del D pr).ker → g ∈ J → ∃ g' : G F Ω, resQ F g' = g ∧ resQ F g' ∈ K.fixingSubgroup := fun g a b => by
    have h : g ∈ F.fixingSubgroup ⊓ K.fixingSubgroup := hFK ▸ ⟨a, b⟩
    obtain ⟨g', rfl⟩ := exists_lift_of_mem_fixing h.1
    exact ⟨g', rfl, h.2⟩

  obtain ⟨g1, i1, x1, p1, w1⟩ := large₂.eltTwo D hC
  obtain ⟨g2, m', hm', hlm', w2, x2, x3, x4⟩ := large₂.eltOdd D hC (sgnP pr) (by cases pr <;> simp [sgnP])
  have hx : D.ξ (g1 * g2 ^ 2) = -D.ξ g2 ^ 2 := by rw [map_mul, map_pow, x1, neg_one_mul]
  have hw : D.om (g1 * g2 ^ 2) = 1 := by rw [map_mul, map_pow, w1, w2, one_pow, one_mul]
  obtain ⟨g0, hg0, hg0K⟩ := hL (g1 * g2 ^ 2) (by
      rw [del_iff D hD, hx, hw, map_one, one_pow, one_mul, map_mul, p1, one_mul, ← map_pow, ← map_zpow, neg_sq, x2, map_pow D.ψ,
        ← zpow_natCast, ← zpow_natCast (D.ψ g2), ← zpow_mul, ← zpow_mul, mul_comm])
    (J.mul_mem (hJS 2 hD.two_mem _ (hD.pl_over 2 Nat.prime_two) (Ine_le_Dec _ i1)) (hJ2 g2))
  have hord : ∀ n : ℕ, 0 < n → n ≤ 4 → bU c (D.ξ (resQ F g0)) ^ n ≠ 1 := fun n h0 h4 e => by
    rw [hg0, hx, ← map_pow] at e
    refine neg_sq_pow_ne_one_of_odd_order hm' x3 x4 (fun h => ?_) h0 h4 (large₂.redOne c (2 * m') (hl2.mul_right hlm') _ ?_ (congrArg Units.val e))
    · have h' : ((-1 : c.O) : PadicAlgCl l) = ((1 : c.O) : PadicAlgCl l) := congrArg _ (congrArg Units.val h)
      norm_num at h'
    · rw [← pow_mul, ((even_two_mul m').mul_left n).neg_pow, ← pow_mul, show 2 * (n * (2 * m')) = m' * (4 * n) by ring, pow_mul, x3, one_pow]

  obtain ⟨g3, i3, w3⟩ : ∃ g ∈ D.Ip l, D.om (g ^ 2) ≠ 1 := by
    by_contra hc
    push Not at hc
    have := Nat.le_of_dvd two_pos (o7 _ (hD.pl_over l hl.out) 2 fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.pow_apply, ← map_pow]; exact hc g hg)
    omega
  obtain ⟨g4, hg4, hg4K⟩ := hL (g3 ^ 2) (hsq _ (hD.pl_over l hl.out) g3 i3) (hJ2 g3)
  obtain ⟨T, rfl, rfl, rfl, hT0⟩ := mkTower D hD pr K F hK (fun A hA => (hJS l hD.l_mem A hA).trans hJK) g0
  have hrb := residual_root_character_eq_pow hD T hFH
  have hq := fun (g : G T.F Ω) => reduced_character_quotient_eq D hD T.pr (hFH (restrict_mem_fixing_subgroup g))
  have hdist : ∀ i j : Fin 4, bU c (chi D T.pr i (resQ T.F g0)) = bU c (chi D T.pr j (resQ T.F g0)) → i = j := by
    have key : ∀ i j : Fin 4, i < j → bU c (D.ξ (resQ T.F g0)) ^ (i : ℕ) ≠ bU c (D.ξ (resQ T.F g0)) ^ (j : ℕ) := fun i j hij e => by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (show (i : ℕ) < j from hij)
      rw [hk, add_assoc, pow_add, left_eq_mul] at e
      exact hord (k + 1) (by omega) (by omega) e
    intro i j e
    rw [hq, hq _ j, mul_right_inj, inv_inj] at e
    rcases lt_trichotomy i j with h | h | h
    exacts [absurd e (key i j h), h, absurd e.symm (key j i h)]
  have hz : ∀ n : ℤ, n ≠ 0 → n.natAbs ≤ 4 → bU c (D.ξ (resQ T.F g0)) ^ n ≠ 1 := fun n h0 h4 e =>
    hord n.natAbs (Int.natAbs_pos.2 h0) h4 (orderOf_dvd_iff_pow_eq_one.1 (Int.ofNat_dvd_left.1 (orderOf_dvd_iff_zpow_eq_one.2 e)))
  refine ⟨T, rfl, ⟨hlab, hev, fun A g hg => hunr A ⟨restrict_inertia_mem hg, restrict_mem_fixing_subgroup g⟩, fun p hp A hA => (hJS p hp A hA).trans hJK, fun w => ⟨g4, hg4K, ?_⟩,
    fun w hw => ⟨g0, hg0K, ?_⟩, fun η _ hη h => ?_, ⟨wAl, by decide, fun n h0 h4 => ⟨g0, hg0K, ?_⟩⟩, fun A hA g hg hr => ?_, ⟨m, hlm, fun g _ => ?_⟩,
    fun A hA g hg => ?_, fun i j hij e => ?_,
    UpperTheory.V.Keep.loc3 D hD h5 T fun A hA g hg =>
      (show g ^ 2 ∈ T.F.fixingSubgroup ⊓ T.K.fixingSubgroup from hFK ▸ ⟨hsq A hA g hg, hJ2 g⟩).1⟩, ⟨h5, hSb, ⟨m, hlm, hm⟩, fun g => ?_⟩, fun A hA g hg => ⟨2, hl2, ?_⟩⟩
  · rw [hrb, hg4, MonoidHom.mem_ker.1 (hIl _ (hD.pl_over l hl.out) (pow_mem i3 2)).1, map_one, one_zpow]
    exact fun e => w3 (large₂.redOne c (l - 1) hl1 _ (by rw [← MonoidHom.pow_apply, hD.om_pow]; rfl) e.symm)
  · rw [hrb, Ne, Units.val_eq_one]
    revert w
    exact fun w hw => hz _ ((by decide : ∀ w ∈ roots, w.1 + 2 * w.2 ≠ 0) w hw) ((by decide : ∀ w ∈ roots, (w.1 + 2 * w.2).natAbs ≤ 4) w hw)
  · obtain ⟨j, hj⟩ := h 0
    have h1 := hj ⟨g0, hg0K⟩
    rw [hη ⟨g0, hg0K⟩ (by show D.om (resQ T.F g0) = 1; rw [hg0, hw]), Units.val_one, one_mul] at h1
    obtain rfl : 0 = j := hdist 0 j (Units.ext h1)
    ext g
    exact (mul_eq_right₀ (bU c (chi D T.pr 0 (resQ T.F g))).ne_zero).1 (hj g)
  · rw [hrb, ← Units.val_pow_eq_pow_val, Ne, Units.val_eq_one]
    simpa [wAl] using hord n h0 h4
  · have h1 := ((residual_rep_trivial_iff D _).1 hr).2
    rw [reduction_psi_eq_omega_pow D hD, MonoidHom.mem_ker.1 (o6 A (hA l (Finset.mem_singleton_self l)) (restrict_inertia_mem hg)), map_one, one_pow, one_mul] at h1
    exact large₂.redOne c m hlm _ (by rw [← MonoidHom.pow_apply, hm]; rfl) (congrArg Units.val h1)
  · rw [← MonoidHom.pow_apply, hm]; rfl
  · have a1 := MonoidHom.mem_ker.1 (hIl A hA (restrict_inertia_mem hg)).1
    have h := (del_iff D hD T.pr _).1 (hFH (restrict_mem_fixing_subgroup g))
    rw [← reduction_psi_eq_omega_pow D hD, a1, map_one, one_pow] at h
    refine (residual_rep_trivial_iff D _).2 ⟨by rw [reduction_alpha_eq_xi D hD, a1, map_one], ?_⟩
    revert h
    cases T.pr <;> simp [sgnP, eq_comm]
  · rw [hT0] at e
    exact hij (hdist i j (Units.ext e))
  · rw [hrb, hrb, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]; rfl
  · have h : g ^ 2 ∈ T.F.fixingSubgroup ⊓ T.K.fixingSubgroup := hFK ▸ ⟨hsq A hA g hg, hJ2 g⟩
    exact h.1
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩

private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    (res O O : O →+* ResidueField O) = residue O := RingHom.ext fun x => (res O O).commutes x

private theorem last_step (hC : CohomologyHyp) (hPM : PMEx) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (hD : T.Deep) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (C : ℕ)
    (hB : ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Bounds a T.d C)
    (hd : 30 * (C + 1) * (C + 1) ≤ T.d) {c₁ : Coef l} {h₁ : c.O ≤ c₁.O} {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPair ι h₁ Q)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V)))
    (hch : (T.fr ∅).Chain (𝔞.red c) (P.map (residue 𝔞.V)) (Q.map (𝔞.red c₁))) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V), T.PM ι X J ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧ X.P.map y = P := by
  obtain ⟨c₂, k₂⟩ := chainDesc 𝔞 c (T.fr ∅) _ _ hr hch
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨c₄, k₄⟩ := hPM Ω l c D T hF hD ι
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c₂
  obtain ⟨d₂, a₃, a₄⟩ := (coefSup l).1 c₃ c₄
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ d₂
  have e₁ : c₁.O ≤ c'.O := a₁.trans b₁
  have h : c.O ≤ c'.O := h₁.trans e₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨J, hJ⟩ := k₄ c' h (a₄.trans b₂) X
  obtain ⟨s, t, es, et, rs, cst⟩ := k₂ c' h (a₂.trans b₁)
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' (a₃.trans b₂)
  have inj := (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') s).2.2
  have loc : ∀ {d : Coef l} (e : d.O ≤ c'.O), maximalIdeal d.O ≤ (maximalIdeal c'.O).comap (inc e) := fun {d} e x hx hu => by
    have h2 : IsUnit (𝔞.a d x) := 𝔞.compat d c' e x ▸ hu.map (𝔞.a c')
    exact hx (IsLocalHom.map_nonunit x h2)

  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc e₁)) = 𝔞.red c₁ :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c₁ c' e₁ x)
  have lQ : (T.fr ∅).Lifts (inc h) t (Q.map (inc e₁)) := by
    refine ⟨hQ.pair.map (inc e₁), hQ.cont.map _ (loc e₁), inj ?_⟩
    show ((Q.map _).map _).map _ = t.map _
    rw [et, res_self, PD.map_map, PD.map_map, ← jc]
    rfl
  obtain ⟨f₁, hf₁⟩ := X.univ c'.O t _ (Asm.chain_end rs cst).1 lQ
  have sd := hJ.seed ((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁) (by
    have e : X.P.map (((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁ : X.A →ₐ[c'.O] PadicAlgCl l) : X.A →+* PadicAlgCl l) =
        Q.map (algebraMap c₁.O (PadicAlgCl l)) := by
      show (X.P.map (f₁ : X.A →+* c'.O)).map (algebraMap c'.O (PadicAlgCl l)) = _
      rw [hf₁]
      rfl
    rw [e]
    exact hQ.seed)
  have s₁ : X.SomeIn J (RingHom.ker ((res c'.O c'.O).comp f₁)) := Asm.someIn_of_locZero X J _ sd fun z hz => by
    have h0 : f₁ z = 0 := Subtype.ext hz
    show res c'.O c'.O (f₁ z) = 0
    rw [h0, map_zero]
  have e₁' : X.P.map (((res c'.O c'.O).comp f₁ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = t := by
    show (X.P.map (f₁ : X.A →+* c'.O)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = t
    rw [hf₁]
    exact lQ.red

  have lR : (T.fr ∅).Lifts (inc h) s QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, inj ?_⟩
    · rw [← RingHom.comp_assoc, fa]
      have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
      rw [this]
      exact hp
    · show (QR.map _).map _ = s.map _
      rw [es, PD.map_map, PD.map_map, fr]
  obtain ⟨f₀, hf₀⟩ := X.univ R s _ rs lR
  have e₀ : X.P.map (((res c'.O R).comp f₀ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = s := by
    show (X.P.map (f₀ : X.A →+* R)).map (res c'.O R : R →+* ResidueField c'.O) = s
    rw [hf₀]
    exact lR.red
  have all := Asm.allIn_of_chain hS X J
    (ch hC D T hF hD ι c' h X J hJ C (hB _ _ fun x hx => (residue_eq_zero_iff _).2 (loc h hx)) hd)
    ((res c'.O R).comp f₀) ((res c'.O c'.O).comp f₁) (e₀ ▸ rs) (e₀ ▸ e₁' ▸ cst) s₁
  refine ⟨c', h, X, J, f.comp (f₀ : X.A →+* R), hJ, ?_, fun b hb => ?_, Asm.zero_of_allIn X J _ all fun z hz => ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · have h0 : res c'.O R ((f₀.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) b) = 0 := by
      rw [res_map, res_eq_zero_iff]
      exact hb
    refine (residue_eq_zero_iff _).1 ((RingHom.congr_fun fr (f₀ (algebraMap X.B X.A b))).trans ?_)
    exact (congrArg (𝔞.j c') h0).trans (map_zero _)
  · have h0 : f₀ z = 0 := (map_eq_zero_iff f fi).1 hz
    show res c'.O R (f₀ z) = 0
    rw [h0, map_zero]
  · exact congrArg (fun Z => PD.map Z f) hf₀

theorem UpperTheory.V.Ws.thmA :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → SeedII → SeedIII → PMEx → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D ∨ Ctx3 D →
      ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → ProMod D ι 𝔞 r := by
  intro hC hFW h2 h3 hPM Ω _ _ _ l _ c D hD ι 𝔞 r u hK hS
  have hG : D.Good := hD.elim (·.1) (·.1)
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, hF₀, hc⟩ : ∃ T₀ : Tower D, T₀.pr = pr ∧ T₀.Fit ∧ ∀ c₀ : PD Unit (G ℚ Ω) 𝔞.k,
      LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ → ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
    rcases hD with hD | hD
    · obtain ⟨T₀, e, ok, two, tame⟩ := exists_tame_tower_ok_two D hD pr hl
      exact ⟨T₀, e, ⟨ok, .inl ⟨hD, two⟩⟩, chain2 hC h2 D T₀ hD ok two tame ι 𝔞⟩
    · obtain ⟨T₀, e, ok, three, tame⟩ := exists_tame_tower_ok_three D hD pr hl
      exact ⟨T₀, e, ⟨ok, .inr ⟨hD, three.five, three.sb, three.psi⟩⟩, chain3 hC h3 D T₀ hD ok three tame ι 𝔞⟩
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP hS)
  obtain ⟨T₁, le₁, tame, hT⟩ := hc _ lP'
  have f₁ := leFit D hG T₀ T₁ le₁
  have hF₁ := f₁.2.2.2.2.1 hF₀
  obtain ⟨C, hB⟩ := x2 hC hFW D T₁ hF₁ tame
  obtain ⟨T, m, le, lay, deep, hd⟩ := layerEx D hG T₁ hF₁ tame (30 * (C + 1) * (C + 1))
  have hF := (leFit D hG T₁ T le).2.2.2.2.1 hF₁
  obtain ⟨c₁, h₁, Q, hQ, hch⟩ := hT T le deep
  obtain ⟨P'', sm, pr'', er, ov, rs, ine⟩ := restrQ D hG T₀ T hF₀ (f₁.2.2.2.2.2.2 T le) 𝔞 P' qP' lP'
  obtain ⟨c', h, X, J, y, k1, k2, k3, k4, k5⟩ :=
    last_step hC hPM T hF deep ι 𝔞 C (hB T m le lay) hd hQ sm pr'' rs (hch _ ov rs)
  refine ⟨T, c', h, X, J, y, P'.r, hF, deep, k1, k2, k3, k4, conj_trans cP cP', qP'.pair.mult, by rw [k5, er],
    fun v i s hs => ?_⟩
  subst k5
  exact (PD.map_ψ X.P y v i s).symm.trans (ine v i s hs)
