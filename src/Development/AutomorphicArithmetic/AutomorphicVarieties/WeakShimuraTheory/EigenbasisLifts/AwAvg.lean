module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_coboundary_on_h_of_vanish_on_finiteIndex {K : Type*} [Field K] [CharZero K] {Γ : Type*} [Group Γ] {M : Type*}
    [AddCommGroup M] [Module K M] (R : Representation K Γ M) (z : Γ → M)
    (hco : ∀ g h, z (g * h) = z g + R g (z h)) (H N : Subgroup Γ) [N.FiniteIndex]
    (hN : ∀ g ∈ H, g ∈ N → z g = 0) :
    ∃ X, ∀ g ∈ H, z g = R g X - X := by
  classical
  have hQ : Finite (H ⧸ N.subgroupOf H) := inferInstance
  letI : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  have hzout : ∀ (g : H) (q : H ⧸ N.subgroupOf H),
      z (((g • q).out : H) : Γ) = z g + R g (z ((q.out : H) : Γ)) := by
    intro g q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf H) (g * q.out)
    have hq : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ N.subgroupOf H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hk]
    have hk0 : z ((k : H) : Γ) = 0 := hN _ (k : H).2 (Subgroup.mem_subgroupOf.mp k.2)
    simp only [Subgroup.coe_mul, hco, hk0, map_zero, add_zero]
  have hm : ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨-(((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K)⁻¹ •
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)), fun g hg => ?_⟩
  have hsum : ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) =
      ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g +
        R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) := by
    calc ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)
        = ∑ q : H ⧸ N.subgroupOf H, z (((((⟨g, hg⟩ : H) • q)).out : H) : Γ) :=
          (Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : H)) _ _ (fun q => rfl)).symm
      _ = ∑ q : H ⧸ N.subgroupOf H, (z g + R g (z ((q.out : H) : Γ))) :=
          Finset.sum_congr rfl (fun q _ => hzout ⟨g, hg⟩ q)
      _ = _ := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Finset.sum_add_distrib, map_sum, Finset.sum_const, Finset.card_univ,
            Nat.cast_smul_eq_nsmul]
  have hR : R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) =
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) -
        ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.symm
  rw [map_neg, map_smul, hR, smul_sub, smul_smul, inv_mul_cancel₀ hm, one_smul]
  abel

theorem UpperTheory.V.Ws.Eb.bkAw :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L]
      [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev),
      V.S' = s.S → ∀ {c : Coef l} {n : ℕ} (r : W.Resid (W.HidaSetting.Lev.frame V) c.O n)
      (R : Representation (PadicAlgCl l) (W.HidaSetting.Lev.frame V).Γ
        (Matrix (Fin n) (Fin n) (PadicAlgCl l))),
      ∀ z ∈ Z1 R, (∀ u, ∀ g ∈ r.Ip u, z g = 0) →
        (∀ g ∈ (W.HidaSetting.Lev.frame V).I0, z g = 0) →
        ∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal →
          ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w),
            z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X := by
  intro l _ L Ω _ _ _ _ _ _ s V hS c n r R z hz hIp hI0 w hw
  classical
  have hco : ∀ g h, z (g * h) = z g + R g (z h) := hz.2
  have hz1 : z 1 = 0 := by simpa using hco 1 1
  by_cases hwS : w ∈ V.S'
  swap
  · refine ⟨0, fun g hg => ?_⟩
    have hg1 : toGS Ω V.S' g = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.le_topologicalClosure _
        (Subgroup.subset_normalClosure
          (Set.mem_iUnion₂.mpr ⟨w, hwS, Set.mem_iUnion₂.mpr ⟨s.A w, s.hA w, hg⟩⟩)))
    rw [map_zero, sub_zero]
    exact (congrArg z hg1).trans hz1
  have hlift : ∀ g ∈ Ine (F := W.Lp L) (s.A w), ∃ h ∈ Ine (F := L) (s.A w),
      ((V.pr h : V.η.ker) : GS Ω V.S') = toGS Ω V.S' g := by
    intro g hg
    obtain ⟨h, rfl⟩ := s.unr (s.A w) w (s.hA w) hg
    exact ⟨h, hg, rfl⟩
  rw [hS] at hwS
  rcases hwS with hl | hSt | h0
  · exact absurd hl hw
  · let N : Subgroup V.frame.Γ := (⨅ i, (r.chib i).ker).map V.frame.η.ker.subtype
    let H : Subgroup V.frame.Γ := (V.frame.Iu ⟨w, hSt⟩).map V.frame.η.ker.subtype
    haveI : N.FiniteIndex := by
      have h1 : Finite (V.frame.G₀ ⧸ (⨅ i, (r.chib i).ker)) :=
        Subgroup.quotient_finite_of_isOpen' V.frame.η.ker _ V.frame.η_open (by
          rw [Subgroup.coe_iInf]
          exact isOpen_iInter_of_finite (fun i => r.chib_open i))
      have h2 : Finite (V.frame.Γ ⧸ V.frame.η.ker) :=
        Subgroup.quotient_finite_of_isOpen _ V.frame.η_open
      exact ⟨by
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite⟩
    have hN : ∀ g ∈ H, g ∈ N → z g = 0 := by
      intro g hgH hgN
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hgH
      obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp hgN
      have hba : b = a := Subtype.ext hab
      subst hba
      exact hIp ⟨w, hSt⟩ b ⟨ha, hb⟩
    obtain ⟨X, hX⟩ := exists_coboundary_on_h_of_vanish_on_finiteIndex R z hco H N hN
    refine ⟨X, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh]
    exact hX _ ⟨V.pr h, ⟨h, hh, rfl⟩, rfl⟩
  · subst h0
    refine ⟨0, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh, map_zero, sub_zero]
    exact hI0 _ ⟨h, hh, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem im_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

private theorem im_model {l : ℕ} [hl : Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {n : ℕ}
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (r : G →* GL (Fin n) (PadicAlgCl l)) (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j)
    (hE : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ E) :
    ∃ (Q : GL (Fin n) (PadicAlgCl l)) (r₀ : G →* GL (Fin n) c.O),
      ∀ g, r g * Q = Q * W.pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  letI : Algebra c.O E := (c.O.val.toRingHom.codRestrict E fun x => ((hc _).1 x.2).1).toAlgebra
  have ha : ∀ x : c.O, ((algebraMap c.O E x : E) : PadicAlgCl l) = x := fun _ => rfl
  haveI : FaithfulSMul c.O E := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    Subtype.ext (congrArg (fun z : E => (z : PadicAlgCl l)) h)
  haveI : IsFractionRing c.O E := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨N, hN⟩ := im_small (l := l) ‖(z : PadicAlgCl l)‖
    refine ⟨⟨(l : PadicAlgCl l) ^ N * z, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) z.2, by rwa [norm_mul]⟩⟩,
      (l : c.O) ^ N, Subtype.ext ?_⟩
    push_cast
    rw [ha]
    field_simp
  let m : G →* Matrix (Fin n) (Fin n) E :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hE g i j⟩
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by
    have h1 : Continuous fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hr i j).norm
    obtain ⟨C, hC⟩ := (isCompact_range h1).bddAbove
    refine ⟨C, fun g i j => le_trans ?_ (hC ⟨g, rfl⟩)⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨N, hN⟩ := im_small (l := l) C
  obtain ⟨Q, r₀, hQ⟩ := UpperTheory.V.Pa.Det.latInt (A := c.O) (F := E) m.toHomUnits ((l : c.O) ^ N)
    (pow_ne_zero _ fun h => hl0 (by simpa using congrArg Subtype.val h)) fun g i j => by
      refine ⟨⟨(l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, (hc _).2
        ⟨mul_mem (pow_mem (natCast_mem _ _) _) (hE g i j), ?_⟩⟩, Subtype.ext ?_⟩
      · rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC g i j) (norm_nonneg _)).trans hN
      · rw [ha]
        push_cast
        rfl
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l)) Q, r₀, fun g => ?_⟩
  have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l))) (hQ g)
  rw [map_mul, map_mul] at h
  convert h using 2 <;> (ext i j; rfl)

private theorem im_cont {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) :
    IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal c.O ^ N) (f g) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  rw [Ideal.Quotient.eq]
  have h2 : ((f y : PadicAlgCl l) - f x) / (l : PadicAlgCl l) ^ N ∈ c.O := (hc _).2
    ⟨div_mem (sub_mem ((hc _).1 (f y).2).1 ((hc _).1 (f x).2).1) (pow_mem (natCast_mem _ _) _), by
      rw [norm_div]
      exact div_le_one_of_le₀ hy.le (norm_nonneg _)⟩
  have h3 : f y - f x = (l : c.O) ^ N * ⟨_, h2⟩ := Subtype.ext (by push_cast; field_simp)
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)

private theorem im_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  refine ⟨IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul ℚ_[l] a y]
      exact IntermediateField.smul_mem _ hy
  · have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
    have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
    rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

theorem UpperTheory.V.Ws.Eb.intModel :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H] {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ →
        ∃ (c' : Coef l) (Q : GL (Fin n) (PadicAlgCl l)) (ρ₀ : H →* GL (Fin n) c'.O), c.O ≤ c'.O ∧ (∀ g, ρ g * Q = Q * W.pushRep (algebraMap c'.O (PadicAlgCl l)) ρ₀ g) ∧ ∀ i j, Alg.AdicCont (maximalIdeal c'.O) fun g => W.mat ρ₀ g i j := by
  intro l _ c H _ _ _ _ _ n ρ hρ
  have hr : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := fun i j =>
    (Units.continuous_val.comp hρ).matrix_elem i j
  obtain ⟨E₁, f₁, m₁⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l H n ρ hr
  obtain ⟨E₂, f₂, m₂⟩ := im_field c
  obtain ⟨c', hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  obtain ⟨Q, r₀, hQ⟩ := im_model (E₁ ⊔ E₂) c' hc ρ hr fun g i j => (le_sup_left : E₁ ≤ _) (m₁ g i j)
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  refine ⟨c', Q, r₀, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ _) (m₂ x hx).1, (m₂ x hx).2⟩, hQ, fun i j N => ?_⟩
  refine im_cont (E₁ ⊔ E₂) c' hc _ ?_ N
  have e : (fun g => ((W.mat r₀ g i j : c'.O) : PadicAlgCl l)) =
      fun g => ((Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := by
    funext g
    rw [← hQ']
    rfl
  rw [e]
  exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TrPlus
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem entry_eq {A : Type} [CommRing A] {n : ℕ} (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    X i j = (Matrix.single j i (1 : A) * X).trace := by
  rw [Matrix.trace_single_mul, one_smul]

theorem UpperTheory.V.Ws.Eb.trPlus :
    ∀ {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A), Full ρ →
        (∀ z : MonoidAlgebra A G, (∀ h : G, (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1 * z) = 0) → W.GDet.repAlg (W.mat ρ) A z = 0) ∧
        ∀ [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] [IsTopologicalGroup G], (Continuous fun g => (W.mat ρ g).trace) → Continuous ρ := by
  intro A G _ _ n ρ hF
  have hs : ∀ h : G, W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single h 1) = W.mat ρ h := by
    intro h
    simp [W.GDet.repAlg]
  have hsp : ∀ X : Matrix (Fin n) (Fin n) A, X ∈ Submodule.span A (Set.range (W.mat ρ)) := by
    intro X
    unfold Full at hF
    rw [hF]
    exact Submodule.mem_top
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      ext i j
      exact i.elim0
    have hsingle : ∀ (B : Type) [CommRing B] [Algebra A B] (g : G) (r : B),
        W.GDet.repAlg (W.mat ρ) B (MonoidAlgebra.single g r) =
          r • (W.mat ρ g).map (algebraMap A B) := by
      intro B _ _ g r
      unfold W.GDet.repAlg
      rw [MonoidAlgebra.lift_single]
      rfl
    have hmap : ∀ y : MonoidAlgebra A G,
        W.GDet.repAlg (W.mat ρ) A[X] (MonoidAlgebra.mapRingHom G (algebraMap A A[X]) y) =
          (W.GDet.repAlg (W.mat ρ) A y).map (algebraMap A A[X]) := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g => simp [MonoidAlgebra.of_apply, hsingle]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
        ext i j
        simp
      | smul r x hx =>
        have hr : r • x = MonoidAlgebra.single 1 r * x := by
          rw [Algebra.smul_def]
          rfl
        have hm : MonoidAlgebra.mapRingHom G (algebraMap A A[X]) (MonoidAlgebra.single 1 r)
            = MonoidAlgebra.single 1 (algebraMap A A[X] r) := by
          ext g
          simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
        rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, hsingle, hsingle, map_one]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have htr : ∀ y : MonoidAlgebra A G,
        (W.GDet.ofRep (W.mat ρ)).tr y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
      intro y
      have hchi : (W.GDet.ofRep (W.mat ρ)).chi y = (W.GDet.repAlg (W.mat ρ) A y).charpoly := by
        unfold W.GDet.chi
        change (W.GDet.repAlg (W.mat ρ) A[X] _).det = _
        rw [← Polynomial.algebraMap_eq, map_sub, hsingle, hmap, map_one]
        rw [Matrix.charpoly]
        congr 1
        ext i j
        by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      unfold W.GDet.tr W.GDet.lam
      rw [hchi, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
      ring
    have key : ∀ X, (X * W.GDet.repAlg (W.mat ρ) A z).trace = 0 := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hs h, ← map_mul, ← htr]
        exact hz h
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    ext i j
    exact (entry_eq _ i j).trans (key _)
  · intro _ _ _ _ hc
    have key : ∀ X, Continuous fun g => (X * W.mat ρ g).trace := by
      intro X
      induction hsp X using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simp_rw [← map_mul]
        exact hc.comp (continuous_const_mul h)
      | zero => simpa using continuous_const
      | add x y _ _ hx hy =>
        simp_rw [add_mul, Matrix.trace_add]
        exact hx.add hy
      | smul a x _ hx =>
        simp_rw [Matrix.smul_mul, Matrix.trace_smul]
        exact hx.const_smul a
    have hm : Continuous fun g => W.mat ρ g := by
      apply continuous_matrix
      intro i j
      exact (key (Matrix.single j i 1)).congr (fun g => (entry_eq _ i j).symm)
    rw [Units.continuous_iff]
    refine ⟨hm, ?_⟩
    refine (hm.comp continuous_inv).congr fun x => ?_
    show ((ρ x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = _
    rw [map_inv]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.derZero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (x' : R →ₐ[c.O] DualNumber (PadicAlgCl l)) (S : Set R), (∀ (N : ℕ) (a : R), ∃ b ∈ Algebra.adjoin c.O S, a - b ∈ maximalIdeal R ^ N) → (∀ a ∈ S, (x' a).snd = 0) → ∀ a, (x' a).snd = 0 := by
  intro l _ c R _ _ _ x' S hdense hS a
  have hadj : ∀ b ∈ Algebra.adjoin c.O S, (x' b).snd = 0 := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS x hx
    | algebraMap r =>
      rw [AlgHom.commutes]
      first
        | rfl
        | simp [TrivSqZeroExt.algebraMap_eq_inl']
    | add x y _ _ hx hy => rw [map_add (f := _), TrivSqZeroExt.snd_add, hx, hy, add_zero]
    | mul x y _ _ hx hy => simp [map_mul, TrivSqZeroExt.snd_mul, hx, hy]
  have hcont := ((coPt c R).2 x').2
  by_contra h
  have hpos : 0 < ‖(x' a).snd‖ := norm_pos_iff.mpr h
  obtain ⟨n, hn⟩ := hcont _ (half_pos hpos)
  obtain ⟨b, hb, hab⟩ := hdense n a
  have key := hn _ hab
  rw [map_sub, TrivSqZeroExt.snd_sub, hadj b hb, sub_zero] at key
  linarith
end
