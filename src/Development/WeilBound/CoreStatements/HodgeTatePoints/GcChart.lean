module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GcBase
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem isLocalizedModule_subtype {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    IsLocalizedModule (nonZeroDivisors A) M.subtype := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩⟩
  · have hx : algebraMap A K (x : A) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro v w hvw
      have h' : (x : A) • v = (x : A) • w := by
        simpa [Module.algebraMap_end_apply] using hvw
      rw [← algebraMap_smul K (x : A) v, ← algebraMap_smul K (x : A) w] at h'
      exact smul_right_injective Ω hx h'
    · intro v
      refine ⟨(algebraMap A K (x : A))⁻¹ • v, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul K (x : A), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · have hy : y ∈ Submodule.span K (M : Set Ω) := hM ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => exact ⟨(⟨z, hz⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨⟨m₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨m₂, s₂⟩, e₂⟩ := h₂
      refine ⟨((s₂ : A) • m₁ + (s₁ : A) • m₂, s₁ * s₂), ?_⟩
      have e₁' : (s₁ : A) • y₁ = (m₁ : Ω) := e₁
      have e₂' : (s₂ : A) • y₂ = (m₂ : Ω) := e₂
      simp only [map_add (f := _), map_smul, Submodule.subtype_apply, ← e₁', ← e₂', Submonoid.smul_def,
        Submonoid.coe_mul]
      rw [smul_add, mul_smul, mul_comm, mul_smul, smul_comm (s₂ : A) (s₁ : A) y₁,
        smul_comm (s₂ : A) (s₁ : A) y₂]
    | smul c z _ h =>
      obtain ⟨⟨m, s⟩, e⟩ := h
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
      dsimp only at hab
      have e' : (s : A) • z = (m : Ω) := e
      have hb : (b : A) • (c • z) = a • z := by
        rw [← algebraMap_smul K (b : A), smul_smul, mul_comm _ c, hab, algebraMap_smul]
      refine ⟨(a • m, b * s), ?_⟩
      rw [map_smul, Submodule.subtype_apply, ← e', Submonoid.smul_def, Submonoid.coe_mul,
        mul_comm, mul_smul, hb]
      exact smul_comm _ _ _

theorem finrank_lattice {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω]
    [IsScalarTower A K Ω] (M : Submodule A Ω) (hM : Submodule.span K (M : Set Ω) = ⊤) :
    finrank K Ω = finrank A M := by
  haveI := isLocalizedModule_subtype M hM
  rw [IsFractionRing.finrank_right_eq A K Ω]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors A) M.subtype le_rfl

private theorem rankAtStalk_eq_finrank' {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P]
    [Module R P] (q : PrimeSpectrum R) : Module.rankAtStalk P q = Module.finrank R P := by
  unfold Module.rankAtStalk
  rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P) q.asIdeal.primeCompl_le_nonZeroDivisors

theorem bc_iso : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (L : Submodule O Ω') (ι : M →ₛₗ[algebraMap A O] Ω'), M.IsFullLattice K → Module.Projective A M → L.IsFullLattice C → Submodule.span O (Set.range ι) = L → Module.finrank K Ω = Module.finrank C Ω' → ∃ j : O ⊗[A] M →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = L ∧ ∀ x, j (1 ⊗ₜ x) = ι x := by
  intro A K _ _ _ _ _ Ω _ _ _ _ M C _ v O _ _ hv _ Ω' _ _ _ _ L ι hM hproj hL hspan hdim
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : Module.Finite A M := Module.Finite.iff_fg.mpr (hM.toIsLattice.fg)
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr (hL.toIsLattice.fg)
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    rw [Submodule.mem_bot]
    have ha' : (a : O) • (x : Ω') = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O)] at ha'
    have hne : algebraMap O C (a : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  letI : Module A Ω' := Module.compHom Ω' (algebraMap A O)
  haveI : IsScalarTower A O Ω' := ⟨fun a o x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ι' : M →ₗ[A] Ω' :=
    { toFun := ι, map_add' := map_add ι
      map_smul' := fun a x => by rw [LinearMap.map_smulₛₗ]; rfl }
  let j : O ⊗[A] M →ₗ[O] Ω' := ι'.liftBaseChange O
  have hj : ∀ x, j (1 ⊗ₜ x) = ι x := fun x => by
    show (1 : O) • ι x = ι x
    exact one_smul _ _
  have hrange : LinearMap.range j = L := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul o x =>
        show o • ι x ∈ L
        exact L.smul_mem o (hspan ▸ Submodule.subset_span ⟨x, rfl⟩)
      | add t₁ t₂ h₁ h₂ => rw [map_add (f := _)]; exact L.add_mem h₁ h₂
    · rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hj x⟩
  refine ⟨j, ?_, hrange, hj⟩
  let j' : O ⊗[A] M →ₗ[O] L := j.codRestrict L (fun t => hrange ▸ LinearMap.mem_range_self j t)
  have hsurj : Function.Surjective j' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hbij : Function.Bijective j' := by
    apply Module.bijective_of_surjective_of_rankAtStalk_eq hsurj
    intro m _
    rw [Module.rankAtStalk_baseChange, rankAtStalk_eq_finrank', rankAtStalk_eq_finrank', ← finrank_lattice M hM.span_eq_top, hdim,
      finrank_lattice L hL.span_eq_top]
  intro t₁ t₂ h
  exact hbij.1 (Subtype.ext h)

end PositivityTheory.HtPt.Gc
end

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem {x : Ω} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem ht_mem_span {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι)
    {t : V} (ht : t ∈ P.T) :
    P.ht t ∈ Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
  classical
  set S := Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'})
  have hp : ∀ y ∈ P.om, (p ^ R) • y ∈ S := by
    intro y hy
    rw [← hred.span_eq] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      refine Submodule.subset_span ⟨(p ^ R) • m, ?_, map_nsmul ι _ _⟩
      have := pow_smul_mem D m.2
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
      exact this
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact S.add_mem ha hb
    | smul a w _ hw => rw [smul_comm]; exact S.smul_mem a hw
  have hT : P.T ≤ S.comap (P.ht.restrictScalars O) := by
    rw [P.free.2.2, Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    have h1 : P.tate (Pi.single i (RingOfIntegers.basis E k)) =
        P.ρ (RingOfIntegers.basis E k) (P.t i) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at he
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ S
    rw [← sub_eq_iff_eq_add.2 he]
    exact S.sub_mem (Submodule.subset_span ⟨_, h_mem_om' D _, rfl⟩) (hp y hy)
  exact hT ht

end

theorem chart_ii : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ hκ hP hT
  refine ⟨om'_le D, fun x hx => ?_⟩
  have hp0 : algebraMap A K ((p : A) ^ R) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlat : D.om'.IsFullLattice K := by
    letI : D.om'.IsLattice K :=
      Submodule.IsLattice.of_fg K (Submodule.FG.of_le D.om_lat.fg (om'_le D))
    refine ⟨?_⟩
    apply top_unique
    rw [← D.om_lat.span_eq_top]
    apply Submodule.span_le.2
    intro x hx
    have hh := Submodule.subset_span (R := K) (pow_smul_mem D hx)
    rw [← IsScalarTower.algebraMap_smul K] at hh
    have hh' := (Submodule.span K (D.om' : Set Ω)).smul_mem
      (algebraMap A K ((p : A) ^ R))⁻¹ hh
    simpa [smul_smul, hp0] using hh'
  refine test_incl A K Ω D.om' _ hlat hP fun q hq h1 => ?_
  by_cases hpq : (p : A) ∈ q
  swap
  · refine ⟨(p : A) ^ R, fun h => hpq (hq.mem_of_pow_mem R h), ?_⟩
    exact pow_smul_mem D (D.om.smul_mem κ hx)
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    hT q hq h1 hpq
  letI : Algebra A O := φ.toAlgebra
  obtain ⟨j, hj, -, hj1⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  obtain ⟨s, hs, hsx⟩ := test_descend A K C v O hv q D.om (D.om'.comap D.om.subtype)
    (κ • ⟨x, hx⟩) hq h1 hφ hcen (by
      obtain ⟨t, ht, hte⟩ := P.κ_mem (ι ⟨x, hx⟩)
        (hred.span_eq ▸ Submodule.subset_span ⟨_, rfl⟩)
      have h2 := ht_mem_span D φ P ι hred ht
      rw [hte, ← ι.map_smulₛₗ, ← hj1] at h2
      have h3 : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) =
          (Submodule.span O ((fun y : D.om => (1 : O) ⊗ₜ[A] y) ''
            (D.om'.comap D.om.subtype : Set D.om))).map j := by
        rw [Submodule.map_span, Set.image_image]
        simp only [hj1]
        rfl
      rw [h3] at h2
      obtain ⟨z, hz, hze⟩ := h2
      rwa [← hj hze])
  exact ⟨s, hs, hsx⟩

end PositivityTheory.HtPt.Gc
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GiFree
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gi

theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c La _ _ EF N u h
  classical
  have := h.free
  have := h.finite
  let ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La) :=
    (Module.End.baseChangeHom ℤ C La).toRingHom.comp (Module.toModuleEnd ℤ La)
  have hρ : ∀ (a : 𝓞 E) (s : C) (x : La), ρ a (s ⊗ₜ x) = s ⊗ₜ (a • x) := fun a s x => rfl
  let e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C := LinearMap.BilinForm.baseChange C EF
  have he : ∀ (s t : C) (x y : La), e (s ⊗ₜ x) (t ⊗ₜ y) = (EF x y : C) * (s * t) := fun s t x y => by
    simp only [e, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  have he1 : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C) := fun x y => by rw [he]; simp
  let T : Submodule O (C ⊗[ℤ] La) := Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x)
  have hT : ∀ x : La, (1 : C) ⊗ₜ[ℤ] x ∈ T := fun x => Submodule.subset_span ⟨x, rfl⟩
  let b := Module.Free.chooseBasis ℤ La
  let B := Algebra.TensorProduct.basis C b
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  choose b' hb' using fun i => h.unimod.2 (b.coord i)
  have hrep : ∀ i y, e (1 ⊗ₜ b' i) y = B.repr y i := by
    intro i y
    have : e (1 ⊗ₜ b' i) = B.coord i := B.ext fun j => by
      rw [Module.Basis.coord_apply, B.repr_self, hB, he1, hb', Module.Basis.coord_apply, b.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]; rfl
  have hskew : ∀ x y, EF x y = -EF y x := fun x y => by
    have := h.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h.alt] at this
    linarith
  have eskew : ∀ x y, e x y = -e y x := by
    intro x y
    induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
      | tmul t y => rw [he, he, hskew]; push_cast; ring
  have hTb : T = Submodule.span O (Set.range B) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change (1 : C) ⊗ₜ[ℤ] x ∈ Submodule.span O (Set.range B)
      rw [← b.sum_repr x, tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [tmul_smul, ← hB]
      exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := B) i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hB]; exact hT _
  have hsp : Submodule.span C (T : Set (C ⊗[ℤ] La)) = ⊤ := by
    rw [hTb, Submodule.span_span_of_tower, B.span_eq]
  let w : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C ⊗[ℤ] La := fun q =>
    ρ (RingOfIntegers.basis E q.2) (1 ⊗ₜ u q.1)
  have hTw : T = Submodule.span O (Set.range w) := by
    apply le_antisymm
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : O)}) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [hTb]; exact Submodule.fg_span (Set.finite_range B)
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, x', rfl⟩ := h.span x
        change (1 : C) ⊗ₜ[ℤ] _ ∈ Submodule.span O (Set.range w) ⊔ Ideal.span {(p : O)} • T
        rw [tmul_add]
        refine Submodule.add_mem_sup ?_ ?_
        · rw [tmul_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [← (RingOfIntegers.basis E).sum_repr (a i), Finset.sum_smul, tmul_sum]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [smul_assoc, tmul_smul]
          exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := w) (i, k))) _
        · rw [tmul_smul, ← Nat.cast_smul_eq_nsmul O]
          exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hT _)
    · rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact hT _
  refine ⟨ρ, T, e, fun a x => hρ a 1 x, rfl, ⟨?_, hsp, hTw⟩, he1, fun x => ?_, fun y hy => ?_, ?_, fun a x y => ?_⟩
  · refine linearIndependent_of_top_le_span_of_card_eq_finrank (b := w) ?_ ?_
    · rw [← hsp, hTw, Submodule.span_span_of_tower]
    · rw [Module.finrank_baseChange, h.rank, Fintype.card_prod, Fintype.card_fin,
        ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  · have := eskew x x
    have h2 : (2 : C) * e x x = 0 := by linear_combination this
    simpa using h2
  · exact B.ext_elem fun i => by rw [← hrep, hy]; simp
  · apply le_antisymm
    · intro y hy
      rw [hTb, ← B.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := hy _ (hT (b' i))
      rw [← hrep, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩ x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        exact ⟨(EF x y : O), by rw [he1, map_intCast]⟩
      | zero => simp
      | add x x' _ _ hx hx' =>
        rw [map_add (f := _), LinearMap.add_apply]; exact Subring.add_mem _ hx hx'
      | smul o x _ hx =>
        rw [← algebraMap_smul C o x, map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact Subring.mul_mem _ ⟨o, rfl⟩ hx
  · induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul t y => rw [hρ, hρ, he, he, h.adj]

end PositivityTheory.HtPt.Gi
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MhQuot
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem quot : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsFinite Γ₁.G.hom → IsFinite Γ.G.hom → Flat a.left → Surjective a.left → quotOrder α (Γ₁.btOrder ⊤) = Γ.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hpt hfin₁ hfin hfl hsurj
  haveI : IsAffine Γ.G.left := isAffine_of_isAffineHom Γ.G.hom
  haveI : IsAffine Γ₁.G.left := isAffine_of_isAffineHom Γ₁.G.hom
  have hα : Function.Surjective α := by
    intro t
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    obtain ⟨y, hy⟩ := a.left.surjective ((Γ.pt t).left z)
    have hgen : (Γ₁.G.hom y).asIdeal = ⊥ := by
      have e1 : Γ₁.G.hom y = Γ.G.hom ((Γ.pt t).left z) := by
        rw [← hy, ← Scheme.Hom.comp_apply, Over.w a]
      rw [e1, ← Scheme.Hom.comp_apply, Over.w (Γ.pt t)]
      show (PrimeSpectrum.comap (algebraMap R (FractionRing R)) z).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal]
      have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
      rw [hz]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    obtain ⟨h, x, hx⟩ := Γ₁.pt_onto y hgen
    refine ⟨h, Γ.pt_inj (α h) t x z ?_⟩
    have e2 : a.left ((Γ₁.pt h).left x) = (Γ.pt (α h)).left x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hpt h]
    rw [← e2, hx, hy]
  have valAt_top : ∀ {B : Type} [CommRing B] {X : Scheme.{0}}
      (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)),
      valAt x ⊤ h s = val x s := by
    intro B _ X x h s
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have sec_ext : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)}, (∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') → s = s' := by
    intro T _ _ Γ s s' h
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [valAt_top, map_sub, h, sub_self]
  have mem_top_iff : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → R), f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    intro T _ _ Γ f
    have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
        (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
      intro B _ X x U hx a b
      simp only [valAt, map_sub]
    constructor
    · intro hf t
      rw [Twhopf.mem_order] at hf
      have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
          ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
            valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
        fun g => hf t g (by simp)
      choose U hgU s hs using hreg
      obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
        (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
          intro g g'
          rw [← sub_eq_zero]
          apply Twhopf.sec_inj R T Γ _ _
          intro h hh
          have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
          have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
          refine (hsub _ _ hh _ _).trans ?_
          erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
          rw [hs, hs, sub_self])
      refine ⟨g0, fun h => ?_⟩
      have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
      let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
      have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
        Twhopf.top_le_of_mem _ z (hgU _)
      refine (valAt_top _ htop g0).symm.trans ?_
      refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
      erw [hglue ((Γ.pt h).left z)]
      exact hs _ h hh
    · intro hf
      rw [Twhopf.mem_order]
      intro t g _
      obtain ⟨s, hs⟩ := hf t
      unfold QFGroup.RegularAt
      exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩
  ext f
  rw [quotOrder, Subalgebra.mem_comap, mem_top_iff, mem_top_iff]
  constructor
  · intro hf t
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank R T Γ
    obtain ⟨s0, hs0⟩ := (mem_top_iff Γ _).1 (hd (fun x => f (t * x))) 1
    obtain ⟨h0, rfl⟩ := hα t
    obtain ⟨s₁, hs₁⟩ := hf h0
    have key : a.left.appTop s0 = a.left.appTop (pb Γ.G.hom d) * s₁ := by
      apply sec_ext Γ₁
      intro h
      rw [map_mul, ← val_comp, ← val_comp, ← Over.comp_left, hpt h, hs0, val_pb (Over.w (Γ.pt (α h))), hs₁, ← map_mul]
      congr 1
      show d * f (α h0 * (1 * α h)) = d * f (α (h0 * h))
      rw [_root_.one_mul, MonoidHom.map_mul]
    have e : Spec.map a.left.appTop = Γ₁.G.left.isoSpec.inv ≫ a.left ≫ Γ.G.left.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have hff : a.left.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff _).1 ⟨by rw [e]; infer_instance, by rw [e]; infer_instance⟩
    letI : Algebra Γ(Γ.G.left, ⊤) Γ(Γ₁.G.left, ⊤) := a.left.appTop.hom.toAlgebra
    have hmem : s0 ∈ Ideal.span {pb Γ.G.hom d} := by
      rw [← @Ideal.comap_map_eq_self_of_faithfullyFlat _ _ _ _ _ hff (Ideal.span {pb Γ.G.hom d}),
        Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s₁, key⟩
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨s, fun h => ?_⟩
    have e3 := hs0 h
    rw [← hs, map_mul, val_pb (Over.w (Γ.pt h))] at e3
    have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hd0
    apply mul_right_cancel₀ hd'
    rw [e3, ← map_mul]
    congr 1
    show d * f (α h0 * (1 * h)) = f (α h0 * h) * d
    rw [_root_.one_mul, mul_comm]
  · intro hf h0
    obtain ⟨s, hs⟩ := hf (α h0)
    refine ⟨a.left.appTop s, fun h => ?_⟩
    rw [← val_comp, ← Over.comp_left, hpt h, hs]
    exact congrArg _ (congrArg f (map_mul α h0 h).symm)

end PositivityTheory.HtPt.Mh
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsBialgHom
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twpol

open Coalgebra WithConv

section Level

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A]
  {J : Type} (x : J → A →ₐ[O] O)

abbrev fm (a : J) : CartierDual O A := toConv (x a).toLinearMap

theorem sep_two (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g) (s t : A ⊗[O] A)
    (h : ∀ a b, CartierDual.pair O A A (fm x a ⊗ₜ fm x b) s = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) t) :
    s = t := by
  have hr : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      φ (TensorProduct.rid O A (LinearMap.lTensor A ψ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [mul_comm]
  have hl : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      ψ (TensorProduct.lid O A (LinearMap.rTensor A φ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp
  refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
  rw [← hl, ← hl]
  refine congrArg _ (sep _ _ fun b => ?_)
  refine (hl φ (fm x b) s).trans (Eq.trans ?_ (hl φ (fm x b) t).symm)
  rw [← hr, ← hr]
  refine congrArg _ (sep _ _ fun a => ?_)
  exact (hr (fm x a) (fm x b) s).trans ((h a b).trans (hr (fm x a) (fm x b) t).symm)

theorem exists_bialgHom [AddCommGroup J] (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g)
    (h0 : fm x 0 = 1) (hadd : ∀ a b, fm x (a + b) = fm x a * fm x b)
    (l : CartierDual O A →ₗ[O] A) (u : J → A) (hl : ∀ a φ, x a (l φ) = φ (u a))
    (hu0 : ∀ b, x b (u 0) = 1) (hu0' : ∀ a, x 0 (u a) = 1)
    (hua : ∀ a a' b, x b (u (a + a')) = x b (u a) * x b (u a'))
    (hub : ∀ a b b', x (b + b') (u a) = x b (u a) * x b' (u a)) :
    ∃ lam : CartierDual O A →ₐc[O] A, ∀ φ, lam φ = l φ := by
  have hx0 : ∀ f, x 0 f = counit (R := O) f := fun f => congrArg (fun φ : CartierDual O A => φ f) h0
  have hxa : ∀ a b f, x (a + b) f = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) (comul f) := fun a b f =>
    (congrArg (fun φ : CartierDual O A => φ f) (hadd a b)).trans (CartierDual.mul_apply _ _ _)
  have hone : u 0 = 1 := sep _ _ fun b => by rw [hu0, map_one]
  have hmul : ∀ a a', u (a + a') = u a * u a' := fun a a' => sep _ _ fun b => by rw [hua, map_mul]
  have hco : ∀ a, comul (R := O) (u a) = u a ⊗ₜ u a := fun a => sep_two x sep _ _ fun b b' => by
    rw [← hxa, hub, CartierDual.pair_tmul_tmul]; rfl
  let F : CartierDual O A →ₐ[O] A := AlgHom.ofLinearMap l
    (sep _ _ fun a => by rw [hl, map_one, CartierDual.one_apply, ← hx0, hu0'])
    (fun φ ψ => sep _ _ fun a => by
      rw [map_mul (x a), hl, hl, hl, CartierDual.mul_apply, hco, CartierDual.pair_tmul_tmul])
  have hF : ∀ φ, F φ = l φ := fun _ => rfl
  refine ⟨BialgHom.ofAlgHom F (AlgHom.ext fun φ => ?_) (AlgHom.ext fun φ => ?_), fun φ => rfl⟩
  · change counit (R := O) (l φ) = counit (R := O) φ
    rw [← hx0, hl, hone, CartierDual.counit_apply]
  · change Algebra.TensorProduct.map F F (comul (R := O) φ) = comul (R := O) (l φ)
    refine sep_two x sep _ _ fun a b => ?_
    rw [← hxa, hl, hmul, ← CartierDual.pair_comul_tmul]
    generalize comul (R := O) φ = s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul φ ψ =>
      rw [Algebra.TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, ← hl, ← hl]
      rfl

end Level

theorem exists_linear {O A T J : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O (T → O))
    (e : A ≃ₐ[O] S) (q : J → T) (x : J → A →ₐ[O] O) (hx : ∀ a f, x a f = (e f).1 (q a))
    (s : T × T → O) (hs : s ∈ Submodule.span O {g | ∃ a ∈ S, ∃ b ∈ S, g = fun z : T × T => a z.1 * b z.2}) :
    ∃ (l : CartierDual O A →ₗ[O] A) (u : J → A),
      (∀ a φ, x a (l φ) = φ (u a)) ∧ ∀ a b, x b (u a) = s (q a, q b) := by
  induction hs using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, g, hg, rfl⟩ := hg
    refine ⟨(CartierDual.evalAt O A (e.symm ⟨g, hg⟩)).smulRight (e.symm ⟨f, hf⟩),
      fun a => f (q a) • e.symm ⟨g, hg⟩, fun a φ => ?_, fun a b => ?_⟩
    · rw [LinearMap.smulRight_apply, map_smul, map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul,
        mul_comm]
      rfl
    · rw [map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul]
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨l, u, h1, h2⟩ := hs
    obtain ⟨l', u', h1', h2'⟩ := ht
    exact ⟨l + l', u + u', by simp [h1, h1'], by simp [h2, h2']⟩
  | smul c s _ hs =>
    obtain ⟨l, u, h1, h2⟩ := hs
    exact ⟨c • l, c • u, by simp [h1], by simp [h2]⟩

theorem tower_pol : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := exists_linear (X.A n) (e n) (lev p n) (fun a => (τ a).pt n)
      (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end PositivityTheory.HtPt.Twpol
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MhTorusA
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

open scoped CategoryTheory.Obj

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torFst (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra ZU.{0} X)) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

def chi {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) : Multiplicative X →* Γ(Y, ⊤) :=
  (pb (g ≫ torFst S X)).toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)

theorem chi_apply {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi g x = pb (g ≫ torFst S X) (AddMonoidAlgebra.single x.toAdd 1) := rfl

theorem chi_comp {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi (f ≫ g) x = f.appTop (chi g x) := by
  rw [chi_apply, chi_apply, Category.assoc, pb_comp]

theorem chi_ext {Y : Scheme.{0}} {g h : Y ⟶ (splitTorus S X).left}
    (w : g ≫ (splitTorus S X).hom = h ≫ (splitTorus S X).hom) (e : ∀ x, chi g x = chi h x) : g = h := by
  refine pullback.hom_ext (f := (splitTorusAff ZU X).hom) (g := toZ S) ?_ w
  refine pb_ext (j := g ≫ torFst S X) (j' := h ≫ torFst S X) (RingHom.congr_fun ?_)
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun m => e (Multiplicative.ofAdd m)
  have e1 : ∀ k : Y ⟶ (splitTorus S X).left, pb (k ≫ torFst S X) (AddMonoidAlgebra.single 0 r) = pb (toZ Y) r := by
    intro k
    refine (pb_spec (k ≫ torFst S X) (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)) r).symm.trans ?_
    congr 2
    exact specULiftZIsTerminal.hom_ext _ _
  rw [e1, e1]

theorem exists_chi (Y : Over S) (c : Multiplicative X →* Γ(Y.left, ⊤)) :
    ∃ g : Y ⟶ splitTorus S X, ∀ x, chi g.left x = c x := by
  obtain ⟨j, hj⟩ := exists_pb (AddMonoidAlgebra.liftNCRingHom (k := ZU.{0}) (pb (toZ Y.left)) c
    fun _ _ => Commute.all _ _)
  refine ⟨Over.homMk (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), fun x => ?_⟩
  have e : (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) ≫ torFst S X = j := pullback.lift_fst _ _ _
  refine (congrArg (fun k => pb k (AddMonoidAlgebra.single x.toAdd 1)) e).trans ?_
  rw [hj, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
  rfl

theorem pb_mul_aff {Y : Over (Spec ZU.{0})} (g h : Y ⟶ splitTorusAff ZU X) (x : X) :
    pb (A := AddMonoidAlgebra ZU.{0} X) (g * h).left (AddMonoidAlgebra.single x 1) =
      pb (A := AddMonoidAlgebra ZU.{0} X) g.left (AddMonoidAlgebra.single x 1) *
        pb (A := AddMonoidAlgebra ZU.{0} X) h.left (AddMonoidAlgebra.single x 1) := by
  let A := AddMonoidAlgebra ZU.{0} X
  let q : Y.left ⟶ Spec (CommRingCat.of (A ⊗[ZU.{0}] A)) := (lift g h).left ≫ (pullbackSpecIso ZU.{0} A A).hom
  have e0 : (g * h).left = q ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A : A →+* A ⊗[ZU.{0}] A)) := rfl
  have e1 : q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = g.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A)).trans
      (congrArg (·.left) (lift_fst g h)))
  have e2 : q ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) = h.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A)).trans
      (congrArg (·.left) (lift_snd g h)))
  rw [e0, ← e1, ← e2, pb_spec, pb_spec, pb_spec, ← map_mul]
  congr 1
  simp [A, AddMonoidAlgebra.comul_single]

theorem chi_mul {Y : Over S} (g h : Y ⟶ splitTorus S X) (x : Multiplicative X) :
    chi (g * h).left x = chi g.left x * chi h.left x := by
  let g' := ofPull (toZ S) (splitTorusAff ZU X) g
  let h' := ofPull (toZ S) (splitTorusAff ZU X) h
  have e : g * h = toPull (toZ S) (splitTorusAff ZU X) (g' * h') :=
    ((map_mul (toPullHom (toZ S) (splitTorusAff ZU X) Y) g' h').trans
      (congrArg₂ (· * ·) (toPull_ofPull _ _ g) (toPull_ofPull _ _ h))).symm
  have e' : (g * h).left ≫ torFst S X = (g' * h').left := by
    rw [e]
    exact toPull_fst _ _ _
  rw [chi_apply, e']
  exact pb_mul_aff g' h' x.toAdd

theorem chi_one (Y : Over S) (x : Multiplicative X) : chi (1 : Y ⟶ splitTorus S X).left x = 1 := by
  have h := chi_mul (1 : Y ⟶ splitTorus S X) 1 x
  rw [_root_.mul_one] at h
  have hu : IsUnit (chi (1 : Y ⟶ splitTorus S X).left x) := (Group.isUnit x).map _
  exact (hu.mul_eq_left.1 h.symm)

theorem chi_pow {Y : Over S} (g : Y ⟶ splitTorus S X) (x : Multiplicative X) (n : ℕ) :
    chi (g ^ n).left x = chi g.left x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pow_eq_one_iff_chi {Y : Over S} (g : Y ⟶ splitTorus S X) (n : ℕ) :
    g ^ n = 1 ↔ ∀ x, chi g.left x ^ n = 1 := by
  refine ⟨fun h x => by rw [← chi_pow, h, chi_one], fun h => Over.OverMorphism.ext (chi_ext ?_ fun x => ?_)⟩
  · exact (Over.w _).trans (Over.w _).symm
  · rw [chi_pow, h, chi_one]

end PositivityTheory.HtPt.Mh
end
end
