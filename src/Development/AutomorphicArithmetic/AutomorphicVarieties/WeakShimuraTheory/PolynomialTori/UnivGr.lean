module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Descend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

theorem UpperTheory.V.Ws.Po.univOf :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ P : Cond c.O D.rbar, P.IsClosed →
      (∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), P R ρ → D.UnrT ρ.hom 1) →
      (∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R), P R ρ) →
      ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O D.rbar U), Represents P ρ := by
  intro hP Ω _ _ _ l hl c D hD P hc hu ⟨R₁, _, _, _, ρ₁, h₁⟩
  obtain ⟨rb, r0, hb, -, -, -, H⟩ := descend D hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := facts D hD
  obtain ⟨_, _⟩ := UpperTheory.V.Ws.Po.fin_res c
  haveI : IsGalois ℚ Ω := {}
  haveI hcl := isClosed_NS Ω D.SP
  haveI : CompactSpace D.Gam := inferInstance
  haveI : T2Space D.Gam := inferInstance
  haveI : TotallyDisconnectedSpace D.Gam := totDisc_quot _ hcl
  have hq : Topology.IsQuotientMap (toGS Ω D.SP) := QuotientGroup.isQuotientMap_mk _
  have hlc : IsLocallyConstant D.rbar := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have : D.rbar (g⁻¹ * x) = 1 := hx
    rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]
  have hlb : IsLocallyConstant rb := fun s => by
    rw [← hq.isOpen_preimage]
    have := hlc s
    rw [← hb] at this
    exact this
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l c.O D.Gam (Fin 4) rb (phiGam D hD hP) hlb
  obtain ⟨ρ, hρ, -⟩ := (H R).1 r
  let P₀ : Cond c.O D.rbar := fun C _ _ _ s => ∃ t : Lift c.O rb C, s.hom = t.hom.comp (toGS Ω D.SP)
  have hmap : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : R →ₐ[c.O] C),
      (ρ.map f).hom = (r.map f).hom.comp (toGS Ω D.SP) := fun C _ _ _ f => by
    ext g a b
    show f (ρ.hom g a b) = f (r.hom _ a b)
    rw [hρ]
    rfl
  have h0 : Represents P₀ ρ := fun C _ _ _ => by
    refine ⟨fun f => ⟨r.map f, hmap C f⟩, fun s ⟨t, ht⟩ => ?_⟩
    obtain ⟨f, hf, huq⟩ := (hr C).2 t trivial
    refine ⟨f, Lift.ext (by rw [hmap, hf, ht]), fun f' hf' => huq f' (Lift.ext ?_)⟩
    refine (MonoidHom.cancel_right hq.surjective).1 ?_
    rw [← hmap, ← ht]
    exact congrArg Lift.hom hf'
  have hPP : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (s : Lift c.O D.rbar C), P C s → P₀ C s :=
    fun C _ _ _ s h => (H C).2 s (hu C s h)
  obtain ⟨R', _, _, _, p, -, h⟩ := univ_cond c.O (G ℚ Ω) (Fin 4) D.rbar R ρ P₀ P h0 hc
    ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hPP _ _ h₁, h₁⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ.map p, fun C _ _ _ =>
    ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨hPP _ _ h', h'⟩⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtClosed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompClosed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) :
    Lift.map (AlgHom.id O R) r = r := by
  apply Lift.ext
  ext g a b
  simp [Lift.map]

private theorem lift_map_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S T : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    [CommRing T] [Algebra O T] [IsCO O T] (f : R →ₐ[O] S) (g : S →ₐ[O] T) (r : Lift O rbar R) :
    Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  simp [Lift.map]

private theorem cond_map_of_isClosed {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (P : Cond O rbar) (hP : P.IsClosed)
    {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    (r : Lift O rbar R) (hr : P R r) (f : R →ₐ[O] S) : P S (Lift.map f r) := by
  obtain ⟨I, hI⟩ := hP R r
  have h0 := (hI R (AlgHom.id O R)).1 (by rw [lift_map_id]; exact hr)
  refine (hI S f).2 fun x hx => ?_
  have := h0 x hx
  simp only [AlgHom.id_apply] at this
  rw [this, map_zero]

theorem UpperTheory.V.Ws.Po.onCompClosed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι]
      (rbar : Γ →* Matrix ι ι (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* Matrix ι ι O), P.IsClosed →
      ∀ (U : Type) [CommRing U] [Algebra O U] [IsCO O U] (ρ : Lift O rbar U), Represents P ρ → ∀ J : Ideal U,
      (∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : U →ₐ[O] C), OnComp P ρ₀ (ρ.map f) ↔ J ≤ RingHom.ker f) →
      Cond.IsClosed (rbar := rbar) fun _ _ _ _ r => OnComp P ρ₀ r := by
  intro O _ _ Γ ι _ _ _ _ rbar P ρ₀ hP U _ _ _ ρ hρ J hJ
  intro R _ _ _ r
  have onP : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (s : Lift O rbar S),
      OnComp P ρ₀ s → P S s := by
    intro S _ _ _ s hs
    obtain ⟨B, _, _, _, _, ρ', hP', -, y, hy⟩ := hs
    subst hy
    exact cond_map_of_isClosed P hP ρ' hP' y
  obtain ⟨I0, hI0⟩ := hP R r
  by_cases htop : I0 = ⊤
  · refine ⟨⊤, fun R' _ _ _ f => ⟨fun h x _ => ?_, fun h => ?_⟩⟩
    · exact (hI0 R' f).1 (onP _ _ h) x (by rw [htop]; exact Submodule.mem_top)
    · exfalso
      have h1 := h 1 Submodule.mem_top
      rw [map_one] at h1
      exact one_ne_zero h1
  · haveI : Nontrivial (R ⧸ I0) := Ideal.Quotient.nontrivial_iff.2 htop
    haveI : IsCO O (R ⧸ I0) :=
      co_quot O R (R ⧸ I0) (Ideal.Quotient.mkₐ O I0) (Ideal.Quotient.mkₐ_surjective O I0)
    have hPπ : P (R ⧸ I0) (Lift.map (Ideal.Quotient.mkₐ O I0) r) :=
      (hI0 _ (Ideal.Quotient.mkₐ O I0)).2 fun x hx => by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    obtain ⟨u, hu, -⟩ := (hρ (R ⧸ I0)).2 _ hPπ
    refine ⟨I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), fun R' _ _ _ f => ?_⟩
    have key : ∀ hf : ∀ a ∈ I0, f a = 0, (OnComp P ρ₀ (Lift.map f r) ↔
        ∀ x ∈ I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), f x = 0) := by
      intro hf
      set g := Ideal.Quotient.liftₐ I0 f hf with hg
      have hgπ : ∀ x, g (Ideal.Quotient.mkₐ O I0 x) = f x := fun x => rfl
      have hfg : f = g.comp (Ideal.Quotient.mkₐ O I0) := by
        ext x
        exact (hgπ x).symm
      have hmap : Lift.map f r = Lift.map (g.comp u) ρ := by
        rw [hfg, ← lift_map_map, ← hu, lift_map_map]
      rw [hmap, hJ]
      constructor
      · intro hJk x hx
        have hle : J.map u ≤ RingHom.ker g := by
          rw [Ideal.map_le_iff_le_comap]
          intro z hz
          exact hJk hz
        have hsup : I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0) ≤ RingHom.ker f := by
          refine sup_le (fun a ha => RingHom.mem_ker.2 (hf a ha)) ?_
          intro y hy
          have hy' : Ideal.Quotient.mkₐ O I0 y ∈ J.map u := hy
          have := hle hy'
          rw [RingHom.mem_ker, hgπ] at this
          exact RingHom.mem_ker.2 this
        exact RingHom.mem_ker.1 (hsup hx)
      · intro h y hy
        obtain ⟨x, hx⟩ := Ideal.Quotient.mkₐ_surjective O I0 (u y)
        have hxm : x ∈ (J.map u).comap (Ideal.Quotient.mkₐ O I0) := by
          show Ideal.Quotient.mkₐ O I0 x ∈ J.map u
          rw [hx]
          exact Ideal.mem_map_of_mem _ hy
        have := h x (Ideal.mem_sup_right hxm)
        rw [RingHom.mem_ker, AlgHom.comp_apply, ← hx, hgπ]
        exact this
    constructor
    · intro h
      exact (key fun x hx => (hI0 R' f).1 (onP _ _ h) x hx).1 h
    · intro h
      exact (key fun a ha => h a (Ideal.mem_sup_left ha)).2 h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem hEl_map' (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Matrix.add_apply, Matrix.smul_apply]

private theorem mult_iff' (f : R →ₐ[c.O] R') (r : Lift c.O D.rbar R) :
    D.Mult (r.map f).hom ↔ ∀ g i j,
      f ((adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) = 0 := by
  refine forall_congr' fun g => ?_
  rw [← f.commutes]
  exact UpperTheory.V.Ws.Po.gsp_iff (f : R →+* R') _ (r.hom g)

end

theorem UpperTheory.V.Ws.Po.ptClosed :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Cond.IsClosed (rbar := D.rbar) fun _ _ _ _ ρ => D.IsPt ρ := by
  intro hP Ω _ _ _ l _ c D hD
  have hL : Cond.IsClosed (rbar := D.rbarAt l) fun _ _ _ _ r => OnComp D.condL (D.r0At l) r := by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compL D hD hP.loc
    exact onCompClosed _ _ _ _ _ _ (closedL D) U ρ hrep J hJ
  have hQ : ∀ p ∈ D.Sb,
      Cond.IsClosed (rbar := D.rbarAt p) fun _ _ _ _ r => OnComp (D.condP p) (D.r0At p) r := fun p hp => by
    obtain ⟨U, _, _, _, ρ, J, hrep, hJ⟩ := compP D hD hP.loc p hp
    exact onCompClosed _ _ _ _ _ _ (closedP D p) U ρ hrep J hJ
  refine closed_of_set _ fun R _ _ _ r => ?_
  obtain ⟨IL, hIL⟩ := hL R (D.loc r l)
  choose IP hIP using fun p hp => hQ p hp R (D.loc r p)
  refine ⟨{x | (∃ g i j, x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : UpperTheory.V.GradeZeroInterpolatingElement.M4 R)) i j) ∨
    (∃ A : ValuationSubring Ω, Raw.Away D.T A ∧ ∃ g ∈ Ine (F := ℚ) A, D.rbar g = 1 ∧ ∃ i j, x = (r.hom g - 1) i j) ∨
    (∃ i j, lamW i ≠ lamW j ∧ x = r.hom D.ph i j) ∨ x = D.hEl r.hom 0 2 ∨ x = D.hEl r.hom 2 0 ∨
    x ∈ IL ∨ ∃ p, ∃ hp : p ∈ D.Sb, x ∈ IP p hp}, fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨g, i, j, rfl⟩ | ⟨A, hA, g, hg, hg1, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl | rfl | hx | ⟨p, hp, hx⟩ := hx
    · exact (mult_iff' D f r).1 h.mult g i j
    · exact (one_iff (f : R →+* R') (r.hom g)).1 (h.unr A hA g hg hg1) i j
    · exact h.nrm.1 i j hij
    · rw [← hEl_map']; exact h.nrm.2.1
    · rw [← hEl_map']; exact h.nrm.2.2
    · exact (hIL R' f).1 h.atL x hx
    · exact (hIP p hp R' f).1 (h.atP p hp) x hx
  · refine ⟨(mult_iff' D f r).2 fun g i j => h _ (.inl ⟨g, i, j, rfl⟩),
      fun A hA g hg hg1 => (one_iff (f : R →+* R') (r.hom g)).2 fun i j =>
        h _ (.inr (.inl ⟨A, hA, g, hg, hg1, i, j, rfl⟩)),
      ⟨fun i j hij => h _ (.inr (.inr (.inl ⟨i, j, hij, rfl⟩))), ?_, ?_⟩,
      (hIL R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inl hx)))))),
      fun p hp => (hIP p hp R' f).2 fun x hx => h x (.inr (.inr (.inr (.inr (.inr (.inr ⟨p, hp, hx⟩))))))⟩
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inl rfl))))
    · rw [hEl_map']; exact h _ (.inr (.inr (.inr (.inr (.inl rfl)))))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtTorus
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.OnCompTorus
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wv_map {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ) (s : Bˣ × Bˣ)
    (h1 : F t.1 = s.1) (h2 : F t.2 = s.2) (w : ℤ × ℤ) : F (wv t w : Aˣ) = (wv s w : Bˣ) := by
  have e1 : Units.map (F : A →* B) t.1 = s.1 := Units.ext h1
  have e2 : Units.map (F : A →* B) t.2 = s.2 := Units.ext h2
  have : Units.map (F : A →* B) (wv t w) = wv s w := by
    unfold wv
    rw [map_mul, map_zpow, map_zpow, e1, e2]
  exact congrArg Units.val this

private theorem wv_one {A B : Type} [CommRing A] [CommRing B] (F : A →+* B) (t : Aˣ × Aˣ)
    (h1 : F t.1 = 1) (h2 : F t.2 = 1) (w : ℤ × ℤ) : F (wv t w : Aˣ) = 1 := by
  rw [wv_map F t (1, 1) h1 h2]
  simp [wv]

private theorem conj_lift {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {rbar : Γ →* M4 (ResidueField O)} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R)
    (s : Rˣ × Rˣ) (h1 : res O R s.1 = 1) (h2 : res O R s.2 = 1) :
    ∃ r' : Lift O rbar R, ∀ g, r'.hom g = tconj s (r.hom g) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp R
  refine ⟨{ hom := ⟨⟨fun g => tconj s (r.hom g), by rw [map_one, hone]⟩, fun g h => ?_⟩
            cont := fun a b N => ?_
            red := fun g a b => ?_ }, fun _ => rfl⟩
  · show tconj s _ = _
    rw [map_mul, hmul]
  · show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R) * r.hom g a b)
    simp only [map_mul]
    exact (IsLocallyConstant.const _).mul (r.cont a b N)
  · show res _ _ ((wv s (wt a b) : R) * r.hom g a b) = _
    have := wv_one (res O R : R →+* ResidueField O) s h1 h2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [map_mul, this, one_mul, r.red]

theorem UpperTheory.V.Ws.Po.onCompTorus :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      (rbar : Γ →* M4 (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* M4 O),
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (r : Lift O rbar R), P R r → P R' (r.map f)) →
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), (∀ g, r'.hom g = tconj s (r.hom g)) → P R r → P R r') →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : Lift O rbar R) (s : Rˣ × Rˣ), res O R s.1 = 1 → res O R s.2 = 1 →
        (∀ g, r'.hom g = tconj s (r.hom g)) → OnComp P ρ₀ r → OnComp P ρ₀ r' := by
  intro O _ _ _ _ Γ _ _ rbar P ρ₀ hmap htor R _ _ _ r r' s h1 h2 hr ⟨B, _, _, _, _, ρ, hP, ⟨x, hx⟩, y, hy⟩
  haveI : IsCO O (MvPowerSeries (Fin 2) B) := co_mvps O B (Fin 2)
  haveI : IsDomain (MvPowerSeries (Fin 2) B) := NoZeroDivisors.to_isDomain _
  let c : B →ₐ[O] MvPowerSeries (Fin 2) B := IsScalarTower.toAlgHom O B _
  have hu : ∀ i : Fin 2, IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin 2) B) := fun i => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  let t : (MvPowerSeries (Fin 2) B)ˣ × (MvPowerSeries (Fin 2) B)ˣ := ((hu 0).unit, (hu 1).unit)
  have ht1 : (t.1 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 0 := rfl
  have ht2 : (t.2 : MvPowerSeries (Fin 2) B) = 1 + MvPowerSeries.X 1 := rfl
  obtain ⟨x', ⟨xC, xX⟩, -⟩ := co_ev O B O (Fin 2) x (fun _ => 0) fun _ => zero_mem _
  have x1 : x' t.1 = 1 := by rw [ht1, map_add (f := _), map_one, xX, add_zero]
  have x2 : x' t.2 = 1 := by rw [ht2, map_add (f := _), map_one, xX, add_zero]
  obtain ⟨y', ⟨yC, yX⟩, -⟩ := co_ev O B R (Fin 2) y ![(s.1 : R) - 1, (s.2 : R) - 1] fun i => by
    rw [← res_eq_zero_iff O]
    fin_cases i
    · simp [h1]
    · simp [h2]
  have y1 : y' t.1 = s.1 := by rw [ht1, map_add (f := _), map_one, yX]; simp
  have y2 : y' t.2 = s.2 := by rw [ht2, map_add (f := _), map_one, yX]; simp
  obtain ⟨ρ', hρ'⟩ := conj_lift (ρ.map c) t (by rw [← UpperTheory.V.Alg.res_map x' _, x1, map_one]) (by rw [← UpperTheory.V.Alg.res_map x' _, x2, map_one])
  have he : ∀ g a b, ρ'.hom g a b = (wv t (wt a b)).val * MvPowerSeries.C (ρ.hom g a b) :=
    fun g a b => by rw [hρ']; rfl
  refine ⟨MvPowerSeries (Fin 2) B, inferInstance, inferInstance, inferInstance, inferInstance, ρ',
    htor _ _ _ t hρ' (hmap _ _ c ρ hP), ⟨x', fun g a b => ?_⟩, y', ?_⟩
  · have := wv_one (x' : MvPowerSeries (Fin 2) B →+* O) t x1 x2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [he, map_mul, this, one_mul, xC, hx]
  · ext g a b
    have := wv_map (y' : MvPowerSeries (Fin 2) B →+* R) t s y1 y2 (wt a b)
    rw [RingHom.coe_coe] at this
    rw [Lift.map_hom, he, map_mul, this, yC, hr, ← hy]
    rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ptTorus :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (r r' : Lift c.O D.rbar R) (s : Rˣ × Rˣ),
      res c.O R s.1 = 1 → res c.O R s.2 = 1 → (∀ g, r'.hom g = tconj s (r.hom g)) → D.IsPt r → D.IsPt r' := by
  intro Ω _ _ _ l _ c D _ R _ _ _ r r' s h1 h2 hc hP
  have hone : ∀ X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R, X = 1 → UpperTheory.V.GradeZeroInterpolatingElement.tconj s X = 1 := by
    rintro X rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.GradeZeroInterpolatingElement.tconj, UpperTheory.V.GradeZeroInterpolatingElement.wv, UpperTheory.V.GradeZeroInterpolatingElement.wt, Matrix.one_apply]
  have hent : ∀ (X : UpperTheory.V.GradeZeroInterpolatingElement.M4 R) (i j : Fin 4), UpperTheory.V.GradeZeroInterpolatingElement.tconj s X i j = 0 ↔ X i j = 0 := by
    intro X i j
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    constructor
    · intro h
      have := congrArg (fun x => (↑(UpperTheory.V.GradeZeroInterpolatingElement.wv s (UpperTheory.V.GradeZeroInterpolatingElement.wt i j))⁻¹ : R) * x) h
      simpa [← mul_assoc] using this
    · intro h
      simp [h]
  have hEl' : D.hEl r'.hom = UpperTheory.V.GradeZeroInterpolatingElement.tconj s (D.hEl r.hom) := by
    simp only [UpperTheory.V.GradeZeroInterpolatingElement.Raw.hEl, hc]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, UpperTheory.V.GradeZeroInterpolatingElement.tconj, Matrix.of_apply]
    rw [mul_add, mul_smul_comm]
  obtain ⟨hb, h02, h20⟩ := hP.nrm
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g
    rw [hc]
    exact UpperTheory.V.Ws.Po.gsp_conj s (hP.mult g)
  · intro A hA g hg hb'
    rw [hc]
    exact hone _ (hP.unr A hA g hg hb')
  · intro i j hij
    rw [hc, hent]
    exact hb i j hij
  · rw [hEl', hent]
    exact h02
  · rw [hEl', hent]
    exact h20
  · exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt l) D.condL (D.r0At l)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condL_map D f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusL D ρ ρ' t h hq)
      R (D.loc r l) (D.loc r' l) s h1 h2 (fun g => hc g) hP.atL
  · intro p hp
    exact UpperTheory.V.Ws.Po.onCompTorus c.O _ (D.rbarAt p) (D.condP p) (D.r0At p)
      (fun R _ _ _ R' _ _ _ f ρ h => UpperTheory.V.GradeZeroInterpolatingElement.Ex.condP_map D p f ρ h)
      (fun R _ _ _ ρ ρ' t h hq => UpperTheory.V.Ws.Po.torusP D p ρ ρ' t h hq)
      R (D.loc r p) (D.loc r' p) s h1 h2 (fun g => hc g) (hP.atP p hp)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem prod_part {O U H : Type} [CommRing O] [CommRing U] [Algebra O U] [Group H] (W : WPres O (ℤ × ℤ) U)
    (r : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 U) (h : ∀ g a b, r g a b ∈ W.part (wt a b)) (L : List (H × Fin 4 × Fin 4)) :
    (L.map fun a => r a.1 a.2.1 a.2.2).prod ∈ W.part (L.map fun a => wt a.2.1 a.2.2).sum := by
  induction L with
  | nil => exact (SetLike.GradedOne.one_mem : (1 : U) ∈ W.part 0)
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact SetLike.GradedMul.mul_mem (h _ _ _) ih

private theorem fin_adjoin {O U R H : Type} [CommRing O] [IsNoetherianRing O] [CommRing U] [Algebra O U] [CommRing R]
    [Algebra O R] [Group H] (W : WPres O (ℤ × ℤ) U) (r : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 U) (h : ∀ g a b, r g a b ∈ W.part (wt a b))
    (f : U →ₐ[O] R) (r' : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 R) (hr : ∀ g a b, r' g a b = f (r g a b)) [Module.Finite O (W.gr 0)] :
    Module.Finite O (Algebra.adjoin O (mono r' 0)) := by
  let φ : W.gr 0 →ₗ[O] R := f.toLinearMap ∘ₗ W.A.val.toLinearMap ∘ₗ (W.gr 0).subtype
  have key : ∀ x ∈ Algebra.adjoin O (mono r' 0), ∃ y ∈ W.part 0, f y = x := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨_, hL ▸ prod_part W r h L, ?_⟩
      rw [map_list_prod, List.map_map]
      simp only [hr]
      rfl
    | algebraMap a =>
      refine ⟨algebraMap O U a, ?_, f.commutes a⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : U) ∈ W.part 0)
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, add_mem ha hb, map_add f a b⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      refine ⟨a * b, ?_, map_mul f a b⟩
      have := (SetLike.GradedMul.mul_mem ha hb : a * b ∈ W.part (0 + 0))
      rwa [add_zero] at this
  have hm : ∀ x : Algebra.adjoin O (mono r' 0), (Algebra.adjoin O (mono r' 0)).val.toLinearMap x ∈ LinearMap.range φ :=
    fun x => by
      obtain ⟨y, hy, e⟩ := key x.1 x.2
      exact ⟨⟨⟨y, W.part_le_A hy⟩, hy⟩, e⟩
  refine Module.Finite.of_injective (LinearMap.codRestrict _ _ hm) fun x y e => ?_
  have e' := congrArg Subtype.val e
  exact Subtype.ext e'

theorem UpperTheory.V.Ws.Po.univGr :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ¬ D.Fin0 →
      ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O D.rbar U) (W : WPres c.O (ℤ × ℤ) U),
        D.IsPt ρ ∧ (∀ s, W.z s ∈ maximalIdeal U) ∧
        (∀ i, ∃ g a b, W.z i = ρ.hom g a b - algebraMap c.O U (D.r0 g a b) ∧ W.wt i = wt a b) ∧
        ¬ @Module.Finite c.O (W.gr 0) inferInstance (Submodule.addCommMonoid (W.gr 0))
          (Submodule.module (W.gr 0)) := by
  intro hP Ω _ _ _ l _ c D hD hF
  have hex : ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R), D.IsPt ρ := by
    by_contra hn
    exact hF fun R _ _ _ ρ h => (hn ⟨R, inferInstance, inferInstance, inferInstance, ρ, h⟩).elim
  obtain ⟨U, _, _, _, ρ, hrep⟩ := univOf hP D hD (fun _ _ _ _ ρ => D.IsPt ρ) (ptClosed hP D hD)
    (fun _ _ _ _ _ h => h.unr) hex
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 (ρ.map f') ((hrep R').1 f')).unique h rfl
  have hst : ρ.TStable w4 := tstable hrep fun R' _ _ _ r r' s h1 h2 h3 h4 => ptTorus D hD R' r r' s h1 h2 h3 h4
  obtain ⟨W, hW, hz⟩ := lift_grading c.O (ℤ × ℤ) (G ℚ Ω) (Fin 4) D.rbar w4 U ρ (fun g a b => D.r0 g a b)
    (fun _ _ _ => rfl) (fun g a b h => Matrix.diagonal_apply_ne _ fun e => h (congrArg w4 e)) hgen hst
  have hid : ρ.map (AlgHom.id c.O U) = ρ := by
    ext g a b
    rfl
  refine ⟨U, inferInstance, inferInstance, inferInstance, ρ, W, hid ▸ (hrep U).1 (AlgHom.id c.O U), fun s => ?_, hz,
    fun hfin => hF fun R _ _ _ r hr => ?_⟩
  · obtain ⟨g, a, b, e, -⟩ := hz s
    rw [e, ← res_eq_zero_iff c.O, map_sub, ρ.red, AlgHom.commutes, sub_eq_zero]
    rfl
  · obtain ⟨f, hf, -⟩ := (hrep R).2 r hr
    exact fin_adjoin W ρ.hom hW f r.hom fun g a b => by rw [← hf]; rfl
