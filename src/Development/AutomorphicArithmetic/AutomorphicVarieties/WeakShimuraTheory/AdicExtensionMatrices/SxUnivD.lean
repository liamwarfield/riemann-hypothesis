module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivRep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivKill
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

private theorem le_ker [IsTopologicalGroup Γ] {G : Type} [Monoid G] (φ : Γ →* G) (h : IsLocallyConstant φ)
    (N : Set Γ) (hN : ∀ g ∈ N, φ g = 1) : (Subgroup.normalClosure N).topologicalClosure ≤ φ.ker := by
  have hc : IsClosed (φ.ker : Set Γ) := by
    have : (φ.ker : Set Γ) = {g | φ g = 1} := rfl
    rw [this]
    exact (h.isClopen_fiber 1).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

private theorem lc_quot {Y : Type} (M : Subgroup Γ) (f : Γ ⧸ M → Y)
    (h : IsLocallyConstant fun g : Γ => f (QuotientGroup.mk g)) : IsLocallyConstant f := fun s =>
  (QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)

private theorem phi_quot (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → M ≤ H →
      Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ M → φ g = 1}) :
    PhiCond (Γ := Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc) fun g hg => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact H.one_mem
  let π := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective π :=
    (QuotientGroup.mk' M).subgroupComap_surjective_of_surjective H (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
      IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M))) ∧
        ∀ g : H.comap (QuotientGroup.mk' M), (g : Γ) ∈ M → φ g = 1})
    (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ, fun g hg => ?_⟩) fun φ φ' e => ?_
  · have : π g = 1 := Subtype.ext ((QuotientGroup.eq_one_iff (g : Γ)).2 hg)
    rw [MonoidHom.comp_apply, this, map_one]
  · exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
  {rbar : Γ →* Matrix ι ι (ResidueField Λ)}

private theorem kills_closure [IsTopologicalGroup Γ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    (s : Lift Λ rbar R) (N : Set Γ) (hN : ∀ g ∈ N, s.hom g = 1) :
    (Subgroup.normalClosure N).topologicalClosure ≤ s.hom.ker := by
  have key : ∀ x y : R, (∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) x = Ideal.Quotient.mk _ y) → x = y := by
    intro x y hxy
    have hH : IsHausdorff (maximalIdeal R) R := (IsCO.complete (O := Λ)).toIsHausdorff
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 (hxy n)
  have hc : IsClosed (s.hom.ker : Set Γ) := by
    have : (s.hom.ker : Set Γ) = ⋂ a, ⋂ b, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (maximalIdeal R ^ n) (s.hom g a b) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) ((1 : Matrix ι ι R) a b)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hg a b n
        rw [hg]
      · intro hg
        ext a b
        exact key _ _ (hg a b)
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun n =>
      ((s.cont a b n).isClopen_fiber _).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

end

theorem UpperTheory.V.Ws.sxUnivKill :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField Λ)) (N : Set Γ), (∀ H : Subgroup Γ, IsOpen (H : Set Γ) → Subgroup.normalClosure N ≤ H → Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ (Subgroup.normalClosure N).topologicalClosure → φ g = 1}) → IsLocallyConstant rbar → (∀ n ∈ N, rbar n = 1) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ rbar R), Represents (killCond rbar N) r := by
  intro l _ Λ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ _ rbar N hfin hloc hN
  haveI : (Subgroup.normalClosure N).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hKc : IsClosed ((Subgroup.normalClosure N).topologicalClosure : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  haveI : TotallyDisconnectedSpace (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) :=
    (UpperTheory.V.AlgebraTools.totallyDisconnected_quot Γ _ hKc).1
  have hK : (Subgroup.normalClosure N).topologicalClosure ≤ rbar.ker := le_ker rbar hloc N hN
  let rq : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure →* Matrix ι ι (ResidueField Λ) :=
    QuotientGroup.lift _ rbar hK
  have hlq : IsLocallyConstant rq := lc_quot _ rq hloc
  have hΦ : PhiCond (Γ := Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) l :=
    phi_quot l _ fun H hH hKH => hfin H hH (le_trans (Subgroup.le_topologicalClosure _) hKH)
  obtain ⟨R, _, _, _, r0, hr0⟩ := univ_lift l Λ (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) ι rq hΦ hlq
  let r : Lift Λ rbar R :=
    ⟨r0.hom.comp (QuotientGroup.mk' _), fun a b n => (r0.cont a b n).comp_continuous continuous_quot_mk,
      fun g a b => r0.red (g : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, r, ?_⟩
  intro R' _ _ _
  constructor
  · intro f n hn
    have h1 : ((n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure)) = 1 :=
      (QuotientGroup.eq_one_iff n).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hn))
    ext a b
    rw [Lift.map_hom]
    show f (r0.hom (n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) = _
    rw [h1, map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro r' hr'
    have hK' : (Subgroup.normalClosure N).topologicalClosure ≤ r'.hom.ker := kills_closure r' N hr'
    let rq' : Lift Λ rq R' :=
      ⟨QuotientGroup.lift _ r'.hom hK', fun a b n => lc_quot _ _ (r'.cont a b n), fun q a b => by
        induction q using QuotientGroup.induction_on with
        | H g => exact r'.red g a b⟩
    obtain ⟨f, hf, huniq⟩ := (hr0 R').2 rq' trivial
    have key : ∀ g : R →ₐ[Λ] R', Lift.map g r = r' ↔ Lift.map g r0 = rq' := by
      intro g
      constructor
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          ext a b
          have := congrArg (fun y : Lift Λ rbar R' => y.hom x a b) h
          exact (Lift.map_hom g r0 _ a b).trans ((Lift.map_hom g r x a b).symm.trans this)
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun x => ?_
        ext a b
        have := congrArg (fun y : Lift Λ rq R' => y.hom (x : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) h
        exact (Lift.map_hom g r x a b).trans ((Lift.map_hom g r0 _ a b).symm.trans this)
    exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gsp_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ν : R) (X : M4 R) :
    IsGSp (f ν) (X.map f) ↔ ∀ i j, f ((adj X * X - ν • (1 : M4 R)) i j) = 0 := by
  unfold IsGSp
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h1 : (adj (X.map f) * X.map f) i j = f ((adj X * X) i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, adj_apply, Matrix.map_apply, map_sum, map_mul, map_zsmul]
  have h2 : (f ν • (1 : M4 R')) i j = f ((ν • (1 : M4 R)) i j) := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
    split_ifs <;> simp
  rw [h1, h2, Matrix.sub_apply, map_sub, sub_eq_zero]

private theorem one_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) :
    X.map f = 1 ↔ ∀ i j, f ((X - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h2 : (1 : M4 R') i j = f ((1 : M4 R) i j) := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [h2, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]

private theorem gsp_diag {R : Type} [CommRing R] (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) :
    IsGSp ν (Matrix.diagonal d) := by
  have e : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]
  unfold IsGSp
  rw [e, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_comm, h, mul_one]
  · simp

private theorem rep_closed {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ) (rbar : Γ →* M4 (ResidueField Λ)) :
    Cond.IsClosed (rbar := rbar) fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom := by
  intro R _ _ _ r
  let S : Set R := {x | (∃ g i j, (adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j = x) ∨
    (∃ g ∈ Φ.N, ∃ i j, (r.hom g - 1) i j = x) ∨ ∃ i j, i ≠ j ∧ r.hom Φ.g0 i j = x}
  refine ⟨Ideal.span S, fun R' _ _ _ f => ?_⟩
  have hs : (∀ x ∈ Ideal.span S, f x = 0) ↔ ∀ x ∈ S, f x = 0 :=
    ⟨fun h x hx => h x (Ideal.subset_span hx), fun h _ hx =>
      (Ideal.span_le (I := RingHom.ker f)).2 (fun y hy => h y hy) hx⟩
  have e1 : ∀ g, IsGSp (((algebraMap Λ R').comp a) (Φ.ν g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j) = 0 := fun g => by
    have := gsp_map_iff (f : R →+* R') (algebraMap Λ R (a (Φ.ν g))) (r.hom g)
    rw [RingHom.comp_apply, ← f.commutes]
    exact this
  have e2 : ∀ g, (r.map f).hom g = 1 ↔ ∀ i j, f ((r.hom g - 1) i j) = 0 := fun g =>
    one_map_iff (f : R →+* R') (r.hom g)
  rw [hs]
  constructor
  · rintro H x (⟨g, i, j, rfl⟩ | ⟨g, hg, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact (e1 g).1 (H.mult g) i j
    · exact (e2 g).1 (H.kill g hg) i j
    · exact H.nrm hij
  · intro H
    exact ⟨fun g => (e1 g).2 fun i j => H _ (Or.inl ⟨g, i, j, rfl⟩),
      fun g hg => (e2 g).2 fun i j => H _ (Or.inr (Or.inl ⟨g, hg, i, j, rfl⟩)),
      fun i j hij => H _ (Or.inr (Or.inr ⟨i, j, hij, rfl⟩))⟩

theorem UpperTheory.V.Ws.sxUnivRep :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R), Represents (fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom) r := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a h
  haveI := h.char
  have hd : ∀ g, (Φ.splitRD ((residue Λ).comp a)).r g =
      Matrix.diagonal fun i => ((residue Λ).comp a) (Φ.χ i g) := fun g => by
    show (Matrix.diagonal fun i => (Φ.χ i g : O)).map ((residue Λ).comp a) = _
    exact Matrix.diagonal_map (map_zero _)
  have hlc : IsLocallyConstant (Φ.splitRD ((residue Λ).comp a)).r := by
    have h4 : IsLocallyConstant fun g => fun i => ((residue Λ).comp a) (Φ.χ i g) := by
      have := (((h.ok.lc 0).prodMk (h.ok.lc 1)).prodMk ((h.ok.lc 2).prodMk (h.ok.lc 3))).comp
        fun x => ![x.1.1, x.1.2, x.2.1, x.2.2]
      convert this using 1
      funext g i
      fin_cases i <;> rfl
    have := h4.comp Matrix.diagonal
    convert this using 1
    funext g
    exact hd g
  have hk : ∀ n ∈ Φ.N, (Φ.splitRD ((residue Λ).comp a)).r n = 1 := fun n hn => by
    rw [hd]
    simp only [h.ok.kill n hn, Matrix.diagonal_one]
  obtain ⟨R, _, _, _, r, hr⟩ := sxUnivKill l (Φ.splitRD ((residue Λ).comp a)).r Φ.N h.phi hlc hk
  haveI := (co_res Λ).1
  let r₁ : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r (ResidueField Λ) :=
    { hom := (Φ.splitRD ((residue Λ).comp a)).r
      cont := fun i j N => hlc.comp fun X => Ideal.Quotient.mk _ (X i j)
      red := fun g i j => by
        obtain ⟨x, hx⟩ := residue_surjective ((Φ.splitRD ((residue Λ).comp a)).r g i j)
        rw [← hx]
        exact (res Λ (ResidueField Λ)).commutes x }
  have h1 : Φ.IsRep ((algebraMap Λ (ResidueField Λ)).comp a) r₁.hom := by
    refine ⟨fun g => ?_, hk, ?_⟩
    · show IsGSp (((residue Λ).comp a) (Φ.ν g)) ((Φ.splitRD ((residue Λ).comp a)).r g)
      rw [hd]
      refine gsp_diag _ _ fun i => ?_
      rw [← map_mul, ← Units.val_mul, h.ok.mul]
    · show ((Φ.splitRD ((residue Λ).comp a)).r Φ.g0).IsDiag
      rw [hd]
      exact Matrix.isDiag_diagonal _
  obtain ⟨R', _, _, _, p, -, hp⟩ := univ_cond Λ Γ (Fin 4) _ R r _ _ hr (rep_closed Φ a _)
    ⟨ResidueField Λ, inferInstance, inferInstance, inferInstance, r₁, hk, h1⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((hp C).1 f).2, fun s hs => (hp C).2 s ⟨hs.kill, hs⟩⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoprodOpt
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private structure SxCOb (O : Type) [CommRing O] [IsLocalRing O] : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]

attribute [local instance] SxCOb.ring SxCOb.alg SxCOb.co

theorem UpperTheory.V.Ws.sxCoprodOpt :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (T : Type) [Finite T] (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra Λ (B t)] [∀ t, IsCO Λ (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (i : A →ₐ[Λ] R) (j : ∀ t, B t →ₐ[Λ] R), ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (fa : A →ₐ[Λ] R') (f : ∀ t, B t →ₐ[Λ] R'), ∃! g : R →ₐ[Λ] R', g.comp i = fa ∧ ∀ t, g.comp (j t) = f t := by
  intro Λ _ _ _ _ T _ A _ _ _ B _ _ _
  let F : Option T → Type := fun o => Option.elim o A B
  letI iR : ∀ o, CommRing (F o) := fun o =>
    match o with
    | none => (inferInstance : CommRing A)
    | some t => (inferInstance : CommRing (B t))
  letI iA : ∀ o, Algebra Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : Algebra Λ A)
    | some t => (inferInstance : Algebra Λ (B t))
  have iC : ∀ o, IsCO Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : IsCO Λ A)
    | some t => (inferInstance : IsCO Λ (B t))
  obtain ⟨R, iRR, iAl, iCO, j, hj⟩ := UpperTheory.V.CA.co_coprod Λ (Option T) F
  refine ⟨R, iRR, iAl, iCO, (j none : A →ₐ[Λ] R), fun t => (j (some t) : B t →ₐ[Λ] R), ?_⟩
  intro R' _ _ _ fa f
  let h : ∀ o, F o →ₐ[Λ] R' := fun o =>
    match o with
    | none => fa
    | some t => f t
  obtain ⟨g, hg, hu⟩ := hj R' h
  refine ⟨g, ⟨hg none, fun t => hg (some t)⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  apply hu
  intro o
  cases o with
  | none => exact h1
  | some t => exact h2 t
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivChar
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* R) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => ψ g
  map_one' := Matrix.ext fun _ _ => by simp
  map_mul' g h := Matrix.ext fun _ _ => by simp [Matrix.mul_apply]

private def ofMat {G R : Type} [Group G] [CommRing R] (r : G →* Matrix Unit Unit R) : G →* R where
  toFun g := r g () ()
  map_one' := by simp
  map_mul' g h := by simp [Matrix.mul_apply]

theorem UpperTheory.V.Ws.sxUnivChar :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : G →* ResidueField Λ), PhiCond (Γ := G) l → IsLocallyConstant χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (ψ : G →* R), AdicCont (maximalIdeal R) ψ ∧ (∀ s, res Λ R (ψ s) = χ s) ∧ ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (ψ' : G →* R'), AdicCont (maximalIdeal R') ψ' → (∀ s, res Λ R' (ψ' s) = χ s) → ∃! f : R →ₐ[Λ] R', ∀ s, f (ψ s) = ψ' s := by
  intro l _ Λ _ _ _ _ _ _ G _ _ _ _ _ χ hΦ hχ
  have hloc : IsLocallyConstant (toMat χ) :=
    hχ.comp (fun x : ResidueField Λ => (Matrix.of fun _ _ => x : Matrix Unit Unit (ResidueField Λ)))
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l Λ G Unit (toMat χ) hΦ hloc
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat r.hom, r.cont () (), fun s => r.red s () (), ?_⟩
  intro R' _ _ _ ψ' hc hred
  let r' : Lift Λ (toMat χ) R' := ⟨toMat ψ', fun _ _ => hc, fun g _ _ => hred g⟩
  obtain ⟨f, hf, huniq⟩ := (hr R').2 r' trivial
  have key : ∀ g : R →ₐ[Λ] R', (∀ s, g (ofMat r.hom s) = ψ' s) ↔ Lift.map g r = r' := by
    intro g
    constructor
    · intro h
      apply Lift.ext
      ext s a b
      cases a
      cases b
      exact (Lift.map_hom g r s () ()).trans (h s)
    · intro h s
      have := congrArg (fun x : Lift Λ (toMat χ) R' => x.hom s () ()) h
      exact (Lift.map_hom g r s () ()).symm.trans this
  exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxUnivD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (D : RD Φ R), Φ.RUniv a D := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS
  haveI := Φ.fin
  haveI := hS.char
  obtain ⟨A, _, _, _, r, hr⟩ := UpperTheory.V.Ws.sxUnivRep l hS
  have hC : ∀ t : Φ.ι × Fin 4, ∃ (B : Type) (_ : CommRing B) (_ : Algebra Λ B) (_ : IsCO Λ B)
      (ψ : Φ.Gv t.1 →* B), AdicCont (maximalIdeal B) ψ ∧
        (∀ s : Φ.Gv t.1, res Λ B (ψ s) = residue Λ (a ((Φ.χ t.2) s))) ∧
        ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (ψ' : Φ.Gv t.1 →* R'),
          AdicCont (maximalIdeal R') ψ' →
            (∀ s : Φ.Gv t.1, res Λ R' (ψ' s) = residue Λ (a ((Φ.χ t.2) s))) →
              ∃! f : B →ₐ[Λ] R', ∀ s, f (ψ s) = ψ' s := by
    intro t
    haveI : CompactSpace (Φ.Gv t.1) := isCompact_iff_compactSpace.mp (hS.closed t.1).isCompact
    let χ : Φ.Gv t.1 →* ResidueField Λ :=
      ((residue Λ).comp a).toMonoidHom.comp ((Units.coeHom O).comp ((Φ.χ t.2).comp (Φ.Gv t.1).subtype))
    have hlc : IsLocallyConstant χ :=
      (hS.ok.lc t.2).comp_continuous continuous_subtype_val
    obtain ⟨B, i1, i2, i3, ψ, h1, h2, h3⟩ := UpperTheory.V.Ws.sxUnivChar l χ (hS.phiv t.1) hlc
    exact ⟨B, i1, i2, i3, ψ, h1, h2, fun R' _ _ _ ψ' h h' => h3 R' ψ' h h'⟩
  choose B iB1 iB2 iB3 ψ hψ1 hψ2 hψ3 using hC
  obtain ⟨R, _, _, _, ι0, j, hU⟩ := @UpperTheory.V.Ws.sxCoprodOpt Λ _ _ _ _ (Φ.ι × Fin 4) _ A _ _ _ B iB1 iB2 iB3
  have hmax : ∀ t (x : B t), x ∈ maximalIdeal (B t) ↔ j t x ∈ maximalIdeal R := by
    intro t x
    rw [← res_eq_zero_iff Λ, ← res_eq_zero_iff Λ, res_map]
  let D : RD Φ R :=
    { r := (Lift.map ι0 r).hom
      ψ := fun v k => (j (v, k) : B (v, k) →+* R).toMonoidHom.comp (ψ (v, k)) }
  refine ⟨R, inferInstance, inferInstance, inferInstance, D, ?_, ?_⟩
  · refine ⟨(hr R).1 ι0, fun i k => (Lift.map ι0 r).cont i k, fun v k => ?_, fun g k => ?_,
      fun g i k hik _ => ?_, fun v k s => ?_⟩
    · exact UpperTheory.V.Ws.adicCont_map (j (v, k) : B (v, k) →+* R) (J := maximalIdeal R)
        (fun x hx => Ideal.mem_comap.mpr ((hmax _ x).mp hx)) (hψ1 (v, k))
    · have := (Lift.map ι0 r).red g k k
      simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep] at this
      exact this
    · apply (res_eq_zero_iff Λ R _).mp
      have := (Lift.map ι0 r).red g i k
      simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply_ne _ hik] at this
      exact this
    · show res Λ R (j (v, k) (ψ (v, k) s)) = _
      rw [res_map]
      exact hψ2 (v, k) s
  · intro R' _ _ _ D' hD'
    have hred : ∀ g i k, res Λ R' (D'.r g i k) = (Φ.splitRD ((residue Λ).comp a)).r g i k := by
      intro g i k
      by_cases hik : i = k
      · subst hik
        simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep]
        exact hD'.diag g i
      · simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply_ne _ hik]
        exact (res_eq_zero_iff Λ R' _).mpr (hD'.off g i k hik (by simp))
    let r' : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R' := ⟨D'.r, hD'.cont, hred⟩
    obtain ⟨fa, hfa, hfau⟩ := (hr R').2 r' hD'.rep
    have hft : ∀ t, ∃! f : B t →ₐ[Λ] R', ∀ s, f (ψ t s) = D'.ψ t.1 t.2 s :=
      fun t => hψ3 t R' (D'.ψ t.1 t.2) (hD'.contψ t.1 t.2) (hD'.redψ t.1 t.2)
    choose f hf hfu using hft
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hU R' fa f
    refine ⟨g, ?_, ?_⟩
    · apply RD.ext
      · have h1 := congrArg Lift.hom hfa
        rw [← hg1] at h1
        ext x i k
        have h2 := congrArg (fun F => F x i k) h1
        simpa [RD.map, Lift.map, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, D, r'] using h2
      · funext v k
        ext s
        show g (j (v, k) (ψ (v, k) s)) = D'.ψ v k s
        rw [← AlgHom.comp_apply, hg2 (v, k), hf]
    · intro f' hf'
      apply hgu
      refine ⟨?_, fun t => ?_⟩
      · apply hfau
        apply Lift.ext
        ext x i k
        have h2 := congrArg (fun E => E.r x i k) hf'
        simpa [RD.map, Lift.map, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, D, r'] using h2
      · apply hfu t
        intro s
        have h2 := congrArg (fun E => E.ψ t.1 t.2 s) hf'
        simpa [RD.map, D] using h2
