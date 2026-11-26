module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
  {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω} {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)}

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RingEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

private theorem phi_surj {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (π : Γ →* Γ')
    (hc : Continuous π) (hπ : Function.Surjective π) {l : ℕ} (h : PhiCond Γ l) : PhiCond Γ' l := fun H hH => by
  haveI := h (H.comap π) (hH.preimage hc)
  let p : H.comap π →* H := π.subgroupComap H
  have hp : Continuous p := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective p := MonoidHom.subgroupComap_surjective_of_surjective _ _ hπ
  refine Finite.of_injective
    (β := {φ : H.comap π →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set (H.comap π))})
    (fun φ => ⟨φ.1.comp p, φ.2.preimage hp⟩) fun φ φ' e => ?_
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem phi_unr (hGF : GlobalFiniteness) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ContainsAbove S l) (M : Subgroup (G ℚ Ω)) [M.Normal]
    (hM : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ M) : PhiCond (G ℚ Ω ⧸ M) l := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hK : CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) := phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
    exact f1
  rw [pow_one] at key
  refine phi_surj (QuotientGroup.lift _ (QuotientGroup.mk' M) fun g hg => (QuotientGroup.eq_one_iff g).2 (hM hg))
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_quotient_mk') (fun y => ?_) key
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk g, rfl⟩

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_ring :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))) (g₁ : G ℚ Ω), D.Marked g₁ → Nonempty (D.Ring U g₁) := by
  intro hI Ω _ _ _ K _ _ _ l hl c N hN e ψ D U g₁ hg₁
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hc, hf, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hc
  haveI : Finite (ResidueField c.O) := hf
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  obtain ⟨-, -, -, hη, hΨ, hK, -, -, -, hKill, -⟩ := dat_facts D
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨T, hT⟩ := (ramFinite ℚ ℚ K Ω).1
  obtain ⟨-, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω N
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by simpa using ⟨hl.out.ne_zero, hN.out⟩)
  classical
  have hmem : ∀ v, ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ T ∪ hfin.toFinset := fun v hv =>
    Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hv))
  have hval : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ∀ n : ℕ,
      A.valuation (n : Ω) < 1 → ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hv n hn
    have h := hv ((n : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e] at h
    exact h.1 hn
  haveI : (Subgroup.normalClosure D.Kill).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hΦ : PhiCond (G ℚ Ω ⧸ (Subgroup.normalClosure D.Kill).topologicalClosure) l := by
    refine phi_unr hI.gf l (T ∪ hfin.toFinset) (fun v hv => hmem v ?_) _
      (Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono fun g hg => ?_))
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hv
    · simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, A, hA, hg⟩ := hg
      have hv' : ((l * N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hmem v h)
      rw [Nat.cast_mul] at hv'
      refine (hKill g).2 ⟨A, fun h => hv' (v.asIdeal.mul_mem_right _ (hval A v hA l h)), hg, ?_, ?_⟩
      · rw [← MonoidHom.mem_ker, D.η_ker]
        exact hT v (fun h => hv (Finset.mem_union_left _ h)) A hA ⟨by rw [galOf_self]; trivial, hg⟩
      · have h1 : Chr.cls ℚ Ω N g = 1 := hIne A (fun h => hv' (v.asIdeal.mul_mem_left _ (hval A v hA N h))) hg
        simp only [Chr.dirG, MonoidHom.comp_apply, h1, map_one]
  exact (exists_sRing D.ι_cont U (D.loc.It U) D.cc g₁ hg₁ (Loc.locGood hI.loc D.loc U) D.Ψ_cont hK
    (exists_univ l D.η D.Ψ hη hΨ D.Kill (fun g ⟨_, _, _, h⟩ => h) _ rfl hΦ)).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RootOfCharpoly
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem quot_mem {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (a t : H →* M) (g : H) (i j : Fin 3)
    (h1 : a g / t g ^ wt1 i ∈ U) (h2 : a g = t g ^ wt1 j) : t g ^ (wt1 j - wt1 i) ∈ U := by
  rwa [h2, div_eq_mul_inv, ← _root_.zpow_sub] at h1

private theorem eq_away {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (I : Subgroup H) (a t : H →* M)
    (i : Fin 3) (hred : ∀ g, a g / t g ^ wt1 i ∈ U) (hroot : ∀ g ∈ I, ∃ j, a g = t g ^ wt1 j)
    (hI : ∀ g ∈ I, t g ∈ U → t g = 1) (g : H) (hg : g ∈ I) : a g = t g ^ wt1 i := by
  obtain ⟨j, hj⟩ := hroot g hg
  have h := quot_mem U a t g i j (hred g) hj
  rw [← map_zpow] at h
  have h' := hI _ (I.zpow_mem hg _) h
  rw [map_zpow, _root_.zpow_sub, mul_inv_eq_one] at h'
  rw [hj, h']

private theorem eq_of_sq {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (a t : H →* M)
    (i : Fin 3) (g : H) (hred : a g / t g ^ wt1 i ∈ U) (hroot : ∃ j, a g = t g ^ wt1 j)
    (hs : t g ^ 2 ∉ U) : a g = t g ^ wt1 i := by
  obtain ⟨j, hj⟩ := hroot
  by_cases hij : j = i
  · rw [hj, hij]
  exfalso
  have h := quot_mem U a t g i j hred hj
  have hd : (wt1 j - wt1 i) ∣ 2 := by
    revert hij
    fin_cases i <;> fin_cases j <;> simp [wt1]
  obtain ⟨m, hm⟩ := hd
  apply hs
  have := U.zpow_mem h m
  rwa [← _root_.zpow_mul, ← hm, zpow_ofNat] at this

private theorem eq_above {H M : Type} [Group H] [CommGroup M] (U : Subgroup M) (I : Subgroup H) (a t : H →* M)
    (i : Fin 3) (hred : ∀ g, a g / t g ^ wt1 i ∈ U) (hroot : ∀ g ∈ I, ∃ j, a g = t g ^ wt1 j)
    (s : H) (hs : s ∈ I) (hs2 : t s ^ 2 ∉ U) (g : H) (hg : g ∈ I) : a g = t g ^ wt1 i := by
  by_cases h : t g ^ 2 ∈ U
  · have h1 := eq_of_sq U a t i s (hred s) (hroot s hs) hs2
    have h2 := eq_of_sq U a t i (g * s) (hred _) (hroot _ (I.mul_mem hg hs)) (by
      rw [map_mul, mul_pow]
      exact fun h' => hs2 ((U.mul_mem_cancel_left h).1 h'))
    rw [map_mul, map_mul, mul_zpow, h1] at h2
    exact mul_right_cancel h2
  · exact eq_of_sq U a t i g (hred g) (hroot g hg) h

private theorem norm_eq_one_of {F : Type} [NormedField F] [IsUltrametricDist F] {u : F} (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have e : u = (u - 1) + 1 := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

private def U1 (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have e : ((u * v : Fˣ) : F) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖((u * v : Fˣ) : F) - 1‖ < 1
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hu)
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' := by
    intro u hu
    have e : (u : F) * (((u⁻¹ : Fˣ) : F) - 1) = -((u : F) - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at h
    show ‖((u⁻¹ : Fˣ) : F) - 1‖ < 1
    rw [h]
    exact hu

private theorem root_of_charpoly {F : Type} [Field F] (a b : Fin 3 → F)
    (h : (Matrix.diagonal a).charpoly = (Matrix.diagonal b).charpoly) (i : Fin 3) : ∃ j, a i = b j := by
  have h1 := congrArg (Polynomial.eval (a i)) h
  rw [Matrix.charpoly_diagonal, Matrix.charpoly_diagonal, Polynomial.eval_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp), eq_comm, Finset.prod_eq_zero_iff] at h1
  obtain ⟨j, -, hj⟩ := h1
  exact ⟨j, by simpa [sub_eq_zero] using hj⟩

private theorem exists_diag {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ)
    (r : Γ →* GG (m := 3) (R := R)) (hm : HasMult η r)
    (hU : Upper η r) (hL : Lower η r) :
    ∃ a : Fin 3 → η.ker →* Rˣ, ∀ g : η.ker, (r g).mat = Matrix.diagonal fun i => (a i g : R) := by
  have hd : ∀ g : η.ker, (r g).mat = Matrix.diagonal fun i => (r g).mat i i := by
    intro g
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_trichotomy (wt i j) 0 with h | h | h
    · exact hU g g.2 i j h
    · exact absurd (Fin.ext (by simp only [wt, wt1] at h; omega)) hij
    · exact hL g g.2 i j h
  let b : Fin 3 → η.ker →* R := fun i =>
    { toFun := fun g => (r g).mat i i
      map_one' := by simp [GG.mat]
      map_mul' := fun g h => by
        have e : (r ((g * h : η.ker) : Γ)).mat = (r g).mat * (r h).mat :=
          congrArg Units.val (map_mul (glPart η r hm) g h)
        rw [e, hd g, Matrix.diagonal_mul, Matrix.diagonal_apply_eq] }
  exact ⟨fun i => (b i).toHomUnits, hd⟩

private theorem norm_le_one_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ y : c.O, ‖(y : PadicAlgCl l)‖ ≤ 1 := fun y =>
    norm_le_one_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  show ‖((u : c.O) : PadicAlgCl l)‖ = 1
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem UpperTheory.V.U3.pt_fixed :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
      (D : Dat Ω K c e ψ)
      {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))}
      {g₁ : G ℚ Ω}, D.Marked g₁ →
      ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r),
      Upper D.η r → Lower D.η r → r = r0 D.η D.ΨQ := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hU hL
  obtain ⟨a, ha⟩ := exists_diag D.η r h.mult hU hL
  obtain ⟨-, -, -, -, -, hkill, -, -, hcont, -, hab⟩ := dat_facts D
  let t : D.η.ker →* (PadicAlgCl l)ˣ := D.ΨQ.comp D.η.ker.subtype
  have htv : ∀ g : G ℚ Ω, (D.ΨQ g : PadicAlgCl l) = algebraMap c.O (PadicAlgCl l) (D.Ψ g : c.O) := fun _ => rfl
  have hr0 : ∀ g : D.η.ker, (r0 D.η D.ΨQ g).mat = Matrix.diagonal fun i => ((t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l) :=
    fun _ => rfl
  have hai : ∀ i (g : D.η.ker), (a i g : PadicAlgCl l) = (r g).mat i i := fun i g => by
    rw [ha g, Matrix.diagonal_apply_eq]
  have hred : ∀ i g, a i g / t g ^ wt1 i ∈ U1 (PadicAlgCl l) := by
    intro i g
    have h1 := h.red g i i
    rw [← hai, hr0, Matrix.diagonal_apply_eq] at h1
    have h2 : ‖((t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
      rw [Units.val_zpow_eq_zpow_val, norm_zpow]
      have : ‖(t g : PadicAlgCl l)‖ = 1 := norm_unit c (D.Ψ g).isUnit
      rw [this, _root_.one_zpow]
    show ‖((a i g / t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1
    rw [Units.val_div_eq_div_val, div_sub_one (Units.ne_zero _), norm_div, h2, div_one]
    exact h1
  have hroot : ∀ i (g : D.η.ker), (r g).mat.charpoly = (r0 D.η D.ΨQ g).mat.charpoly → ∃ j, a i g = t g ^ wt1 j := by
    intro i g hg
    rw [ha, hr0] at hg
    obtain ⟨j, hj⟩ := root_of_charpoly _ _ hg i
    exact ⟨j, Units.ext hj⟩
  have hine : ∀ i (A : ValuationSubring Ω) (g : D.η.ker), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → a i g = t g ^ wt1 i := by
    intro i A g hg
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨hle, s, hs, hsu⟩ := hab A hA
      refine eq_above (U1 _) ((Ine (F := ℚ) A).subgroupOf D.η.ker) (a i) t i (hred i)
        (fun x hx => hroot i x ((pt_inertia_above hC D hM h A hA).1 x hx)) ⟨s, hle hs⟩ hs (fun hu => ?_) g hg
      have h1 := norm_unit c hsu
      rw [map_sub, map_pow, map_one] at h1
      exact absurd hu (not_lt.2 h1.ge)
    · obtain ⟨M, hMc⟩ := pt_inertia_away D hM h A hA
      refine eq_away (U1 _) ((Ine (F := ℚ) A).subgroupOf D.η.ker) (a i) t i (hred i)
        (fun x hx => hroot i x ?_) (fun x hx hu => ?_) g hg
      · have h1 : (r0 D.η D.ΨQ x).mat = (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r x).mat *
            ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
          rw [hMc x hx x.2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [h1, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      · have h1 : ¬ IsUnit ((D.Ψ x : c.O) - 1) := fun hx1 => by
          have h1 := norm_unit c hx1
          rw [map_sub, map_one] at h1
          exact absurd hu (not_lt.2 h1.ge)
        have h2 : barChar c.O D.Ψ x = 1 := by
          apply Units.ext
          show residue c.O (D.Ψ x : c.O) = 1
          rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub, residue_eq_zero_iff]
          exact h1
        have h3 : (x : G ℚ Ω) ∈ D.Kill := by
          refine ⟨A, hA, hx, SemidirectProduct.ext ?_ x.2⟩
          show tor _ (barChar c.O D.Ψ x) = 1
          rw [h2, map_one]
        have h4 := congrArg (fun y => GG.mat y 0 0) (hkill x h3)
        have h5 : (D.Ψ x : c.O) = 1 := by simpa [GG.mat, tor_val, wt1] using h4
        apply Units.ext
        show (D.ΨQ x : PadicAlgCl l) = 1
        rw [htv, h5, map_one]
  have hall : ∀ i g, a i g = t g ^ wt1 i := by
    intro i g
    have hk := char_eq_one D (a i / (zpowGroupHom (wt1 i)).comp t) ?_ (hred i)
      (fun A g hg => div_eq_one.2 (hine i A g hg))
    · exact div_eq_one.1 (DFunLike.congr_fun hk g)
    · have c1 : Continuous fun g : D.η.ker => (r g).mat i i :=
        (h.cont.comp continuous_subtype_val).matrix_elem i i
      have c2 : Continuous fun g : D.η.ker => (t g : PadicAlgCl l) :=
        Units.continuous_val.comp (hcont.comp continuous_subtype_val)
      refine (c1.div (c2.zpow₀ (wt1 i) fun g => Or.inl (Units.ne_zero _))
        fun g => zpow_ne_zero _ (Units.ne_zero _)).congr fun g => ?_
      show _ = ((a i g / t g ^ wt1 i : (PadicAlgCl l)ˣ) : PadicAlgCl l)
      rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, hai]
      rfl
  have hker : ∀ g ∈ D.η.ker, r g = r0 D.η D.ΨQ g := by
    intro g hg
    refine SemidirectProduct.ext (Units.ext ?_) (h.mult g)
    show (r (⟨g, hg⟩ : D.η.ker)).mat = (r0 D.η D.ΨQ (⟨g, hg⟩ : D.η.ker)).mat
    rw [ha, hr0]
    simp only [hall]
  have hc : r D.cc = r0 D.η D.ΨQ D.cc := by
    refine SemidirectProduct.ext (Units.ext ?_) (h.mult _)
    have h1 : D.ΨQ D.cc = 1 := by
      apply Units.ext
      rw [htv, hM.Ψc]
      simp
    rw [unitaryThreeReflection_left, h1, map_one]
    exact h.norm.atc
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (D.η g) with hg | hg
  · exact hker g hg
  · have h1 : g * D.cc ∈ D.η.ker := by
      rw [MonoidHom.mem_ker, map_mul, hg, hM.ηc]
      simp
    have h2 := hker _ h1
    rw [map_mul, map_mul, hc] at h2
    exact mul_right_cancel h2
end
