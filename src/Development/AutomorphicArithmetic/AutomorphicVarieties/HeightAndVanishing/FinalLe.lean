module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CokerAb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaAbsTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ReductionToDirichletCharAnyLevelOfLe
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelDown
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelLocal
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_ker_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _))

theorem UpperTheory.V.Base.selLocal :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R ((LocSel ρ U' 𝒟).comap (resU ρ h)) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 ι _ D hD hcov
  set X := (LocSel ρ U' 𝒟).comap (resU ρ h) with hX
  have key0 : ∀ x ∈ X, ∀ D' ∈ 𝒟, resU ρ (le_trans inf_le_left h : U' ⊓ D' ≤ U) x = 0 := by
    intro x hx D' hD'
    have e := (mem_locSel.mp (Submodule.mem_comap.mp hx)) D' hD'
    rw [resU_resU] at e
    exact e
  have key : ∀ x ∈ X, ∀ D' ∈ 𝒟,
      resU ρ (inf_le_inf_right D' h) (resU ρ (inf_le_left : U ⊓ D' ≤ U) x) = 0 := by
    intro x hx D' hD'
    rw [resU_resU]
    exact key0 x hx D' hD'
  let f : X →ₗ[R] (∀ i, LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    LinearMap.pi fun i => LinearMap.codRestrict _
      ((resU ρ (inf_le_left : U ⊓ D i ≤ U)).comp X.subtype)
      (fun x => LinearMap.mem_ker.mpr (key x.1 x.2 (D i) (hD i)))
  have hmem : ∀ y ∈ LinearMap.ker f, ((y : H1U ρ U)) ∈ LocSel ρ U 𝒟 := by
    intro y hy
    have hy' : ∀ i, resU ρ (inf_le_left : U ⊓ D i ≤ U) (y : H1U ρ U) = 0 := by
      intro i
      simpa [f] using congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hy) i)
    rw [mem_locSel]
    intro D' hD'
    rcases hcov D' hD' with hle | ⟨i, u, hu, hconj⟩
    · have e := resU_resU ρ (le_inf hle inf_le_right : U ⊓ D' ≤ U' ⊓ D')
        (le_trans inf_le_left h) (y : H1U ρ U)
      rw [key0 _ y.2 D' hD', map_zero] at e
      exact e.symm
    · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y : H1U ρ U)
      have h0 := hy' i
      rw [← hz] at h0 ⊢
      rw [resU_mk_eq_zero] at h0 ⊢
      obtain ⟨m, hm⟩ := h0
      refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun v => ?_⟩
      have hvU : (v : G) ∈ U := (Subgroup.mem_inf.mp v.2).1
      have hwD : u⁻¹ * (v : G) * u ∈ D i := hconj v v.2
      have hwU : u⁻¹ * (v : G) * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu
      have e1 : z.1 ⟨u⁻¹ * (v : G) * u, hwU⟩ = ρ (u⁻¹ * (v : G) * u) m - m :=
        hm ⟨u⁻¹ * (v : G) * u, Subgroup.mem_inf.mpr ⟨hwU, hwD⟩⟩
      have hc := z.2.2
      have c1 := hc ⟨v, hvU⟩ ⟨u, hu⟩
      have c2 := hc ⟨u, hu⟩ ⟨u⁻¹ * (v : G) * u, hwU⟩
      have eq : (⟨v, hvU⟩ * ⟨u, hu⟩ : U) = ⟨u, hu⟩ * ⟨u⁻¹ * (v : G) * u, hwU⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [eq, c2, e1] at c1
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at c1
      have hr : ρ u (ρ (u⁻¹ * (v : G) * u) m) = ρ v (ρ u m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [map_sub, hr] at c1
      show z.1 ⟨v, hvU⟩ = _
      rw [eq_sub_of_add_eq c1.symm]
      simp only [map_sub]
      abel
  let g : LinearMap.ker f →ₗ[R] LocSel ρ U 𝒟 :=
    LinearMap.codRestrict _ (X.subtype.comp (LinearMap.ker f).subtype) (fun y => hmem y.1 y.2)
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    exact e
  have e := length_le_of_ker_le f g hg
  rwa [Module.length_pi_of_fintype] at e
end

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_addMonoidHom_le_of_card_eq {R A B C X : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
    (f : A →ₗ[R] X) (j : B →ₗ[R] X) (hj : Function.Injective j) (g : B →ₗ[R] C)
    (h : ∀ x, g x = 0 → j x ∈ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := congrArg Subtype.val hx
      simpa [LinearMap.mem_ker] using this
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simpa using y.2
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  gcongr
  · let φ : LinearMap.ker g →ₗ[R] LinearMap.range f :=
      (j.comp (LinearMap.ker g).subtype).codRestrict (LinearMap.range f) (fun x => h x x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact congrArg Subtype.val hab
    calc Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.range f) :=
          Module.length_le_of_injective φ hφ
      _ ≤ Module.length R A := Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  · exact Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)

theorem UpperTheory.V.Base.selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) + Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1,
      ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
    intro x
    rw [Representation.mem_invariants]
    intro u
    have := (mem_eig.mp x.2) u
    simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := by
    intro x hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨y, ?_⟩, hy⟩
    show resU ρ h y ∈ LocSel ρ U' 𝒟
    rw [hy]
    exact (x : LocSel ρ U' 𝒟).2
  refine le_trans (length_addMonoidHom_le_of_card_eq ((resU ρ h).comp A.subtype) j hj g hker) ?_
  gcongr
  exact selLocal R G M ρ U' U h 𝒟 ι D hD hcov
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RelIndexInfDvd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.KerFin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem kerFin_triv {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U' U : Subgroup G) (h : U' ≤ U) (hρ : ∀ u ∈ U, ∀ m, ρ u m = m) (n : ℕ) (hn : ∀ u ∈ U, u ^ n ∈ U')
    [Fintype (U ⧸ U'.subgroupOf U)] :
    Module.length R (LinearMap.ker (resU ρ h)) ≤ (Fintype.card (U ⧸ U'.subgroupOf U) : ℕ∞) *
      Module.length R (LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M))) := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  set N := LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M)) with hN
  have hadd : ∀ z ∈ Z1U ρ U, ∀ a b : U, z (a * b) = z a + z b := by
    intro z hz a b
    have := ((mem_Z1_iff_cocycle (ρ.comp U.subtype) z).mp hz).2 a b
    rw [this, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ a a.2]
  have hone : ∀ z ∈ Z1U ρ U, z 1 = 0 := by
    intro z hz
    have := hadd z hz 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ z ∈ Z1U ρ U, ∀ a : U, z a⁻¹ = - z a := by
    intro z hz a
    have := hadd z hz a a⁻¹
    rw [mul_inv_cancel, hone z hz] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hpow : ∀ z ∈ Z1U ρ U, ∀ a : U, ∀ k : ℕ, z (a ^ k) = k • z a := by
    intro z hz a k
    induction k with
    | zero => rw [pow_zero, hone z hz, zero_smul]
    | succ k ih => rw [pow_succ, hadd z hz, ih, succ_nsmul]
  have hB : ∀ z ∈ Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype)), (z : U → M) = 0 := by
    intro z hz
    rw [Submodule.mem_comap, B1, LinearMap.mem_range] at hz
    obtain ⟨m, hm⟩ := hz
    funext u
    rw [Submodule.coe_subtype] at hm
    rw [← hm, amitsur_d0_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ u u.2, sub_self]
    rfl
  let ev : (Z1U ρ U) →ₗ[R] (U ⧸ K → M) :=
    LinearMap.pi (fun q => (LinearMap.proj (Quotient.out q) : (U → M) →ₗ[R] M) ∘ₗ (Z1U ρ U).subtype)
  have hev : ∀ z q, ev z q = (z : U → M) (Quotient.out q) := fun z q => rfl
  let Φ : H1U ρ U →ₗ[R] (U ⧸ K → M) :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype))).liftQ ev (by
      intro z hz
      rw [LinearMap.mem_ker]
      funext q
      rw [hev, hB z hz]
      rfl)
  have hΦ : ∀ z q, Φ (Submodule.Quotient.mk z) q = (z : U → M) (Quotient.out q) := fun z q => rfl
  have hvan : ∀ z : Z1U ρ U, resU ρ h (Submodule.Quotient.mk z) = 0 → ∀ u : U, (u : G) ∈ U' → (z : U → M) u = 0 := by
    intro z hz u hu
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).mp hz
    have := hm ⟨(u : G), hu⟩
    rw [hρ _ (h hu), sub_self] at this
    exact this
  have key : ∀ x ∈ LinearMap.ker (resU ρ h), ∀ q, Φ x q ∈ N := by
    intro x hx q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    rw [hΦ, hN, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul,
      ← hpow z z.2]
    exact hvan z hx _ (hn _ (Quotient.out q).2)
  let Ψ : LinearMap.ker (resU ρ h) →ₗ[R] (U ⧸ K → N) :=
    LinearMap.pi (fun q => LinearMap.codRestrict N
      ((LinearMap.proj q : (U ⧸ K → M) →ₗ[R] M) ∘ₗ Φ ∘ₗ (LinearMap.ker (resU ρ h)).subtype)
      (fun x => key x.1 x.2 q))
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hxk⟩ hx0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hq : ∀ q : U ⧸ K, (z : U → M) (Quotient.out q) = 0 := by
      intro q
      have := congrArg (fun f => ((f q : N) : M)) hx0
      exact this
    have hz : (z : U → M) = 0 := by
      funext u
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K u
      have hkU : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
      have hu : u = Quotient.out (QuotientGroup.mk u : U ⧸ K) * (k : U)⁻¹ := by
        rw [hk]; group
      rw [hu, hadd z z.2, hq, hinv z z.2, hvan z hxk _ hkU, neg_zero, add_zero]
      rfl
    have hz' : z = 0 := Subtype.ext hz
    subst hz'
    rfl
  calc Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (U ⧸ K → N) :=
        Module.length_le_of_injective Ψ hΨ
    _ = _ := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

private theorem exists_doubleCoset_section {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), U' ≤ θ.ker → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hc U' U h hker hcomm n hn hdiv
  classical
  have h0 : U'.relIndex U ≠ 0 := fun hz => hn (Nat.eq_zero_of_zero_dvd (hz ▸ hdiv))
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  have hnorm : K.Normal := by
    constructor
    intro k hk g
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    have hcm := hcomm g g.2 k k.2
    have : ((g * k * g⁻¹ : U) : G) = ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹) * k := by
      push_cast; group
    rw [this]
    exact U'.mul_mem hcm hk
  have hcardK : Nat.card (U ⧸ K) = U'.relIndex U := by
    rw [Subgroup.relIndex, ← hK, Subgroup.index]
  have hpowU : ∀ u ∈ U, u ^ n ∈ U' := by
    intro u hu
    obtain ⟨c, hc'⟩ := hdiv
    have h1 : (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) ^ (U'.relIndex U) = 1 := by
      rw [← hcardK]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    rw [hc', pow_mul]
    have : ((⟨u, hu⟩ : U) ^ (U'.relIndex U) : U) = (u ^ (U'.relIndex U) : G) := by simp
    rw [this] at h1
    exact U'.pow_mem h1 c
  have hrel_le : U'.relIndex U ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  obtain ⟨_, hζ, heOtop, _⟩ := rootVal l O n hn
  have hact : ∀ g m, twist₂ l θ g m = ((θ g : Oˣ) : O) • m := fun g m => by
    rw [twist₂, scalRep_apply]
  by_cases htriv : U ≤ θ.ker
  · have hρ : ∀ u ∈ U, ∀ m, twist₂ l θ u m = m := by
      intro u hu m
      rw [hact, htriv hu, Units.val_one, one_smul]
    have := kerFin_triv (twist₂ l θ) U' U h hρ n hpowU
    refine this.trans ?_
    rw [(qoFacts l O).2.2.2, (rootVal l O n hn).1, Fintype.card_eq_nat_card, hcardK]
    push_cast
    rw [← mul_assoc]
    gcongr
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp htriv
    set ζ : O := ((θ g : Oˣ) : O) with hζdef
    have hθn : (θ g) ^ n = 1 := by
      rw [← map_pow]
      exact hker (hpowU g hg)
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, hθn, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      exact Units.ext h1
    have hsub : H0U (twist₂ l θ) U ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (twist₂ l θ) U) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    obtain ⟨T, hTU, hTcard, hTcl⟩ := exists_doubleCoset_section U' U h0
    have key := kerResAb O G (QO l O) (twist₂ l θ) hc (qoFacts l O).1
      (fun g => ⟨(θ g : O), fun m => hact g m⟩) U' U h hcomm T hTU
      (hTcl.trans (Subgroup.le_topologicalClosure _))
    refine key.trans ?_
    have hle : T.card ≤ n := hTcard.trans hrel_le
    calc (T.card : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) ≤ (n : ℕ∞) * ((n.factorization l : ℕ∞) * eO l O) := by
          gcongr
      _ = ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
          push_cast
          rw [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.KerIdx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_reps {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerIdx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ (n : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hθ U' U h hab n hn hd
  obtain ⟨T, hT, hc, hU⟩ := exists_reps U' U (ne_zero_of_dvd_ne_zero hn hd)
  have key := UpperTheory.V.Base.kerResAb O G (QO l O) (twist₂ l θ) hθ (UpperTheory.V.Base.qoFacts l O).1
    (fun g => ⟨((θ g : Oˣ) : O), fun _ => rfl⟩) U' U h hab T hT (hU.trans (Subgroup.le_topologicalClosure _))
  refine key.trans ?_
  have : (T.card : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hc.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
  gcongr
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem comm_inf {G : Type} [Group G] (U' D : Subgroup G) (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ U') :
    ∀ a ∈ ⊤ ⊓ D, ∀ b ∈ ⊤ ⊓ D, a * b * a⁻¹ * b⁻¹ ∈ U' ⊓ D := fun a ha b hb =>
  ⟨h a b, D.mul_mem (D.mul_mem (D.mul_mem ha.2 hb.2) (D.inv_mem ha.2)) (D.inv_mem hb.2)⟩

theorem UpperTheory.V.Chr.eigLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → levH ℚ Ω H ≤ ψ.ker →
          eigL l e (levH ℚ Ω H) ψ ≤ V l e ψ + (loss l N H.index e : ℕ∞) * eO l O := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ e ψ he hψ
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hopen, -, -, -, hine⟩ := clsFacts ℚ Ω N
  obtain ⟨hex, hN, hconj⟩ := placesQ Ω
  have hk : (cls ℚ Ω N).ker ≤ levH ℚ Ω H := fun g hg => by
    show cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.1 hg]
    exact H.one_mem
  have hUo : IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := Subgroup.isOpen_mono hk hopen
  have hψi : levH ℚ Ω H ≤ (ψ⁻¹).ker := fun g hg => by
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.mem_ker.1 (hψ hg), inv_one]
  have hc : ContAction (rho l e ψ) := (contTw ℚ Ω l).2.2 O ψ⁻¹ _ (Subgroup.isOpen_mono hψi hUo)
  have hcomm : ∀ a b : G ℚ Ω, a * b * a⁻¹ * b⁻¹ ∈ levH ℚ Ω H := fun a b => by
    show cls ℚ Ω N _ ∈ H
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, mul_inv_cancel]
    exact H.one_mem
  have hn : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdvd : (levH ℚ Ω H).relIndex ⊤ ∣ H.index := by
    rw [Subgroup.relIndex_top_right, levH, Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨hb1, hb2⟩ := H0_local_card_bounded_of_cls_ker_le_ker Ω l O N e ψ he (hk.trans hψ)
  obtain ⟨A₀, hA₀⟩ := hex l hl.out
  have hA : ∀ p : N.primeFactors, ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧
      ∀ A' : ValuationSubring Ω, A'.valuation ((p : ℕ) : Ω) < 1 → ¬ A'.valuation (l : Ω) < 1 →
        ∃ u : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) A', u⁻¹ * x * u ∈ Ine (F := ℚ) A := by
    intro p
    by_cases h : ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 ∧ ¬ A.valuation (l : Ω) < 1
    · obtain ⟨A, h1, h2⟩ := h
      exact ⟨A, h2, fun A' h3 _ =>
        (hconj p A' A (Nat.prime_of_mem_primeFactors p.2) h3 h1).imp fun _ hu => hu.2⟩
    · exact ⟨⊤, ((places ℚ Ω l ⊤).2.1 rfl).2, fun A' h3 h4 => absurd ⟨A', h3, h4⟩ h⟩
  choose A hAl hAc using hA
  have hID : ∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ Dec (F := ℚ) B := fun _ _ h => h.1
  let D : Option N.primeFactors → Subgroup (G ℚ Ω) := fun i => i.elim (Dec (F := ℚ) A₀) fun p => Ine (F := ℚ) (A p)
  have h1 := selDown O _ _ (rho l e ψ) (levH ℚ Ω H) ⊤ le_top _ (conjStable_shaFam ℚ Ω l) _ D
    (by
      rintro (_ | p)
      · exact Or.inl ⟨A₀, hA₀, rfl⟩
      · exact Or.inr ⟨A p, rfl⟩)
    (by
      have hd : ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
          ∃ u : G ℚ Ω, ∀ x ∈ Dec (F := ℚ) B, u⁻¹ * x * u ∈ D none := fun B hB =>
        (hconj l B A₀ hl.out hB hA₀).imp fun _ hu => hu.1
      rintro _ (⟨B, hB, rfl⟩ | ⟨B, rfl⟩)
      · obtain ⟨u, hu⟩ := hd B hB
        exact Or.inr ⟨none, u, trivial, fun x hx => hu x hx.2⟩
      · by_cases hB : B.valuation (l : Ω) < 1
        · obtain ⟨u, hu⟩ := hd B hB
          exact Or.inr ⟨none, u, trivial, fun x hx => hu x (hID B hx.2)⟩
        · by_cases hB' : B.valuation (N : Ω) < 1
          · obtain ⟨p, hp, hp'⟩ := (hN B N (NeZero.ne N)).1 hB'
            obtain ⟨u, hu⟩ := hAc ⟨p, hp⟩ B hp' hB
            exact Or.inr ⟨some ⟨p, hp⟩, u, trivial, fun x hx => hu x hx.2⟩
          · exact Or.inl (inf_le_right.trans ((hine B hB').trans hk)))
  have h2 := (selTwist O _ _ (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) (rho l e ψ) ψ (tw_apply l e ψ) (levH ℚ Ω H)
    (fun u hu => hψ hu) _ (conjStable_shaFam ℚ Ω l)).2 ⊤ 1
  rw [mul_one] at h2
  have h3 := cokerAb O _ _ (rho l e ψ) hc (qoFacts l O).1 (fun g => ⟨_, fun _ => rfl⟩) (levH ℚ Ω H) ⊤ le_top
    isClosed_univ (hUo.preimage continuous_subtype_val) fun a _ b _ => hcomm a b
  have h3' := h3.trans (mul_le_mul' (pow_le_pow_left' (Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)) 2) hb2)
  have h4 := (kerIdx l O _ _ hc _ _ (inf_le_inf_right (D none) (le_top : levH ℚ Ω H ≤ ⊤)) (comm_inf _ _ hcomm) _ hn
    ((relIndex_inf_dvd _ _ _).trans hdvd)).trans (mul_le_mul' le_rfl (hb1 A₀ _ hA₀ (le_inf le_top (hID A₀))))
  have h5 : ∀ p : N.primeFactors, _ := fun p =>
    kerFin l O _ _ hc _ _ (inf_le_inf_right (D (some p)) (le_top : levH ℚ Ω H ≤ ⊤)) (fun g hg => by
      have e1 : chiO ℚ Ω l O g = 1 := by
        have := MonoidHom.mem_ker.1 ((places ℚ Ω l (A p)).2.2.2 (hAl p) hg.2)
        rw [chiO, MonoidHom.comp_apply, this, map_one]
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hψi hg.1), one_mul]
      show chiO ℚ Ω l O g ^ (-(e : ℤ)) = 1
      rw [e1, one_zpow]) (comm_inf _ _ hcomm) _ hn ((relIndex_inf_dvd _ _ _).trans hdvd)
  rw [Fintype.sum_option] at h1
  have h6 := (Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h5 p).trans_eq (Finset.sum_const _)
  refine (h2.le.trans (h1.trans (add_le_add (add_le_add le_rfl (add_le_add h4 h6)) h3'))).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, loss, add_assoc]
  congr 1
  push_cast
  ring
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr

section Red

variable (E : Type) [Field E] [NumberField E] [IsCMField E] {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}
  {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {Ω' : Type} [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
  (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem levH_le_ker {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : levH ℚ Ω H ≤ (dirG ℚ Ω χ).ker :=
  fun _ hg => h.1 hg

theorem levH_facts : (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) :=
  ⟨Subgroup.index_comap_of_surjective _ (clsOnto Ω N).1,
    Subgroup.isOpen_mono (H₁ := (cls ℚ Ω N).ker) (fun g hg => by
      show cls ℚ Ω N g ∈ H
      rw [MonoidHom.mem_ker.1 hg]; exact one_mem _) (clsFacts ℚ Ω N).1⟩

theorem reduction_to_dirichletChar_any_level (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O)) := by
  obtain ⟨c, hc, hp, hm⟩ := partModel E N H hE l O Ω' D Ω e
  rw [(levGal E N H hE).2.1, hp, hm]
  exact ⟨fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ))),
    fun hT => (signLe Ω N H l O h2 e _ c hc T hT.ge).trans (Finset.sum_le_sum fun χ hχ =>
      eigLe Ω N H l O e _ he (levH_le_ker O Ω (hT.le hχ)))⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem dirG_pow {s : ℕ} {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) : dirG ℚ Ω χ ^ H.index = 1 := by
  unfold evenSet at h
  have hH : H ≤ (MulChar.toUnitHom χ).ker := h.1
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  unfold dirG
  rw [MonoidHom.comp_apply, ← map_pow, ← MonoidHom.mem_ker]
  exact hH (H.pow_index_mem _)

theorem V_le_V' {s e : ℕ} (he : e ≠ 0) {χ : DirichletCharacter O N} (h : χ ∈ evenSet O H s) {N' : ℕ} (hN : N' ≠ 0) :
    V l e (dirG ℚ Ω χ) ≤ V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O ∧
    (¬ l ∣ H.index → V l e (dirG ℚ Ω χ) = V' l N' e (dirG ℚ Ω χ)) := by
  have hopen : IsOpen ((dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (levH_le_ker (O := O) (Ω := Ω) h) (levH_facts (Ω := Ω) (H := H)).2
  have hpow := dirG_pow (O := O) (Ω := Ω) h
  exact vLe Ω l O N' e H.index _ hN he Subgroup.index_ne_zero_of_finite hopen hpow

theorem reduction_to_dirichletChar_any_level_of_le (hE : HasLevel E N H) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))] (h2 : l ≠ 2)
    {e : ℕ} (he : e ≠ 0) (T : Finset (DirichletCharacter O N)) {N' : ℕ} (hN : N' ≠ 0) :
    (↑T = evenSet O H e → plusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) ∧
    (↑T = evenSet O H (e + 1) → minusLen D e * eO l O ≤ ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
      ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O)) := by
  have hrank : Module.finrank ℚ E = H.index := (levGal E N H hE).2.1
  have key := reduction_to_dirichletChar_any_level (E := E) (O := O) (D := D) (Ω := Ω) hE h2 he T
  have hsum : ∀ s, (↑T : Set (DirichletCharacter O N)) = evenSet O H s →
      ∑ χ ∈ T, (V l e (dirG ℚ Ω χ) + (loss l N (Module.finrank ℚ E) e : ℕ∞) * eO l O) ≤
        ∑ χ ∈ T, (V' l N' e (dirG ℚ Ω χ) +
          ((loss l N (Module.finrank ℚ E) e + N'.primeFactors.card * (Module.finrank ℚ E).factorization l : ℕ) : ℕ∞) * eO l O) := by
    intro s hT
    refine Finset.sum_le_sum fun χ hχ => ?_
    have hχ' : χ ∈ evenSet O H s := by rw [← hT]; exact hχ
    have h1 := (V_le_V' (l := l) (O := O) (Ω := Ω) he hχ' hN).1
    rw [hrank]
    calc V l e (dirG ℚ Ω χ) + (loss l N H.index e : ℕ∞) * eO l O
        ≤ (V' l N' e (dirG ℚ Ω χ) + ((N'.primeFactors.card * H.index.factorization l : ℕ) : ℕ∞) * eO l O) +
          (loss l N H.index e : ℕ∞) * eO l O := add_le_add h1 le_rfl
      _ = _ := by push_cast; ring
  exact ⟨fun hT => (key.1 hT).trans (hsum e hT), fun hT => (key.2 hT).trans (hsum (e + 1) hT)⟩

end Red

end UpperTheory.V.Chr

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.RedAll
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.redAll :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, (Vlen Ω c e ψ + (lossAll l N H.index e : ℕ∞) * eO l c.O) := by
  intro E _ _ _ N _ H hH l _ hl2 c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI : NeZero (Nat.totient N) := ⟨(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩
  haveI : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    refine HasEnoughRootsOfUnity.of_dvd c.O (n := Nat.totient N) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => ?_)
    induction g using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, ZMod.pow_totient, QuotientGroup.mk_one]
  have hfr := (Chr.levGal E N H hH).2.1
  have key := (Chr.reduction_to_dirichletChar_any_level_of_le E c.O D Ω hH hl2 he T (N' := N) (NeZero.ne N)).1 hT
  rw [hfr] at key
  exact key
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem sum_split {ι : Type} (T : ℕ → Finset ι) (O : Finset ι) (v : ι → ℕ → ℝ) (t N q : ℕ) (L K S : ℝ)
    (hv : ∀ i e, 0 ≤ v i e) (hL : 0 ≤ L) (hK : 0 ≤ K) (hS : 0 ≤ S) (hT : ∀ e, (T e).card ≤ N) (hq : O.card ≤ q)
    (h1 : ∀ e ∈ Finset.Ico 1 t, ∀ i ∈ T e, i ∈ O ∨ v i e * L ≤ K)
    (h2 : ∀ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ S) :
    L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e ≤ L * (q * S) + t * (N * K) := by
  classical
  have step : ∀ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e ≤ L * ∑ i ∈ O, v i e + N * K := by
    intro e he
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ i ∈ T e, L * v i e ≤ ∑ i ∈ T e, ((if i ∈ O then L * v i e else 0) + K) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hO : i ∈ O
          · rw [if_pos hO]
            linarith
          · rw [if_neg hO]
            rcases h1 e he i hi with h | h
            · exact absurd h hO
            · linarith [mul_comm (v i e) L]
      _ = ∑ i ∈ T e ∩ O, L * v i e + (T e).card * K := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem]
      _ ≤ ∑ i ∈ O, L * v i e + N * K := by
          apply add_le_add
          · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => mul_nonneg hL (hv i e))
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT e) hK
  have hA : ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ q * S := by
    calc ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e ≤ ∑ i ∈ O, S := Finset.sum_le_sum h2
      _ = O.card * S := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ q * S := mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hS
  have hB : ((Finset.Ico 1 t).card : ℝ) ≤ t := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le t 1
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  calc L * ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, v i e
      = ∑ e ∈ Finset.Ico 1 t, L * ∑ i ∈ T e, v i e := Finset.mul_sum _ _ _
    _ ≤ ∑ e ∈ Finset.Ico 1 t, (L * ∑ i ∈ O, v i e + N * K) := Finset.sum_le_sum step
    _ = L * ∑ i ∈ O, ∑ e ∈ Finset.Ico 1 t, v i e + ((Finset.Ico 1 t).card : ℝ) * (N * K) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ L * (q * S) + t * (N * K) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hL) (mul_le_mul_of_nonneg_right hB hNK)

private theorem final_le (M L l q N t B : ℝ) (a b C : ℕ) (hM : M = N * t) (h3 : 3 ≤ M) (hL : L ≤ l)
    (hl : 0 ≤ l) (hlM : l ≤ M) (hq : 0 ≤ q) (hqM : q ≤ M) (hB : 0 ≤ B) (hC : a + 2 * b + 9 ≤ C) (hC' : l * q ≤ C) :
    L * (q * (B + M ^ a)) + t * (N * (M ^ 2) ^ b) + L * (N * (t * M ^ 6)) ≤ M ^ C + C * B := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hNt : N * (t * M ^ 6) = M ^ 7 := by
    rw [hM]
    ring
  have hNb : t * (N * (M ^ 2) ^ b) = M ^ (2 * b + 1) := by
    rw [hM]
    ring
  rw [hNt, hNb]
  have hX : 0 ≤ q * (B + M ^ a) := mul_nonneg hq (by positivity)
  have e1 : L * (q * (B + M ^ a)) ≤ l * (q * (B + M ^ a)) := mul_le_mul_of_nonneg_right hL hX
  have e2 : l * (q * (B + M ^ a)) = (l * q) * B + l * q * M ^ a := by ring
  have e3 : (l * q) * B ≤ C * B := mul_le_mul_of_nonneg_right hC' hB
  have hlq : l * q ≤ M * M := mul_le_mul hlM hqM hq hM0
  have e4 : l * q * M ^ a ≤ M * M * M ^ a := mul_le_mul_of_nonneg_right hlq (pow_nonneg hM0 a)
  have e4' : M * M * M ^ a = M ^ (a + 2) := by ring
  have e5 : L * M ^ 7 ≤ l * M ^ 7 := mul_le_mul_of_nonneg_right hL (pow_nonneg hM0 7)
  have e6 : l * M ^ 7 ≤ M * M ^ 7 := mul_le_mul_of_nonneg_right hlM (pow_nonneg hM0 7)
  have e6' : M * M ^ 7 = M ^ 8 := by ring
  obtain ⟨D, hD⟩ : ∃ D, C = D + 1 := ⟨C - 1, by omega⟩
  have p1 : M ^ (a + 2) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p2 : M ^ (2 * b + 1) ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p3 : M ^ 8 ≤ M ^ D := pow_le_pow_right₀ hM1 (by omega)
  have p4 : 3 * M ^ D ≤ M * M ^ D := mul_le_mul_of_nonneg_right h3 (pow_nonneg hM0 D)
  have p5 : M ^ C = M * M ^ D := by rw [hD, pow_succ']
  linarith

theorem UpperTheory.V.HV.sumIn :
    CountII → CountV → CountVs → CountIV → SumIn := by
  unfold SumIn
  intro hII hV hVs hIV χ l j hl
  haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.instIsAlgClosure (k := ℚ))
  obtain ⟨C2, hC2⟩ := hII χ
  obtain ⟨C5, hC5⟩ := hV χ
  obtain ⟨C6, hC6⟩ := hVs χ
  obtain ⟨C4, hC4⟩ := hIV χ (l : ℕ) j hl
  set Cm := max C2 (max C5 C6) with hCm
  refine ⟨C4 + 2 * Cm + 9 + (l : ℕ) * χ.N, ?_⟩
  intro h hχ t ht2 hBig B hB hLay E _ _ _ hE Ω _ _ _ ld
  classical
  haveI : NeZero h.N := ⟨h.N_pos.ne'⟩
  haveI : NeZero (Nat.totient h.N) := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  obtain ⟨c, hc⟩ := exists_coef (l : ℕ) (Nat.totient h.N)
  haveI := hc
  have hlp : (l : ℕ).Prime := l.2
  have hl2 : (l : ℕ) ≠ 2 := (prime_of_mem_Bchi hl).2
  have hlB : (l : ℕ) ∈ Bchi h.chi := by
    rw [hχ]
    exact hl
  have hbf := bchiFacts h t hBig
  have hlq1 : (l : ℕ) < h.q1 := (hbf.1 _ hlB).1
  have hld : (l : ℕ) < h.d := (hbf.1 _ hlB).2
  have hidx := hostIndex h
  have hNpos : 0 < h.N := h.N_pos
  have hq1N : h.q1 ≤ h.N := Nat.le_of_dvd hNpos h.host_q1_dvd_N
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hNpos h.q_dvd
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hNpos hidx.2.2.1
  have hlN : (l : ℕ) ≤ h.N := by omega
  set M : ℝ := (h.N : ℝ) * t with hMdef
  set L : ℝ := Real.log ((l : ℕ) : ℝ) with hLdef
  have hN1 : (1 : ℝ) ≤ h.N := by exact_mod_cast (by omega : 1 ≤ h.N)
  have hM3 : 3 ≤ M := by
    have a1 : (16 : ℝ) ≤ h.N := by exact_mod_cast h16
    have a2 : (2 : ℝ) ≤ t := by exact_mod_cast ht2
    rw [hMdef]
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hl1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hL0 : 0 ≤ L := Real.log_nonneg hl1
  have hLl : L ≤ ((l : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((l : ℕ) : ℝ) by linarith)
    linarith
  have hNM : (h.N : ℝ) ≤ M := by
    have a2 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    rw [hMdef]
    nlinarith
  have hlM : ((l : ℕ) : ℝ) ≤ M := le_trans (by exact_mod_cast hlN) hNM
  have hqM : (h.q : ℝ) ≤ M := le_trans (by exact_mod_cast hqN) hNM
  have hKb : ∀ e, 0 < e → e < t → ∀ k ≤ Cm, (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (M ^ 2) ^ Cm := by
    intro e he0 het k hk
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
    have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
    have hx1 : 1 ≤ ((l : ℕ) : ℝ) * h.N * e := by
      have a1 : 1 ≤ ((l : ℕ) : ℝ) * h.N := by nlinarith
      nlinarith
    have hx2 : ((l : ℕ) : ℝ) * h.N * e ≤ M ^ 2 := by
      have a1 : (h.N : ℝ) * e ≤ M := by
        rw [hMdef]
        exact mul_le_mul_of_nonneg_left het' (by linarith)
      calc ((l : ℕ) : ℝ) * h.N * e = ((l : ℕ) : ℝ) * (h.N * e) := by ring
        _ ≤ M * M := mul_le_mul hlM a1 (by positivity) hM0
        _ = M ^ 2 := by ring
    calc (((l : ℕ) : ℝ) * h.N * e) ^ k ≤ (((l : ℕ) : ℝ) * h.N * e) ^ Cm := pow_le_pow_right₀ hx1 hk
      _ ≤ (M ^ 2) ^ Cm := pow_le_pow_left₀ (by linarith) hx2 Cm
  let Oset : Finset (DirichletCharacter c.O h.N) :=
    (Finset.Ico 1 t).biUnion (fun e => (h.X c e).filter (fun ψ => Odd (orderOf (chiP (l : ℕ) ψ))))
  have hkey : ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X c e,
      Vlen (AlgebraicClosure ℚ) c e ψ ≠ ⊤ ∧
        (ψ ∈ Oset ∨ Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) * L ≤ (M ^ 2) ^ Cm) := by
    intro e he0 het ψ hψ
    have hchar := ((Host.mem_X h).1 hψ).1
    rcases (UpperTheory.V.HV.cases h t hBig c.O ψ hchar (l : ℕ) e hlp hl2 he0 het).2 hlB with hc2 | hc4 | hc5
    · have hv := hC2 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ hc2
      exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C2 (le_max_left _ _)))⟩
    · have hs := hC4 h hχ t ht2 hBig B hLay (AlgebraicClosure ℚ) c ψ hchar hc4.2.2
      refine ⟨hs.1 e he0 het, Or.inl ?_⟩
      exact Finset.mem_biUnion.2 ⟨e, Finset.mem_Ico.2 ⟨he0, het⟩, Finset.mem_filter.2 ⟨hψ, hc4.2.2⟩⟩
    · by_cases hR : h.R1 (l : ℕ) ψ ≤ 2 ^ c2 ψ
      · have hv := hC5 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ ⟨hc5, hR⟩
        exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C5 (le_trans (le_max_left _ _) (le_max_right _ _))))⟩
      · have hv := hC6 h hχ t hBig (AlgebraicClosure ℚ) (l : ℕ) c e hl2 he0 het ψ hψ ⟨hc5, not_le.1 hR⟩
        exact ⟨hv.1, Or.inr (hv.2.trans (hKb e he0 het C6 (le_trans (le_max_right _ _) (le_max_right _ _))))⟩
  have hOcard : Oset.card ≤ h.q := by
    apply (xCard c.O h.N).2 h.q (Nat.pos_of_ne_zero h.chi.ne.out) Oset
    intro ψ hψ
    obtain ⟨e, -, hψ'⟩ := Finset.mem_biUnion.1 hψ
    obtain ⟨hX, hodd⟩ := Finset.mem_filter.1 hψ'
    exact ((hostOdd h c.O ψ ((Host.mem_X h).1 hX).1).2 (l : ℕ) hlp hl2 hlq1.ne hld.ne hodd).1
  have hO2 : ∀ ψ ∈ Oset, ∑ e ∈ Finset.Ico 1 t, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) ≤ B + M ^ C4 := by
    intro ψ hψ
    obtain ⟨e, -, hψ'⟩ := Finset.mem_biUnion.1 hψ
    obtain ⟨hX, hodd⟩ := Finset.mem_filter.1 hψ'
    exact (hC4 h hχ t ht2 hBig B hLay (AlgebraicClosure ℚ) c ψ ((Host.mem_X h).1 hX).1 hodd).2
  have hXsub : ∀ e, h.X c e ⊆ h.X c 0 ∪ h.X c 1 := by
    intro e ψ hψ
    rw [Host.mem_X] at hψ
    rw [Finset.mem_union, Host.mem_X, Host.mem_X]
    have h2 := hψ.2
    unfold PsiEven at h2
    rcases Nat.even_or_odd e with he | he
    · left
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_zero]
    · right
      refine ⟨hψ.1, ?_⟩
      unfold PsiEven
      rw [h2, he.neg_one_pow, pow_one]
  have hred : ∀ e, 0 < e → e < t → plusLen (ld (l : ℕ)) e * eO (l : ℕ) c.O ≤
      ∑ ψ ∈ h.X c e, (Vlen (AlgebraicClosure ℚ) c e ψ + (lossAll (l : ℕ) h.N h.H.index e : ℕ∞) * eO (l : ℕ) c.O) := by
    intro e he0 het
    exact redAll E h.N h.H (hostLevel h E (by rw [hχ]; exact hE)) (l : ℕ) hl2 c Ω (ld (l : ℕ)) (AlgebraicClosure ℚ) e he0.ne' (h.X c e)
      (by
        ext ψ
        rw [Finset.mem_coe, Host.mem_X]
        rfl)
  have hsb := Chr.sumBack (l : ℕ) c.O (DirichletCharacter c.O h.N) (fun e => h.X c e) (h.X c 0 ∪ h.X c 1)
    (fun ψ e => Vlen (AlgebraicClosure ℚ) c e ψ) (fun e => plusLen (ld (l : ℕ)) e)
    (fun e => lossAll (l : ℕ) h.N h.H.index e) t hXsub
    (fun e he0 het => ⟨fun ψ hψ => (hkey e he0 het ψ hψ).1, hred e he0 het⟩)
  have hA : (∑ e ∈ Finset.Ico 1 t, ((plusLen (ld (l : ℕ)) e).toNat : ℝ)) ≤
      (∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X c e, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ)) +
        ((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) := hsb.2
  have hloss : ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ t * M ^ 6 := by
    calc ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, M ^ 6 := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, het⟩ := Finset.mem_Ico.1 he
          have hb := (lossLe (l : ℕ) h.N h.H.index e hlp hl2 (by omega) hidx.2.1 he1).1
          have hb' : ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := by
            exact_mod_cast hb
          have het' : (e : ℝ) ≤ t := by exact_mod_cast het.le
          calc ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) ≤ (((h.N * e) ^ 6 : ℕ) : ℝ) := hb'
            _ = ((h.N : ℝ) * e) ^ 6 := by push_cast; ring
            _ ≤ M ^ 6 := by
              apply pow_le_pow_left₀ (by positivity)
              rw [hMdef]
              exact mul_le_mul_of_nonneg_left het' (by positivity)
      _ = ((Finset.Ico 1 t).card : ℝ) * M ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ t * M ^ 6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le t 1
  have hsplit : L * ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X c e, Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ) ≤
      L * (h.q * (B + M ^ C4)) + t * (h.N * (M ^ 2) ^ Cm) :=
    sum_split (fun e => h.X c e) Oset (fun ψ e => Chr.nrm (l : ℕ) c.O (Vlen (AlgebraicClosure ℚ) c e ψ)) t h.N h.q L
      ((M ^ 2) ^ Cm) (B + M ^ C4) (fun ψ e => Vn_nonneg (AlgebraicClosure ℚ) c e ψ) hL0 (by positivity)
      (add_nonneg hB (pow_nonneg hM0 _)) (fun e => (xCard c.O h.N).1 _) hOcard
      (fun e he ψ hψ => (hkey e (Finset.mem_Ico.1 he).1 (Finset.mem_Ico.1 he).2 ψ hψ).2) hO2
  have hT0 : ((h.X c 0 ∪ h.X c 1).card : ℝ) ≤ h.N := by exact_mod_cast (xCard c.O h.N).1 _
  have hlossnn : 0 ≤ ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have s1 := mul_le_mul_of_nonneg_left hA hL0
  rw [mul_add] at s1
  have s2 : L * (((h.X c 0 ∪ h.X c 1).card : ℝ) * ∑ e ∈ Finset.Ico 1 t, ((lossAll (l : ℕ) h.N h.H.index e : ℕ) : ℝ)) ≤
      L * (h.N * (t * M ^ 6)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hT0 hloss hlossnn (by positivity)) hL0
  have hqC : h.q = χ.N := by
    simp only [Host.q, hχ]
  have hlqC : ((l : ℕ) : ℝ) * h.q ≤ ((C4 + 2 * Cm + 9 + (l : ℕ) * χ.N : ℕ) : ℝ) := by
    rw [hqC]
    exact_mod_cast Nat.le_add_left _ _
  have hfin := final_le M L ((l : ℕ) : ℝ) (h.q : ℝ) (h.N : ℝ) (t : ℝ) B C4 Cm (C4 + 2 * Cm + 9 + (l : ℕ) * χ.N)
    hMdef hM3 hLl (by linarith) hlM (Nat.cast_nonneg _) hqM hB (by omega) hlqC
  refine ⟨?_, ?_⟩
  · intro l' hl' e he0 het
    rw [Finset.mem_singleton] at hl'
    subst hl'
    exact hsb.1 e he0 het
  · rw [Finset.sum_singleton]
    linarith
