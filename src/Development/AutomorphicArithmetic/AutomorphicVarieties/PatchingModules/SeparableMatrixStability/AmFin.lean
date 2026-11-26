module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem quot_equiv (K : Type) [Field K] (m : ℕ) :
    Nonempty ((PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) ≃ (Fin m → K)) := by
  let f : PowerSeries K →+ (Fin m → K) :=
    { toFun := fun p i => PowerSeries.coeff (i : ℕ) p
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hs : Function.Surjective f := by
    intro v
    refine ⟨PowerSeries.mk fun i => if h : i < m then v ⟨i, h⟩ else 0, ?_⟩
    ext i
    simp [f]
  have hk : (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}).toAddSubgroup = f.ker := by
    ext p
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, AddMonoidHom.mem_ker]
    constructor
    · intro h; ext i; exact h i i.2
    · intro h i hi; exact congrFun h ⟨i, hi⟩
  exact ⟨((QuotientAddGroup.quotientAddEquivOfEq hk).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hs)).toEquiv⟩

private theorem l_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] (φ : ℤ_[l] →+* K) : (l : K) = 0 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  by_cases hpl : p = l
  · subst hpl
    exact CharP.cast_eq_zero K p
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      have h1 : ¬ ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hd
        have e := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).1 (Int.natCast_dvd_natCast.1 hd)
        exact hpl e.symm
      push_neg at h1
      simpa using h1
    have hu' := hu.map φ
    rw [map_natCast, CharP.cast_eq_zero K p] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.am_fin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ IsNilpotent (algebraMap x.A (x.Am m) x.t) ∧ IsNilpotent (algebraMap x.A (DD (x.Am m) g) x.t) ∧ (l : x.A) = 0 ∧ 1 < Nat.card x.K := by
  intro l _ F n x m g
  obtain ⟨e⟩ := quot_equiv x.K m
  have hn : IsNilpotent (algebraMap x.A (x.Am m) x.t) := ⟨m, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  refine ⟨Finite.of_equiv _ e.symm, ?_, hn, hn.map (DD.C : x.Am m →+* DD (x.Am m) g), ?_, Finite.one_lt_card⟩
  · rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  · have h := l_zero l x.K (algebraMap ℤ_[l] x.K)
    rw [← map_natCast (PowerSeries.C (R := x.K)), h, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Cont

variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a + g a := fun N => by
  simpa only [map_add (f := _)] using (hf N).comp₂ (hg N) (· + ·)

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun a => f a * g a := fun N => by
  simpa only [map_mul] using (hf N).comp₂ (hg N) (· * ·)

private theorem ac_sum {ι : Type} (s : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (0 : R)
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using ac_add (hf i) ih

private theorem ac_map {S : Type} [CommRing S] (φ : R →+* S) {t : R} {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    AdicCont (Ideal.span {φ t}) fun a => φ (f a) := fun N => by
  have hle : Ideal.span {t} ^ N ≤ (Ideal.span {φ t} ^ N).comap φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_nil {t : R} (ht : IsNilpotent t) {f : Γ → R} (hf : AdicCont (Ideal.span {t}) f) :
    IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  refine IsLocallyConstant.desc _ (Ideal.Quotient.mk (Ideal.span {t} ^ N)) (hf N) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN]
  simp

private theorem lc_mat {n : ℕ} {f : Γ → Matrix (Fin n) (Fin n) R} (hf : ∀ i j, IsLocallyConstant fun a => f a i j) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have : ∀ᶠ b in nhds a, ∀ i j, f b i j = f a i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq a
  exact this.mono fun b hb => Matrix.ext hb

end Cont

private theorem epM_entry {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (Z : Fin g → Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (DD.epM fun j => (Z j).map (algebraMap A X)) a b =
      ∑ j, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b) := by
  have e : ∀ c : A, algebraMap A (DD X g) c = DD.C (algebraMap A X c) := fun _ => rfl
  have s : ∀ (s : Finset (Fin g)), (∑ j ∈ s, (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) * algebraMap A (DD X g) (Z j a b)) =
      ⟨0, fun i => if i ∈ s then algebraMap A X (Z i a b) else 0, 0, 0⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext <;> simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ih, e]
      ext j
      · simp
      · by_cases h : j = i
        · subst h; simp [hi]
        · simp [h]
      · simp
      · simp
  rw [s]
  simp [DD.epM]

private theorem ρX_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (i j : Fin n) : AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j := by
  have h := x.cont i j
  rw [PowerSeries.maximalIdeal_eq_span_X] at h
  exact ac_map (algebraMap x.A X) h

theorem UpperTheory.V.Pa.rho_hom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], (x.ρX X 1 = 1 ∧ (∀ g h, x.ρX X (g * h) = x.ρX X g * x.ρX X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A X x.t}) fun g => x.ρX X g i j) ∧ (k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j) ∧ (IsNilpotent (algebraMap x.A X x.t) → IsLocallyConstant (x.ρX X) ∧ IsLocallyConstant (k.ρ1 X)) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ x.wX X v * x.wiX X v = 1 := by
  intro l _ F n x k X _ _
  obtain ⟨h1, h2, -, h4⟩ := Det.rho1Hom k X
  have c1 : ∀ i j, AdicCont (Ideal.span {algebraMap x.A (DD X k.g) x.t}) fun g => k.ρ1 X g i j := by
    intro i j
    simp only [Kap.ρ1, Matrix.mul_apply, Matrix.add_apply, epM_entry]
    refine ac_sum _ fun c => ac_mul (ac_add (ac_const _) (ac_sum _ fun a => ac_mul (ac_const _) ?_)) (ρX_cont x _ c j)
    exact ac_map (algebraMap x.A (DD X k.g)) ((k.mem a).2.1 i c)
  refine ⟨⟨by simp [NP.ρX, mat], fun g h => by simp [NP.ρX, mat, Matrix.map_mul], ρX_cont x X⟩, ⟨h1, h2, c1⟩,
    fun ht => ⟨lc_mat fun i j => ac_nil ht (ρX_cont x X i j), lc_mat fun i j => ac_nil ?_ (c1 i j)⟩,
    fun v => ⟨(h4 v).1, ?_⟩⟩
  · exact ht.map (DD.C : X →+* DD X k.g)
  · rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_comm {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+ B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.map φ y) =
      MonoidAlgebra.map φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply]
  apply MonoidAlgebra.coeff_injective
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ)

private theorem md_comm' {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+* B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.mapRingHom G φ y) =
      MonoidAlgebra.mapRingHom G' φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  exact md_comm f φ.toAddMonoidHom y

private theorem md_surj (A : Type) {G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : Function.Surjective (MonoidAlgebra.mapDomainRingHom A f) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff, hx]

private theorem comap_chi {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    (y : MonoidAlgebra A G) : (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y) := by
  show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom _ f
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C y)) = _
  rw [map_sub, md_comm', MonoidAlgebra.mapDomainRingHom_apply (Polynomial A) f (MonoidAlgebra.single 1 Polynomial.X),
    MonoidAlgebra.mapDomain_single, map_one]
  rfl

private theorem md_gen {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom _ f (GDet.gen y) = GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j) := by
  unfold GDet.gen
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul,
    ← MonoidAlgebra.mapDomainRingHom_apply, md_comm']

private theorem mem_CH {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (z : MonoidAlgebra A G) :
    z ∈ D.CH ↔ ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ),
      z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) (Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))) := by
  simp only [GDet.CH, Set.mem_setOf_eq]
  refine exists_congr fun m => exists_congr fun y => exists_congr fun β => ?_
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    ext g
    rw [h g, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl
  · intro h g
    rw [h, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl

private theorem md_CH {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    {m : ℕ} (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen y)
        (((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y)))) =
    MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j))
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
          (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)))) := by
  rw [md_comm]
  congr 1
  have hc : ((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y) =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
        (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) := by
    rw [← md_gen]
    exact comap_chi f (D.map MvPolynomial.C) (GDet.gen y)
  rw [hc, ← md_gen]
  exact (Polynomial.aeval_algHom_apply
    (MonoidAlgebra.mapDomainAlgHom (R := MvPolynomial (Fin m) A) (A := MvPolynomial (Fin m) A) f) _ _).symm

theorem UpperTheory.V.Pa.comap_lam :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G'), (∀ y, (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ i y, (D.comap f).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ y, (D.comap f).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ (B : Type) [CommRing B] (φ : A →+* B), (D.comap f).map φ = (D.map φ).comap f) ∧ (∀ ρ : G' →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).comap f = GDet.ofRep (ρ.comp f)) ∧ (Function.Surjective f → (∀ D' : GDet n A G', D'.comap f = D.comap f → D' = D) ∧ MonoidAlgebra.mapDomainRingHom A f '' (D.comap f).CH = D.CH) := by
  intro n A G G' _ _ _ f D
  refine ⟨comap_chi f D, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    simp only [GDet.lam, comap_chi]
  · intro y
    simp only [GDet.tr, GDet.lam, comap_chi]
  · intro B _ φ
    apply GDet.ext
    intro C _ _ x
    rfl
  · intro ρ
    apply GDet.ext
    intro B _ _ x
    have key : ((GDet.repAlg ρ B).comp (MonoidAlgebra.mapDomainAlgHom (R := B) (A := B) f)) =
        GDet.repAlg (ρ.comp f) B := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, MonoidAlgebra.mapDomainAlgHom]
      · exact Subsingleton.elim _ _
    show Matrix.det (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B f x)) =
      Matrix.det (GDet.repAlg (ρ.comp f) B x)
    rw [← key]
    rfl
  · intro hf
    constructor
    · intro D' h
      apply GDet.ext
      intro B _ _ x
      obtain ⟨x', rfl⟩ := md_surj B f hf x
      exact congrArg (fun E : GDet n A G => E.D B x') h
    · ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨m, y, β, rfl⟩ := (mem_CH _ _).1 hw
        exact (mem_CH _ _).2 ⟨m, _, β, md_CH f D y β⟩
      · intro hz
        obtain ⟨m, y', β, rfl⟩ := (mem_CH _ _).1 hz
        choose y hy using fun j => md_surj A f hf (y' j)
        have hy' : (fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) = y' := funext hy
        refine ⟨_, (mem_CH _ _).2 ⟨m, y, β, rfl⟩, ?_⟩
        rw [md_CH, hy']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomlDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homl_desc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ'), Continuous f → Function.Surjective f → Finite (HomL l (H.comap f)) → Finite (HomL l H) ∧ Nat.card (HomL l H) ≤ Nat.card (HomL l (H.comap f)) := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H hf hsurj hfin
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  let Φ : HomL l H → HomL l (H.comap f) := fun φ =>
    ⟨φ.1.comp g, by
      show IsOpen (g ⁻¹' (φ.1.ker : Set H))
      exact φ.2.preimage hg⟩
  have hinj : Function.Injective Φ := by
    intro φ ψ h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hgs y
    have := congrArg (fun χ : HomL l (H.comap f) => χ.1 x) h
    simpa [Φ] using this
  have hF : Finite (HomL l H) := Finite.of_injective Φ hinj
  exact ⟨hF, Nat.card_le_card_of_injective Φ hinj⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.GdetDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem gdesc_ker {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) (J : TwoSidedIdeal (MonoidAlgebra A G))
    (hJ : ∀ k, f k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J) (x : MonoidAlgebra A G)
    (hx : MonoidAlgebra.mapDomainAlgHom A A f x = 0) : x ∈ J := by
  have key : ∀ y : MonoidAlgebra A G,
      y - MonoidAlgebra.mapDomain (Function.surjInv hf) (MonoidAlgebra.mapDomainAlgHom A A f y) ∈ J := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g a =>
      have h1 := J.mul_mem_left (MonoidAlgebra.single (Function.surjInv hf (f g)) a) _
        (hJ ((Function.surjInv hf (f g))⁻¹ * g) (by simp [Function.surjInv_eq]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_inv_cancel_left, mul_one, mul_one] at h1
      simpa using h1
  simpa [hx] using key x

private theorem gdesc_toT {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G) :
    toT A G' B (MonoidAlgebra.mapDomainRingHom B f x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (MonoidAlgebra.mapDomainAlgHom A A f) (toT A G B x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp [toT_single]

theorem UpperTheory.V.Pa.gdet_desc :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G), Function.Surjective f → (∀ k, f k = 1 → D.Kills (MonoidAlgebra.single k 1 - 1)) → ∃ D' : GDet n A G', D'.comap f = D := by
  intro n A G G' _ _ _ f D hf hk
  have hs : Function.Surjective (MonoidAlgebra.mapDomainAlgHom A A f) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | single g a =>
      obtain ⟨g, rfl⟩ := hf g
      exact ⟨MonoidAlgebra.single g a, by simp⟩
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D.toDet (MonoidAlgebra.mapDomainAlgHom A A f) hs
    (gdesc_ker f hf _ fun k h => (UpperTheory.V.CA.d_ker _ _).1.2 ((UpperTheory.V.CA.d_toDet D _).2.2.2.2 (hk k h)))
  refine ⟨GDet.ofDet D', ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  exact GDet.ext fun B _ _ x => congrArg (D'.D B) (gdesc_toT f B x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocFin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.coc_fin :
    ∀ (G R : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommRing R] [Finite R] (n : ℕ) (ρ : G → Matrix (Fin n) (Fin n) R), TopFG G → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → IsLocallyConstant ρ → {z : G → Matrix (Fin n) (Fin n) R | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹}.Finite := by
  intro G R _ _ _ _ _ n ρ hfg h1 hmul hρ
  obtain ⟨s, hs, hden⟩ := hfg
  haveI : Finite s := hs.to_subtype
  have hinv : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hinv' : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hz1 : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → z 1 = 0 := by
    intro z hz
    have := hz 1 1
    simpa [h1] using this
  have hzinv : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) →
      ∀ g, z g⁻¹ = ρ g⁻¹ * (-z g) * ρ g := by
    intro z hz g
    have e := hz g g⁻¹
    rw [mul_inv_cancel, hz1 z hz] at e
    have e2 : ρ g * z g⁻¹ * ρ g⁻¹ = -z g := eq_neg_of_add_eq_zero_right e.symm
    calc z g⁻¹ = ρ g⁻¹ * (ρ g * z g⁻¹ * ρ g⁻¹) * ρ g := by
          simp only [Matrix.mul_assoc]
          rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = ρ g⁻¹ * (-z g) * ρ g := by rw [e2]
  apply Set.Finite.of_finite_image (f := fun z : G → Matrix (Fin n) (Fin n) R => fun x : s => z x)
    (Set.toFinite _)
  rintro z ⟨hzl, hz⟩ z' ⟨hzl', hz'⟩ he
  let H : Subgroup G :=
    { carrier := {g | z g = z' g}
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = z' (a * b)
        change z a = z' a at ha
        change z b = z' b at hb
        rw [hz, hz', ha, hb]
      one_mem' := by
        change z 1 = z' 1
        rw [hz1 z hz, hz1 z' hz']
      inv_mem' := fun {a} ha => by
        change z a = z' a at ha
        change z a⁻¹ = z' a⁻¹
        rw [hzinv z hz, hzinv z' hz', ha] }
  have hsH : Subgroup.closure s ≤ H := (Subgroup.closure_le H).2 fun x hx => congrFun he ⟨x, hx⟩
  have hcl : IsClosed (H : Set G) := by
    have hd := hzl.comp₂ hzl' (fun a b => a - b)
    have hc := hd.isClosed_fiber 0
    convert hc using 1
    ext g
    exact sub_eq_zero.symm
  have hU : (H : Set G) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hden.closure_eq]
    exact closure_minimal (fun x hx => hsH hx) hcl
  funext g
  have hg : g ∈ (H : Set G) := hU ▸ Set.mem_univ g
  exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelMap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A R R' : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') {n : ℕ}

private theorem adic_map {G : Type} [TopologicalSpace G] (t : A) (u : G → R)
    (hu : AdicCont (Ideal.span {algebraMap A R t}) u) :
    AdicCont (Ideal.span {algebraMap A R' t}) fun g => f (u g) := by
  intro N
  have hmap : Ideal.map f ((Ideal.span {algebraMap A R t}) ^ N) =
      (Ideal.span {algebraMap A R' t}) ^ N := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, AlgHom.commutes]
  have hle : (Ideal.span {algebraMap A R t}) ^ N ≤
      ((Ideal.span {algebraMap A R' t}) ^ N).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hmap.le
  have e : (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g))) =
      (Ideal.quotientMap _ (f : R →+* R') hle) ∘
        (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R t}) ^ N) (u g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  change IsLocallyConstant (fun g => Ideal.Quotient.mk ((Ideal.span {algebraMap A R' t}) ^ N) (f (u g)))
  rw [e]
  exact (hu N).comp _

private theorem mm_mul (M N : Matrix (Fin n) (Fin n) R) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem mm_add (M N : Matrix (Fin n) (Fin n) R) : (M + N).map f = M.map f + N.map f :=
  map_add f.mapMatrix M N

private theorem mm_sub (M N : Matrix (Fin n) (Fin n) R) : (M - N).map f = M.map f - N.map f :=
  map_sub f.mapMatrix M N

private theorem mm_neg (M : Matrix (Fin n) (Fin n) R) : (-M).map f = -M.map f :=
  map_neg f.mapMatrix M

private theorem dY_map {l : ℕ} [Fact l.Prime] (F : GFrame l) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    (dY F ρ Y g).map f = dY F (fun g => (ρ g).map f) (Y.map f) g := by
  unfold dY
  rw [mm_sub, mm_mul, mm_mul]

end

theorem UpperTheory.V.Pa.sel_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R R' : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R'] [Algebra A R'] (f : R →ₐ[A] R') (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R')), (∀ Z ∈ V, Z.map f ∈ V') → ∀ z, (z ∈ SelZ F t ρ w wi V → (fun g => (z g).map f) ∈ SelZ F t (fun g => (ρ g).map f) (fun v => (w v).map f) (fun v => (wi v).map f) V') ∧ (z ∈ Bd F ρ V → (fun g => (z g).map f) ∈ Bd F (fun g => (ρ g).map f) V') := by
  intro l _ F n A R R' _ _ _ _ _ f t ρ w wi V V' hV z
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hV _ (h1 g), fun i j => ?_, fun g k => ?_, fun g => ?_, fun u g hg => ?_,
      fun v => ?_⟩
    · exact adic_map f t (fun g => z g i j) (h2 i j)
    · beta_reduce
      rw [h3, mm_add, mm_mul, mm_mul]
    · beta_reduce
      rw [h4, mm_neg, Matrix.transpose_map]
    · beta_reduce
      rw [h5 u g hg]
      exact Matrix.map_zero _ (map_zero f)
    · obtain ⟨Y, hY, hloc⟩ := h6 v
      refine ⟨Y.map f, hV _ hY, fun g => ?_⟩
      have key : (wi v).map f * ((z ((F.φ v) g)).map f -
            dY F (fun g => (ρ g).map f) (Y.map f) ((F.φ v) g)) * (w v).map f =
          (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v).map f := by
        rw [mm_mul, mm_mul, mm_sub, dY_map]
      obtain ⟨hl1, hl2⟩ := hloc g
      refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
      · beta_reduce
        rw [key, Matrix.map_apply, hl1 i j hij, map_zero]
      · beta_reduce
        rw [key, Matrix.map_apply, hl2 hg i, map_zero]
  · rintro ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map f, hV _ hY, ?_, ?_⟩
    · rw [← Matrix.transpose_map, hT, mm_neg]
    · funext g
      exact dY_map f F ρ Y g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelLin
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem adic_lin {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) (c : R) {f f' : G → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => c * f g + f' g := by
  intro N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) (c * f g + f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) c * Ideal.Quotient.mk (I ^ N) (f g) + Ideal.Quotient.mk (I ^ N) (f' g) := by
    funext g
    simp only [map_add (f := _), map_mul]
  rw [e]
  exact ((IsLocallyConstant.const _).mul (h N)).add (h' N)

private theorem adic_zero {G R : Type} [TopologicalSpace G] [CommRing R] (I : Ideal R) :
    AdicCont I fun _ : G => (0 : R) := fun _ => IsLocallyConstant.const _

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)

private theorem dY_lin (c : A) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y + Y') g = c • dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

private theorem dY_zero (g : F.G₀) : dY F ρ 0 g = 0 := by simp [dY]

private theorem locAt_lin (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (c : A) {z z' : F.G₀ → Matrix (Fin n) (Fin n) R}
    {v : F.Vl} {Y Y' : Matrix (Fin n) (Fin n) R} (h : LocAt F ρ w wi z v Y) (h' : LocAt F ρ w wi z' v Y') :
    LocAt F ρ w wi (c • z + z') v (c • Y + Y') := by
  intro g
  obtain ⟨h1, h2⟩ := h g
  obtain ⟨h1', h2'⟩ := h' g
  have key : wi v * ((c • z + z') ((F.φ v) g) - dY F ρ (c • Y + Y') ((F.φ v) g)) * w v =
      c • (wi v * (z ((F.φ v) g) - dY F ρ Y ((F.φ v) g)) * w v) +
        wi v * (z' ((F.φ v) g) - dY F ρ Y' ((F.φ v) g)) * w v := by
    rw [dY_lin]
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h1 i j hij, h1' i j hij, smul_zero, add_zero]
  · rw [key, Matrix.add_apply, Matrix.smul_apply, h2 hg i, h2' hg i, smul_zero, add_zero]

end

private theorem sub_of_lin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (s : Set M) (h0 : (0 : M) ∈ s)
    (h : ∀ (c : A) x y, x ∈ s → y ∈ s → c • x + y ∈ s) : ∃ S : Submodule A M, (S : Set M) = s := by
  refine ⟨{ carrier := s, add_mem' := ?_, zero_mem' := h0, smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    have := h 1 x y hx hy
    rwa [one_smul] at this
  · intro c x hx
    have := h c x 0 hx h0
    rwa [add_zero] at this

theorem UpperTheory.V.Pa.sel_lin :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  intro l _ F n A R _ _ _ t ρ w wi V
  constructor
  · apply sub_of_lin
    · refine ⟨fun _ => V.zero_mem, fun i j => ?_, fun g h => by simp, fun g => by simp, fun u g _ => rfl,
        fun v => ⟨0, V.zero_mem, fun g => ?_⟩⟩
      · exact adic_zero _
      · simp [dY_zero]
    · intro c x y hx hy
      obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
      obtain ⟨y1, y2, y3, y4, y5, y6⟩ := hy
      refine ⟨fun g => V.add_mem (V.smul_mem c (x1 g)) (y1 g), fun i j => ?_, fun g h => ?_, fun g => ?_,
        fun u g hg => ?_, fun v => ?_⟩
      · have e : (fun g => (c • x + y) g i j) = fun g => algebraMap A R c * x g i j + y g i j := by
          funext g
          rw [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, Algebra.smul_def]
        rw [e]
        exact adic_lin _ _ (x2 i j) (y2 i j)
      · simp only [Pi.add_apply, Pi.smul_apply, x3 g h, y3 g h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, smul_add]
        abel
      · simp only [Pi.add_apply, Pi.smul_apply, x4 g, y4 g, Matrix.transpose_add, Matrix.transpose_smul,
          Matrix.transpose_neg, smul_neg]
        abel
      · simp [x5 u g hg, y5 u g hg]
      · obtain ⟨Y, hY, hYl⟩ := x6 v
        obtain ⟨Y', hY', hYl'⟩ := y6 v
        exact ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', locAt_lin F ρ w wi c hYl hYl'⟩
  · apply sub_of_lin
    · exact ⟨0, V.zero_mem, by simp, funext fun g => (dY_zero F ρ g).symm⟩
    · rintro c x y ⟨Y, hY, hYt, rfl⟩ ⟨Y', hY', hYt', rfl⟩
      refine ⟨c • Y + Y', V.add_mem (V.smul_mem c hY) hY', ?_, ?_⟩
      · rw [Matrix.transpose_add, Matrix.transpose_smul, hYt, hYt', smul_neg, neg_add]
      · funext g
        rw [dY_lin]
        rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlMap
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResMap
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff {l : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

theorem UpperTheory.V.AlgebraTools.proLRes_map :
    ∀ (l : ℕ) [Fact l.Prime] (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (f : G →* H), Continuous f → Function.Surjective f →
      (proLRes l G).map f = proLRes l H := by
  intro l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, mem_proLRes]
    intro N hN
    rw [pq_iff] at hN
    let M : OpenNormalSubgroup G :=
      { toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup
        isNormal' := Subgroup.Normal.comap inferInstance f }
    haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'
    have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro x
      obtain ⟨k, hk⟩ := hN (f x)
      refine ⟨k, ?_⟩
      show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup
      rw [OpenSubgroup.mem_comap, map_pow]
      exact hk
    have := (mem_proLRes.mp hg) M hM
    exact (OpenSubgroup.mem_comap (hf := hf)).mp this
  · intro h hh
    rw [mem_proLRes] at hh
    let t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G :=
      fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)
    let T0 : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }
    haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'
    have htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro g
      refine ⟨0, ?_⟩
      show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)
      simp
    haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩
    have hcl : ∀ i, IsClosed (t i) := fun i =>
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
      intro i j
      have hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G)) := by
        rw [pq_iff]
        intro g
        obtain ⟨a, ha⟩ := (pq_iff _).mp i.2 g
        obtain ⟨b, hb⟩ := (pq_iff _).mp j.2 g
        refine ⟨a + b, ?_⟩
        have e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b := by rw [pow_add, pow_mul]
        have e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a := by rw [add_comm, pow_add, pow_mul]
        have m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G) := e1 ▸ pow_mem ha _
        have m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G) := e2 ▸ pow_mem hb _
        show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)
        exact OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩
      refine ⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩
    have hnon : ∀ i, (t i).Nonempty := by
      intro i
      have hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G) := i.1.toOpenSubgroup.isClosed
      have hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H) := by
        rw [Subgroup.coe_map]
        exact hf.isClosedMap _ hNcl
      haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by
        rw [Subgroup.finiteIndex_iff]
        intro h0
        have hd := Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs
        rw [h0, zero_dvd_iff] at hd
        exact (Subgroup.finiteIndex_iff.mp inferInstance) hd
      let M : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f,
            Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩
          isNormal' := Subgroup.Normal.map inferInstance f hs }
      haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'
      have hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H)) := by
        rw [pq_iff]
        intro y
        obtain ⟨x, rfl⟩ := hs y
        obtain ⟨k, hk⟩ := (pq_iff _).mp i.2 x
        refine ⟨k, ?_⟩
        show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f
        exact ⟨x ^ l ^ k, hk, map_pow f x _⟩
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp (hh M hM)
      exact ⟨x, hfx, hx⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
      (fun i => (hcl i).isCompact) hcl
    rw [Set.mem_iInter] at hg
    refine ⟨g, ?_, (hg (Classical.arbitrary _)).1⟩
    rw [SetLike.mem_coe, mem_proLRes]
    intro N hN
    exact (hg ⟨N, hN⟩).2
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal],
      IsOpen (H : Set Γ') → Continuous f → Function.Surjective f →
        (PL (l := l) (H.comap f)).map f = PL (l := l) H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ _ hf hsurj
  have hmem {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {x : G} :
      x ∈ PL (l := l) K ↔
        ∀ U : OpenNormalSubgroup G, (∀ h ∈ K, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U := by
    simp only [PL, Subgroup.mem_iInf]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine hmem.mpr fun V hV => ?_
    let U : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap f hf
        isNormal' := Subgroup.Normal.comap V.isNormal' f }
    apply hmem.mp hx U
    intro h hh
    obtain ⟨e, he⟩ := hV (f h) hh
    refine ⟨e, ?_⟩
    change f (h ^ l ^ e) ∈ V
    rwa [map_pow]
  · intro y hy
    let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ U}
    let top : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := ⊤
        isNormal' := Subgroup.normal_top }
    have htop : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ top := by
      intro h _
      exact ⟨0, Subgroup.mem_top _⟩
    have : Nonempty ι := ⟨⟨top, htop⟩⟩
    let t (i : ι) : Set Γ := f ⁻¹' {y} ∩ (i.1 : Set Γ)
    have hclosed (i : ι) : IsClosed (t i) :=
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (· ⊇ ·) t := by
      intro i j
      have hpow : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ i.1 ⊓ j.1 := by
        intro h hh
        obtain ⟨a, ha⟩ := i.2 h hh
        obtain ⟨b, hb⟩ := j.2 h hh
        refine ⟨a + b, ⟨?_, ?_⟩⟩
        · rw [pow_add, pow_mul]
          exact pow_mem ha _
        · rw [add_comm, pow_add, pow_mul]
          exact pow_mem hb _
      exact ⟨⟨i.1 ⊓ j.1, hpow⟩, fun _ hx => ⟨hx.1, hx.2.1⟩, fun _ hx => ⟨hx.1, hx.2.2⟩⟩
    have hnonempty (i : ι) : (t i).Nonempty := by
      let V : OpenNormalSubgroup Γ' :=
        { toSubgroup := i.1.toSubgroup.map f
          isOpen' := f.isOpenMap_of_sigmaCompact hsurj hf _ i.1.toOpenSubgroup.isOpen
          isNormal' := Subgroup.Normal.map i.1.isNormal' f hsurj }
      have hyV : y ∈ V := by
        refine hmem.mp hy V fun h hh => ?_
        obtain ⟨x, rfl⟩ := hsurj h
        obtain ⟨e, he⟩ := i.2 x hh
        exact ⟨e, ⟨x ^ l ^ e, he, map_pow f x _⟩⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyV
      exact ⟨x, hxy, hx⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
      hnonempty (fun i => (hclosed i).isCompact) hclosed
    rw [Set.mem_iInter] at hx
    exact ⟨x, hmem.mpr fun U hU => (hx ⟨U, hU⟩).2, (hx ⟨top, htop⟩).1⟩
end
