module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteProjectiveModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIso
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Transfer

theorem coneExact_baseChange_of_quasiIso {R R' : Type} [CommRing R] [CommRing R'] [inst : Algebra R R']
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    GlobalTheory.ConeExact (K := fun p => R' ⊗[R] K.X p) (C := fun p => R' ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.baseChange R') (fun p => (C.d p (p + 1)).hom.baseChange R')
      (fun p => (φ.f p).hom.baseChange R') := by
  have key := (GlobalTheory.quasiIso_iff_coneExact _).1 h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

variable {R : Type} [CommRing R] {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C)
  (R' : Type) [CommRing R'] [Algebra R R']

theorem dB_comm (i j : ℕ) (x : R' ⊗[R] K.X i) :
    dB C R' i j ((φ.f i).hom.baseChange R' x) = (φ.f j).hom.baseChange R' (dB K R' i j x) := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, φ.comm]

theorem dB_dB (L : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ) (x : R' ⊗[R] L.X i) :
    dB L R' j k (dB L R' i j x) = 0 := by
  simp only [dB, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, L.d_comp_d,
    ModuleCat.hom_zero, LinearMap.baseChange_zero, LinearMap.zero_apply]

def cycMap (i j : ℕ) : LinearMap.ker (dB K R' i j) →ₗ[R'] LinearMap.ker (dB C R' i j) :=
  ((φ.f i).hom.baseChange R').restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [dB_comm, hx, map_zero])

theorem cycMap_val (i j : ℕ) (z : LinearMap.ker (dB K R' i j)) :
    (cycMap φ R' i j z).1 = (φ.f i).hom.baseChange R' z.1 := rfl

theorem ext_comm {R'' : Type} [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) (y : R' ⊗[R] K.X i) :
    (φ.f i).hom.baseChange R'' (ext α _ y) = ext α _ ((φ.f i).hom.baseChange R' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [ext]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_comp {H : Type} [AddCommGroup H] [Module R' H] (i j k : ℕ)
    (θ : LinearMap.ker (dB C R' j k) →ₗ[R'] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (dB C R' i j))
    (surj : ∀ c, dB C R' j k c = 0 → ∃ (c' : R' ⊗[R] C.X i) (k' : R' ⊗[R] K.X j),
      dB K R' j k k' = 0 ∧ dB C R' i j c' + (φ.f j).hom.baseChange R' k' = c)
    (inj : ∀ (k' : R' ⊗[R] K.X j) (c : R' ⊗[R] C.X i), dB K R' j k k' = 0 →
      (φ.f j).hom.baseChange R' k' = dB C R' i j c → k' ∈ LinearMap.range (dB K R' i j)) :
    Function.Surjective (θ.comp (cycMap φ R' j k)) ∧
      ∀ z, θ.comp (cycMap φ R' j k) z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' i j) := by
  refine ⟨fun x => ?_, fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs x
    obtain ⟨c', k', hk', hsum⟩ := surj z.1 z.2
    have hm : dB C R' i j c' ∈ LinearMap.ker (dB C R' j k) := dB_dB R' C i j k c'
    have hz : z = cycMap φ R' j k ⟨k', hk'⟩ + ⟨_, hm⟩ := Subtype.ext (by
      rw [Submodule.coe_add, cycMap_val, ← hsum, add_comm])
    refine ⟨⟨k', hk'⟩, ?_⟩
    rw [LinearMap.comp_apply, hz, map_add (f := _), (hk ⟨_, hm⟩).2 ⟨c', rfl⟩, add_zero]
  · rw [LinearMap.comp_apply, hk, cycMap_val]
    constructor
    · rintro ⟨c, hc⟩
      exact inj z.1 c z.2 hc.symm
    · rintro ⟨b, hb⟩
      exact ⟨(φ.f i).hom.baseChange R' b, by rw [dB_comm, hb]⟩

end Transfer

theorem nonempty_model_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) →
    Model s C → Nonempty (Model s K) := by
  intro R _ X s K C φ hq M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    show IsPullback (𝟙 X) s s (spMap (RingHom.id R))
    rw [Cris.spMap_id]; exact IsPullback.id_horiz s
  obtain ⟨e1, -⟩ := M.θ0_one h0
  obtain ⟨y, hy1, hy2⟩ := (coneExact_baseChange_of_quasiIso φ (hq R)).zero ((1 : R) ⊗ₜ[R] M.one) 0
    ((LinearMap.mem_ker.1 e1).trans (map_zero _).symm) (map_zero _)
  let oneK : K.X 0 := TensorProduct.lid R (K.X 0) y
  have hy : (1 : R) ⊗ₜ[R] oneK = y := by
    rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
  have hinj : ∀ {M : ModuleCat.{0} R} (a b : M), (1 : R) ⊗ₜ[R] a = (1 : R) ⊗ₜ[R] b → a = b := fun a b hab => by
    rw [← TensorProduct.lid_symm_apply, ← TensorProduct.lid_symm_apply] at hab
    exact (TensorProduct.lid R _).symm.injective hab
  have hφone : (φ.f 0).hom oneK = M.one := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy]; exact hy1)
  have hdone : (K.d 0 1).hom oneK = 0 := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy, TensorProduct.tmul_zero]; exact hy2)
  refine ⟨{
    θ0 := fun {R'} _ _ {X'} {s'} {ψ} h => (LinearEquiv.ofBijective (cycMap φ R' 0 1) ⟨?_, ?_⟩).trans (M.θ0 h)
    one := oneK
    θ0_one := ?_
    θ1 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ1 h).comp (cycMap φ R' 1 2)
    θ2 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ2 h).comp (cycMap φ R' 2 3)
    exact := ?_
    nat := ?_ }⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext ((coneExact_baseChange_of_quasiIso φ (hq _)).inj z.1 (congrArg Subtype.val hz) z.2)
  · intro w
    obtain ⟨x, hx1, hx2⟩ := (coneExact_baseChange_of_quasiIso φ (hq _)).zero w.1 0
      ((LinearMap.mem_ker.1 w.2).trans (map_zero _).symm) (map_zero _)
    exact ⟨⟨x, hx2⟩, Subtype.ext hx1⟩
  · intro R' _ _ X' s' ψ h
    have e : (1 : R') ⊗ₜ[R] oneK ∈ LinearMap.ker (dB K R' 0 1) := by
      rw [LinearMap.mem_ker, dB, LinearMap.baseChange_tmul, hdone, TensorProduct.tmul_zero]
    obtain ⟨e', he'⟩ := M.θ0_one h
    refine ⟨e, fun T => ?_⟩
    have hc : cycMap φ R' 0 1 ⟨_, e⟩ = ⟨_, e'⟩ := Subtype.ext (by
      rw [cycMap_val, LinearMap.baseChange_tmul, hφone])
    show (M.θ0 h (cycMap φ R' 0 1 ⟨_, e⟩)).1 T = 1
    rw [hc]; exact he' T
  · intro R' _ _ X' s' ψ h
    have hc := coneExact_baseChange_of_quasiIso φ (hq R')
    obtain ⟨s1, k1, s2, k2⟩ := M.exact h
    have A := exact_comp φ R' 0 1 2 (M.θ1 h) s1 k1
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 0 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨x, -, hx⟩ := hc.zero c k' hkc.symm hk'
        exact ⟨x, hx⟩)
    have B := exact_comp φ R' 1 2 3 (M.θ2 h) s2 k2
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 1 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨c', k'', -, hx⟩ := hc.succ 0 c k' hkc.symm hk'
        exact ⟨k'', hx⟩)
    exact ⟨A.1, A.2, B.1, B.2⟩
  · intro R' _ _ X' s' ψ h R'' _ _ X'' s'' ψ' h' α χ w hχ
    obtain ⟨n1, n2⟩ := M.nat h h' α χ w hχ
    refine ⟨fun z z' hz => ?_, fun z z' hz => ?_⟩
    · show M.θ1 h' (cycMap φ R'' 1 2 z') = pullHO1 w (M.θ1 h (cycMap φ R' 1 2 z))
      exact n1 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])
    · show M.θ2 h' (cycMap φ R'' 2 3 z') = pullHO2 w (M.θ2 h (cycMap φ R' 2 3 z))
      exact n2 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) → Model s C → Nonempty (Model s K) := by
  first | exact @GlobalTheory.AbCoh.nonempty_model_of_quasiIso | exact GlobalTheory.AbCoh.nonempty_model_of_quasiIso | (intros; apply GlobalTheory.AbCoh.nonempty_model_of_quasiIso <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_finite_projective_model : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧
      Nonempty (Model s K) := by
  intro R _ _ X s hP hF
  haveI := hP
  haveI := hF
  letI := algebraΓOfHom s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have := isAffineHom_diagonal_of_isSeparated s
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := GlobalTheory.isAffineOpen_finset_biInf hD
  have hM : (LB.triv X).IsLB := LB.isLB_triv X
  have := Twist.isFiniteQC_twist (F := structureModule X) hM
  obtain ⟨K, φ, h1, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (R := R) (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) m
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X s (LB.triv X) _ (by rw [Fintype.card_fin]; exact hp.le))
      (GlobalTheory.AbLaw.flat_cechLB_X s hM hD') (fun n => by
        obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_coh_equiv s hM hc hD' n
        have := GlobalTheory.ProperFinite.finite_coh_of_isProper s (twist (structureModule X) (LB.triv X)) n
        exact Module.Finite.equiv e.symm)
  have hsep : IsSeparated s := inferInstance
  have hDa : ∀ i, IsAffineOpen (D i) := fun i => hD i
  obtain ⟨MC⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin m) D hsep hDa hc
  exact ⟨K, fun p => ⟨h2 p, h4 p⟩, ⟨m, h1⟩, GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso R X s K _ φ (fun S _ _ => h7 S) MC⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomSplitBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SplitCx

variable {R : Type} [CommRing R]

theorem exists_quasiInv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (d : M →ₗ[R] N) (hQ : Module.Projective R (N ⧸ LinearMap.range d)) :
    ∃ b : N →ₗ[R] M, ∀ x, d (b (d x)) = d x := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y : N, y - t ((LinearMap.range d).mkQ y) ∈ LinearMap.range d := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun ht ((LinearMap.range d).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let r : N →ₗ[R] LinearMap.range d :=
    LinearMap.codRestrict _ (LinearMap.id - t ∘ₗ (LinearMap.range d).mkQ) hmem
  have hr : ∀ y : LinearMap.range d, r y = y := by
    intro y
    apply Subtype.ext
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 y.2, map_zero, sub_zero]
  haveI : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype r (LinearMap.ext hr)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict d)
  refine ⟨s ∘ₗ r, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hs (r (d x))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  have h2 := congrArg Subtype.val h1
  have h3 : (r (d x) : N) = d x := congrArg Subtype.val (hr ⟨d x, LinearMap.mem_range_self d x⟩)
  exact h2.trans h3

theorem exists_decomp {M0 M1 M2 : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [Module.Projective R M1] [Module.Projective R M2]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (h : ∀ x, d1 (d0 x) = 0)
    (hQ1 : Module.Projective R (M1 ⧸ LinearMap.range d0))
    (hQ2 : Module.Projective R (M2 ⧸ LinearMap.range d1)) :
    ∃ (e : M1 →ₗ[R] M1) (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1),
      e ∘ₗ e = e ∧ e ∘ₗ d0 = 0 ∧ d1 ∘ₗ e = 0 ∧ LinearMap.id = e + d0 ∘ₗ a + b ∘ₗ d1 := by
  obtain ⟨b, hb⟩ := exists_quasiInv d1 hQ2
  obtain ⟨b', hb'⟩ := exists_quasiInv d0 hQ1
  set a : M1 →ₗ[R] M0 := b' ∘ₗ (LinearMap.id - b ∘ₗ d1) with ha
  set e : M1 →ₗ[R] M1 := LinearMap.id - d0 ∘ₗ a - b ∘ₗ d1 with he0
  have he : ∀ y, e y = y - d0 (b' (y - b (d1 y))) - b (d1 y) := fun y => by
    simp [e, a]
  have k1 : ∀ x, d1 (e x) = 0 := fun x => by
    rw [he]; simp only [map_sub, h, hb]; abel
  have k2 : ∀ x, d0 (b' (e x)) = 0 := fun x => by
    rw [he]; simp only [map_sub, hb']; abel
  refine ⟨e, a, b, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply]
    simp only [he (e x), k1, map_zero, sub_zero, k2]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    simp only [he, h, map_zero, sub_zero, hb', sub_self]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, k1]
  · ext x
    simp only [e, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

theorem bc {M0 M1 M2 P : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [AddCommGroup P] [Module R P]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (π : M1 →ₗ[R] P) (σ : P →ₗ[R] M1)
    (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1)
    (hπσ : π ∘ₗ σ = LinearMap.id) (hπd : π ∘ₗ d0 = 0) (hdσ : d1 ∘ₗ σ = 0)
    (hid : LinearMap.id = σ ∘ₗ π + d0 ∘ₗ a + b ∘ₗ d1) (S : Type) [CommRing S] [Algebra R S] :
    Function.Surjective (fun z : LinearMap.ker (d1.baseChange S) => π.baseChange S z.1) ∧
      ∀ z : LinearMap.ker (d1.baseChange S),
        π.baseChange S z.1 = 0 ↔ z.1 ∈ LinearMap.range (d0.baseChange S) := by
  have e1 : ∀ y, π.baseChange S (σ.baseChange S y) = y := fun y => by
    have := congrArg (LinearMap.baseChange S) hπσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at this
    exact LinearMap.congr_fun this y
  have e2 : ∀ y, π.baseChange S (d0.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hπd
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e3 : ∀ y, d1.baseChange S (σ.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hdσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e4 : ∀ y, y = σ.baseChange S (π.baseChange S y) + d0.baseChange S (a.baseChange S y)
      + b.baseChange S (d1.baseChange S y) := fun y => by
    have := congrArg (LinearMap.baseChange S) hid
    rw [LinearMap.baseChange_id, LinearMap.baseChange_add, LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact LinearMap.congr_fun this y
  refine ⟨fun y => ⟨⟨σ.baseChange S y, e3 y⟩, e1 y⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine ⟨a.baseChange S z.1, ?_⟩
    have h0 : d1.baseChange S z.1 = 0 := z.2
    have := e4 z.1
    rw [hz, h0, map_zero, map_zero, zero_add, add_zero] at this
    exact this.symm
  · rintro ⟨w, hw⟩
    rw [← hw]; exact e2 w

end GlobalTheory.AbCoh.SplitCx

namespace GlobalTheory.AbCoh

theorem cohom_split_baseChange : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z := by
  intro R _ K hK hQ i h1 h2 R' _ _
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  try simp only [Nat.add_sub_cancel, Nat.add_one_sub_one]
  haveI : Module.Projective R (K.X (j + 1)) := (hK _).2
  haveI : Module.Projective R (K.X (j + 1 + 1)) := (hK _).2
  haveI : Module.Finite R (K.X (j + 1)) := (hK _).1
  have hdd : ∀ x, (K.d (j + 1) (j + 1 + 1)).hom ((K.d j (j + 1)).hom x) = 0 := fun x => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]; rfl
  obtain ⟨e, a, b, hee, hed, hde, hid⟩ := SplitCx.exists_decomp (K.d j (j + 1)).hom
    (K.d (j + 1) (j + 1 + 1)).hom hdd (hQ j (by omega)) (hQ (j + 1) (by omega))
  let π : K.X (j + 1) →ₗ[R] LinearMap.range e := e.rangeRestrict
  let σ : LinearMap.range e →ₗ[R] K.X (j + 1) := (LinearMap.range e).subtype
  have hπσ : π ∘ₗ σ = LinearMap.id := by
    ext ⟨y, w, rfl⟩
    change e (e w) = e w
    rw [← LinearMap.comp_apply, hee]
  have hπd : π ∘ₗ (K.d j (j + 1)).hom = 0 := by
    ext x
    change e ((K.d j (j + 1)).hom x) = 0
    rw [← LinearMap.comp_apply, hed]; rfl
  have hdσ : (K.d (j + 1) (j + 1 + 1)).hom ∘ₗ σ = 0 := by
    ext ⟨y, w, rfl⟩
    change (K.d (j + 1) (j + 1 + 1)).hom (e w) = 0
    rw [← LinearMap.comp_apply, hde]; rfl
  have hid' : LinearMap.id = σ ∘ₗ π + (K.d j (j + 1)).hom ∘ₗ a + b ∘ₗ (K.d (j + 1) (j + 1 + 1)).hom := by
    rw [hid]; rfl
  haveI : Module.Projective R (LinearMap.range e) := Module.Projective.of_split σ π hπσ
  obtain ⟨sR, kR⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R
  obtain ⟨sR', kR'⟩ := SplitCx.bc _ _ π σ a b hπσ hπd hdσ hid' R'
  refine ⟨LinearMap.range e, inferInstance, inferInstance, inferInstance, inferInstance,
    (TensorProduct.lid R _).toLinearMap ∘ₗ (π.baseChange R ∘ₗ (LinearMap.ker _).subtype),
    π.baseChange R' ∘ₗ (LinearMap.ker _).subtype, ?_, sR', ?_, kR', ?_⟩
  · exact (TensorProduct.lid R _).surjective.comp sR
  · intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype,
      LinearEquiv.map_eq_zero_iff]
    exact kR z
  · intro z z' hz
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
    rw [hz]
    clear hz
    induction (z.1 : R ⊗[R] K.X (j + 1)) using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [ext, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Algebra.ofId_apply,
        LinearMap.baseChange_tmul, TensorProduct.lid_tmul]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, _root_.mul_one]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapAlgHomAlgebraMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbCoh.CohBaseChange

theorem exists_equiv_of_ker {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ z, f z = 0 ↔ g z = 0) : ∃ e : A ≃ₗ[S] B, ∀ z, e (f z) = g z := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext z; exact h z
  refine ⟨(f.quotKerEquivOfSurjective hf).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    g.quotKerEquivOfSurjective hg, fun z ↦ ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, this]
  rfl

variable {R : Type} [CommRing R]

theorem dB_ext (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R']
    [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'') (i j : ℕ) (y : R' ⊗[R] K.X i) :
    dB K R'' i j (ext α _ y) = ext α _ (dB K R' i j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem spMap_algHom_algebraMap {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α.comp_algebraMap]

theorem isPullback_self {X : Scheme.{0}} (s : X ⟶ Sp R) : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
  have : spMap (algebraMap R R) = 𝟙 (Sp R) := Spec.map_id _
  rw [this]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem liftsAt_of (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (i : ℕ) {H H₀ : Type} [AddCommGroup H] [Module R' H]
    [AddCommGroup H₀] [Module k H₀] (θ : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] H)
    (θ₀ : LinearMap.ker (dB K k i (i + 1)) →ₗ[k] H₀) (p : H → H₀) (hθ : Function.Surjective θ)
    (hθ₀ : ∀ z, θ₀ z = 0 ↔ z.1 ∈ LinearMap.range (dB K k (i - 1) i))
    (nat : ∀ z z', z'.1 = ext α _ z.1 → θ₀ z' = p (θ z)) (hp : Function.Surjective p) : LiftsAt K α i := by
  intro z hz
  obtain ⟨x, hx⟩ := hp (θ₀ ⟨z, hz⟩)
  obtain ⟨y, rfl⟩ := hθ x
  have hy' : ext α _ y.1 ∈ LinearMap.ker (dB K k i (i + 1)) := by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 y.2, map_zero]
  have h1 := nat y ⟨_, hy'⟩ rfl
  obtain ⟨b, hb⟩ := (hθ₀ (⟨z, hz⟩ - ⟨_, hy'⟩)).1 (by rw [map_sub, h1, hx, sub_self])
  refine ⟨y.1, b, y.2, ?_⟩
  rw [hb]
  simp

theorem bc_of {R' : Type} [CommRing R'] [Algebra R R'] {Z Z' P H H' : Type} [AddCommGroup Z] [Module R Z]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    [AddCommGroup H'] [Module R' H'] (u : Z →ₗ[R] P) (v : Z' →ₗ[R'] R' ⊗[R] P) (θ : Z →ₗ[R] H)
    (θ' : Z' →ₗ[R'] H') (p : H → H') (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ') (h : ∀ z, θ z = 0 ↔ u z = 0)
    (h' : ∀ z, v z = 0 ↔ θ' z = 0) (nat : ∀ z, ∃ z', v z' = 1 ⊗ₜ u z ∧ θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e, he⟩ := exists_equiv_of_ker θ u hθ hu h
  obtain ⟨e', he'⟩ := exists_equiv_of_ker v θ' hv hθ' h'
  refine ⟨e.baseChange R R' _ _ ≪≫ₗ e', fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hθ c
  obtain ⟨z', h1, h2⟩ := nat z
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he, ← h1, he', h2]

variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem liftsAt_zero (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by
  intro z hz
  have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
  have h₀ := IsPullback.of_hasPullback s (spMap (algebraMap R k))
  obtain ⟨e', -⟩ := M.θ0_one h'
  obtain ⟨e₀, he₀⟩ := M.θ0_one h₀
  obtain ⟨r, hr, -⟩ := hU k _ _ _ h₀ (M.θ0 h₀ ⟨z, hz⟩).1 (M.θ0 h₀ ⟨z, hz⟩).2
  have hz' : (⟨z, hz⟩ : LinearMap.ker (dB K k 0 1)) = r • ⟨_, e₀⟩ := by
    apply (M.θ0 h₀).injective
    rw [map_smul]
    refine Subtype.ext (funext fun T ↦ ?_)
    rw [hr T, Algebra.algebraMap_eq_smul_one, ← he₀ T]
    rfl
  obtain ⟨r', rfl⟩ := hα r
  refine ⟨r' • ((1 : R') ⊗ₜ[R] M.one), 0, ?_, ?_⟩
  · rw [map_smul]
    exact (congrArg (r' • ·) (LinearMap.mem_ker.1 e')).trans (smul_zero _)
  · have := congrArg Subtype.val hz'
    simp only [Submodule.coe_smul] at this
    rw [this, map_zero, add_zero, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp

theorem of_parts (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  intro R _ _ X s hp hf hU hl
  obtain ⟨K, hK, hb, ⟨M⟩⟩ := hex R X s hp hf
  have hproj := halg R K hK hb (by
    intro i hi R' _ _ _ _ k _ _ α hα
    have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
    have w := IsPullback.of_hasPullback (pullback.snd s (spMap (algebraMap R R'))) (spMap (α : R' →+* k))
    have h₀ := w.paste_horiz h'
    rw [spMap_algHom_algebraMap] at h₀
    obtain ⟨s1, s2⟩ := hl R' k α hα _ _ _ _ _ _ h' w
    obtain ⟨n1, n2⟩ := M.nat h' h₀ α _ w.w rfl
    obtain ⟨a1, -, a2, -⟩ := M.exact h'
    obtain ⟨-, b1, -, b2⟩ := M.exact h₀
    interval_cases i
    · exact liftsAt_zero M hU α hα
    · exact liftsAt_of K α 1 (M.θ1 h') (M.θ1 h₀) _ a1 b1 n1 s1
    · exact liftsAt_of K α 2 (M.θ2 h') (M.θ2 h₀) _ a2 b2 n2 s2)
  have hid := isPullback_self s
  obtain ⟨a1, b1, a2, b2⟩ := M.exact hid
  have hz : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ℕ) (z : LinearMap.ker (dB K R i (i + 1))),
      ext (Algebra.ofId R R') _ z.1 ∈ LinearMap.ker (dB K R' i (i + 1)) := fun R' _ _ i z ↦ by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 z.2, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ1 hid) hu a1 fun z ↦ (ku z).trans (b1 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ2 hid) hu a2 fun z ↦ (ku z).trans (b2 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R'
    obtain ⟨c1, d1, -, -⟩ := M.exact h
    obtain ⟨n1, -⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ1 hid) (M.θ1 h) _ hu hv a1 c1 (fun z ↦ (b1 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d1 z).symm) fun z ↦ ⟨⟨_, hz R' 1 z⟩, hn _ _ rfl, n1 _ _ rfl⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R'
    obtain ⟨-, -, c2, d2⟩ := M.exact h
    obtain ⟨-, n2⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ2 hid) (M.θ2 h) _ hu hv a2 c2 (fun z ↦ (b2 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d2 z).symm) fun z ↦ ⟨⟨_, hz R' 2 z⟩, hn _ _ rfl, n2 _ _ rfl⟩

end GlobalTheory.AbCoh.CohBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimLEIsLocalRingQuotPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.LowBaseChange

theorem krullDimLE_isLocalRing_quot_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 2 1 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

variable {R : Type} [CommRing R]

theorem one_tmul_eq_zero_iff {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {M : Type} [AddCommGroup M] [Module R M] (I : Ideal R)
    (t : (R ⧸ I) ⊗[R] M) : ∃ x : M, (1 : R ⧸ I) ⊗ₜ[R] x = t :=
  TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective t

theorem projective_coker_of_approx [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by
  haveI : IsNoetherian R B := isNoetherian_of_isNoetherianRing_of_finite R B
  have hinjq : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ m)) := by
    intro m _
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := exists_one_tmul m t
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, one_tmul_eq_zero_iff] at ht
    set N := B ⧸ (m • LinearMap.range f)
    have hq : (m • LinearMap.range f).mkQ (f a) ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R N) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨y, hy, hay⟩ := hyp m n a ht
      have e : (m • LinearMap.range f).mkQ (f a) = (m • LinearMap.range f).mkQ (f y) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hay
      rw [e]
      have hle : m ^ (n + 1) • (⊤ : Submodule R B) ≤
          (m ^ n • (⊤ : Submodule R N)).comap (m • LinearMap.range f).mkQ := by
        refine Submodule.smul_le.2 fun r hr x _ => ?_
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hr) Submodule.mem_top
      exact hle hy
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff _).1 hq
    have h1 : f a - (r : R) • f a ∈ m • LinearMap.range f := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul]
      exact hr.symm
    have hsplit : (⟨f a, LinearMap.mem_range_self f a⟩ : LinearMap.range f) =
        ⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a) (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ +
          (r : R) • ⟨f a, LinearMap.mem_range_self f a⟩ := by
      ext; simp
    rw [hsplit, TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
    have h2 : (1 : R ⧸ m) ⊗ₜ[R] (⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a)
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ : LinearMap.range f) = 0 := by
      rw [one_tmul_eq_zero_iff, Submodule.mem_smul_top_iff]; exact h1
    rw [h2, zero_add, Algebra.smul_def, _root_.mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 r.2, TensorProduct.zero_tmul]
  have hinj : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor m.ResidueField) := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have hL : RingHom.ker (algebraMap R (R ⧸ m)) = m := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have := GlobalTheory.exact_lTensor_iff_residueField m (R ⧸ m) hL
      (0 : PUnit →ₗ[R] LinearMap.range f) (LinearMap.range f).subtype
    rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective,
      LinearMap.exact_zero_iff_injective] at this
    exact this.1 (hinjq m)
  obtain ⟨l, hl⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
    (LinearMap.range f).subtype hinj
  have hex := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 1 2
  obtain ⟨s, hs⟩ := hex.2 ⟨l, hl⟩
  exact Module.Projective.of_split s _ hs

end GlobalTheory.AbCoh.LowBaseChange


open GlobalTheory.AbCoh.LowBaseChange in
theorem GlobalTheory.AbCoh.projective_coker_of_liftsAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  intro R _ _ K hK _ hL i hi
  haveI := (hK (i + 1)).1
  haveI := (hK (i + 1)).2
  refine projective_coker_of_approx (K.d i (i + 1)).hom ?_
  intro m _ n a ha
  obtain ⟨h0, h1⟩ := krullDimLE_isLocalRing_quot_pow m n
  haveI := h1
  haveI : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, h0⟩
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hle : m ^ (n + 1) ≤ m := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let α : (R ⧸ m ^ (n + 1)) →ₐ[R] (R ⧸ m) := Ideal.Quotient.factorₐ R hle
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hz : dB K (R ⧸ m) i (i + 1) ((1 : R ⧸ m) ⊗ₜ[R] a) = 0 := by
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
    exact ha
  obtain ⟨y, b, hy, hyb⟩ := hL i hi (R ⧸ m ^ (n + 1)) (R ⧸ m) α hα _ hz
  obtain ⟨y₀, rfl⟩ := exists_one_tmul _ y
  obtain ⟨b₀, rfl⟩ := exists_one_tmul _ b
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hy
  refine ⟨y₀, hy, ?_⟩
  rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← TensorProduct.tmul_add] at hyb
  have hdd : (K.d i (i + 1)).hom ((K.d (i - 1) i).hom b₀) = 0 := by
    have := congrArg (fun g => g.hom b₀) (K.d_comp_d (i - 1) i (i + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have hm : a - (y₀ + (K.d (i - 1) i).hom b₀) ∈ m • (⊤ : Submodule R (K.X i)) := by
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← hyb, sub_self]
  have := Submodule.mem_map_of_mem (f := (K.d i (i + 1)).hom) hm
  rw [Submodule.map_smul'', ← LinearMap.range_eq_map, map_sub, map_add (f := _), hdd, add_zero] at this
  exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.CohBaseChange

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s :=
  of_parts (@GlobalTheory.AbCoh.exists_finite_projective_model) (@GlobalTheory.AbCoh.projective_coker_of_liftsAt) (@GlobalTheory.AbCoh.cohom_split_baseChange)

end GlobalTheory.AbCoh.CohBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_cohomology_residue_field_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  first | exact @GlobalTheory.AbCoh.CohBaseChange.main | exact GlobalTheory.AbCoh.CohBaseChange.main | (intros; apply GlobalTheory.AbCoh.CohBaseChange.main <;> assumption)
end
