module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

def unitsT : CommRingCat.{0} ⥤ Type where
  obj A := (A : Type)ˣ
  map {A B} f := TypeCat.ofHom fun (u : (A : Type)ˣ) => Units.map f.hom.toMonoidHom u
  map_id A := by ext u; rfl
  map_comp f g := by ext u; rfl

structure Trip (q : ℕ) (A : Type) [CommRing A] where
  root : Prim q A
  src : Aˣ
  tgt : Aˣ
  tgt_eq : (tgt : A) = root.1 * src

def Trip.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Trip q A) : Trip q B :=
  ⟨x.root.map f, Units.map f.toMonoidHom x.src, Units.map f.toMonoidHom x.tgt, by
    change f (x.tgt : A) = f x.root.1 * f (x.src : A)
    rw [x.tgt_eq, map_mul]⟩

def tripT (q : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Trip q A
  map f := TypeCat.ofHom (Trip.map f.hom)
  map_id A := by
    ext x
    cases x
    rfl
  map_comp f g := by
    ext x
    cases x
    rfl

def unitsP : PSh := Scheme.Γ ⋙ unitsT

def tripP (q : ℕ) : PSh := Scheme.Γ ⋙ tripT q

def unitsP.mk {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) : unitsP.obj (op U) := v

def tripP.mk {q : ℕ} {U : Scheme.{0}} (x : Trip q Γ(U, ⊤)) : (tripP q).obj (op U) := x

def tripP.get {q : ℕ} {U : Scheme.{0}} (x : (tripP q).obj (op U)) : Trip q Γ(U, ⊤) := x

theorem unitsP.map_mk {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ) :
    unitsP.map g.op (unitsP.mk v) = unitsP.mk (Units.map g.appTop.hom.toMonoidHom v) := rfl

theorem smap_sum {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.map φ (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.map φ (f x) := by
  simp only [Sec.map, map_finsuppSum, map_smul]

theorem res_sum {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.res g (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.res g (f x) := by
  simp only [Sec.res, map_finsuppSum, map_smul]

theorem smap_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_eq_zero_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (s : Sec F U)
    (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  obtain ⟨S, hS, hS'⟩ := h
  exact Sheaf.isSeparated F U S hS s 0 (fun V g hg => (hS' V g hg).trans (map_zero _).symm)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U)) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

end GlobalTheory.EtC.KummerSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

noncomputable section

namespace GlobalTheory.EtC.FreeActSum

def rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q ((GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ) (NeZero.ne q)

lemma rootUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ((rootUnit ζ : Aˣ) : A) = ζ.1 := rfl

lemma orderOf_rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) :
    orderOf (rootUnit ζ) = q := by
  rw [orderOf_eq_iff (NeZero.pos q)]
  refine ⟨?_, ?_⟩
  · ext; simp [rootUnit_val, (GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ]
  · intro m hmq hm0 h1
    have hne : ¬ m ≡ 0 [MOD q] := by
      intro h
      have := (Nat.modEq_zero_iff_dvd).1 h
      exact absurd (Nat.le_of_dvd hm0 this) (not_le.2 hmq)
    have hu := (GlobalTheory.EtC.PrimBasic.prim_basic q A).2.2.1 ζ m 0 hne
    have h1' : ζ.1 ^ m = 1 := by
      have := congrArg (fun u : Aˣ => (u : A)) h1
      simpa [rootUnit_val] using this
    rw [h1', pow_zero, sub_self] at hu
    exact not_isUnit_zero hu

abbrev H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Subgroup Aˣ :=
  Subgroup.zpowers (rootUnit ζ)

lemma mem_H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u ∈ H ζ := by
  rw [← QuotientGroup.eq]
  simp

def expo {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ℤ :=
  Classical.choose (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

lemma expo_spec {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    rootUnit ζ ^ expo ζ u = ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u :=
  Classical.choose_spec (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

def tau {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ZMod q :=
  (expo ζ u : ZMod q)

lemma tau_mul {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (u : Aˣ) (n : ℕ) :
    tau ζ (rootUnit ζ ^ n * u) = tau ζ u + n := by
  have hcls : (QuotientGroup.mk (rootUnit ζ ^ n * u) : Aˣ ⧸ H ζ) = QuotientGroup.mk u := by
    rw [QuotientGroup.eq]
    have : (rootUnit ζ ^ n * u)⁻¹ * u = (rootUnit ζ ^ n)⁻¹ := by
      rw [mul_inv_rev, mul_comm u⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have h1 := expo_spec ζ (rootUnit ζ ^ n * u)
  have h2 := expo_spec ζ u
  rw [hcls] at h1
  set r := ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)
  have key : rootUnit ζ ^ (expo ζ (rootUnit ζ ^ n * u) - (n : ℤ) - expo ζ u) = 1 := by
    rw [zpow_sub, zpow_sub, h1, h2, zpow_natCast]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_rootUnit] at key
  unfold tau
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key
  push_cast at this
  linear_combination this

end GlobalTheory.EtC.FreeActSum

namespace GlobalTheory.EtC.FreeActSum

theorem free_act_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  intro q _ A _ _ ζ ι s c a v w hw hsum
  let T : (Aˣ →₀ ULift.{1} (ZMod q)) →+ ZMod q :=
    Finsupp.liftAddHom (fun u => (AddMonoidHom.mulRight (tau ζ u)).comp (AddEquiv.ulift.toAddMonoidHom))
  have hT := congrArg T hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at hT
  rw [← hT]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hwu : w i = rootUnit ζ ^ a i * v i := by
    ext; simp [rootUnit_val, hw i hi]
  simp only [T, map_sub, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulRight]
  rw [hwu, tau_mul]
  show (c i).down * (a i : ZMod q) = (c i).down * (tau ζ (v i) + a i) - (c i).down * tau ζ (v i)
  ring

end GlobalTheory.EtC.FreeActSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSumStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_free_action_finsupp_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  first | (exact @GlobalTheory.EtC.FreeActSum.free_act_sum) | (exact GlobalTheory.EtC.FreeActSum.free_act_sum) | (intros; apply GlobalTheory.EtC.FreeActSum.free_act_sum  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit


set_option maxHeartbeats 1000000 in
theorem res_resGen_of_pow (q : ℕ) [NeZero q] {W V : Scheme.{0}} (k : W ⟶ V) (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : k.appTop.hom ξ.1 = k.appTop.hom ζ.1 ^ (a : ZMod q).val) :
    Sec.res k (resGen 1 ξ) = (a : ZMod q).val • resGen 1 (ζ.map k.appTop.hom) := by
  have e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom) := by
    unfold resGen
    rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
  rw [e1]
  have e2 := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h
  simp only [zpow_one] at e2
  unfold resGen
  rw [e2]
  exact map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _

end GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit


set_option maxHeartbeats 1000000 in
theorem relation_kernel (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (hc : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  classical
  set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) :=
    c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r
    with hd_def
  have hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0 := by
    rw [← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
  have hloc := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val :=
    fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root
  have hall := loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots
  have hboth := loc_calculus.2.2.1 V _ _ hloc hall
  apply sec_eq_zero_of_loc
  refine loc_calculus.2.1 V _ _ hboth ?_
  rintro W k ⟨hkd, hka⟩
  rw [res_sum]
  by_cases hW : IsEmpty W
  · exact sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)
  rw [not_isEmpty_iff] at hW
  haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩
  choose a ha using hka
  let a' : (tripP q).obj (op V) → ℕ := fun x =>
    if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0
  have hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val := fun x hx => dif_pos hx
  have hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) =
      (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) •
        resGen 1 ((tripP.get x₀).root.map k.appTop.hom) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul,
      Nat.cast_smul_eq_nsmul]
  have halg := GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support
    (fun x => c x) a'
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src)
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) ?_ ?_
  · rw [hsum]
    suffices h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]
    apply ULift.ext
    rw [Finsupp.sum]
    refine Eq.trans ?_ halg
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]; simp
  · intro x hx
    rw [hax x hx]
    change k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) =
      k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))
    rw [(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]
  · rw [hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum] at hkd
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd
    exact hkd

end GlobalTheory.EtC.KummerSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero : ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q)), (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) - freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0 → (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.relation_kernel
  | exact GlobalTheory.EtC.KummerSplit.relation_kernel
  | (intros; apply GlobalTheory.EtC.KummerSplit.relation_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

theorem exists_comp_eq_of_injective {R : Type} [CommRing R] {A B K : Shv R} [Injective K] (g : A ⟶ B) (φ : A ⟶ K)
    (h : ∀ U (a : Sec A U), Sec.map g a = 0 → Sec.map φ a = 0) : ∃ ψ : B ⟶ K, g ≫ ψ = φ := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel g)
  have hf : S.f ≫ φ = 0 := by
    refine (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R (S.f ≫ φ)).2.2.2 0 fun U a => ?_
    have h0 : Sec.map g (Sec.map (kernel.ι g) a) = 0 := by
      rw [← sec_map_comp, kernel.condition]; rfl
    change Sec.map φ (Sec.map (kernel.ι g) a) = Sec.map (0 : kernel g ⟶ K) a
    rw [h U _ h0]; rfl
  exact ⟨hS.descToInjective φ hf, hS.comp_descToInjective φ hf⟩

theorem kernel_local (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (h : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero q V c h

theorem exists_isKum (q : ℕ) [NeZero q] : ∃ t, IsKum q t := by
  have hinj : Injective ((res (ZMod q) (tw q 1)).X 0) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q 1)).2.1 0
  have hu := free_hom_sections (ZMod q) unitsP ((free (ZMod q)).obj unitsP)
  obtain ⟨G, hG⟩ := (free_hom_sections (ZMod q) (tripP q) ((free (ZMod q)).obj unitsP)).1
    (fun U x => freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).src))
    (fun V U g x => by
      rw [res_sub, hu.2.2.1, hu.2.2.1]
      rfl)
  obtain ⟨Φ, hΦ⟩ := (free_hom_sections (ZMod q) (tripP q) ((res (ZMod q) (tw q 1)).X 0)).1
    (fun U x => resGen 1 (tripP.get x).root)
    (fun V U g x => by
      unfold resGen
      rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
      rfl)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective G Φ (fun U a ha => by
    apply sec_eq_zero_of_loc
    refine loc_calculus.2.1 U _ _ ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) (tripP q) U).1 a) ?_
    rintro V g ⟨c, hc⟩
    have hc' := congrArg (Sec.map G) hc
    rw [← sec_res_map, ha, res_zero', smap_sum] at hc'
    rw [sec_res_map, hc, smap_sum]
    simp only [hG] at hc'
    simp only [hΦ]
    exact kernel_local q V c hc'.symm)
  refine ⟨fun U v => Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)), ?_, ?_⟩
  · intro V U g v _
    rw [sec_res_map, hu.2.2.1]
    rfl
  · intro U ζ v w hw
    have e := congrArg (Sec.map ψ) (hG U (tripP.mk ⟨ζ, v, w, hw⟩))
    rw [← sec_map_comp, hψ, hΦ, smap_sub] at e
    change resGen 1 ζ = Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) -
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) at e
    show Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) =
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) + resGen 1 ζ
    rw [e]
    exact (add_sub_cancel _ _).symm

theorem isKum_kumT : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := fun q _ => pick_spec (exists_isKum q)

end GlobalTheory.EtC.KummerSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.isKum_kumT
  | exact GlobalTheory.EtC.KummerSplit.isKum_kumT
  | (intros; apply GlobalTheory.EtC.KummerSplit.isKum_kumT <;> assumption)
end
