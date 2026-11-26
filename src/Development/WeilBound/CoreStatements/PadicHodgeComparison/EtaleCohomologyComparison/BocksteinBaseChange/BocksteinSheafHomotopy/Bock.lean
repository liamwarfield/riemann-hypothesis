module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BocksteinLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

def IsRedSh {Q q : ℕ} (h : q ∣ Q) (i : ℤ) (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map π (twGen i ζ) = (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i ξ)

theorem dvdA (p a b : ℕ) : p ^ a ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_right a b)

theorem dvdB (p a b : ℕ) : p ^ b ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_left b a)

def InTwSeq : Prop := ∀ (p a b : ℕ) [Fact p.Prime] (i : ℤ),
  ∃ (π : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdB p a b) (ZMod (p ^ b)))).obj (tw (p ^ b) i))
    (π' : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i))
    (l : kernel π ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i)),
    IsRedSh (dvdB p a b) i π ∧ IsRedSh (dvdA p a b) i π' ∧ Epi π ∧ p ^ a • kernel.ι π = 0 ∧
      kernel.ι π ≫ π' = p ^ b • l

def InRedSh : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ)
  (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)), IsRedSh h i π →
  ∀ (E : Spc) (n : ℤ) (z : Ht Q E n i),
    restrH (ZMod.castHom h (ZMod q)) E (tw q i) n (red Q q E n i z) = HK.post _ ((chains _).obj E) π n z

theorem bock_of (hS : InTwSeq) (hR : InRedSh) : BocksteinInputFromFormal := by
  intro hF p a b _ X _ n i z hz
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, π', l, hπ, hπ', hepi, htor, hcomp⟩ := hS p a b i
  have hex : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
  obtain ⟨c, hc⟩ := hF.a7 (ZMod (p ^ (a + b))) _ hex
  have e1 := hR _ _ (dvdB p a b) i π hπ (sch.obj X) n z
  rw [hz, map_zero] at e1
  obtain ⟨w', hw'⟩ := ((hc ((chains (ZMod (p ^ (a + b)))).obj (sch.obj X)) n).1 z).1 e1.symm
  subst hw'
  refine ⟨?_, ?_⟩
  · change p ^ a • HK.post _ _ (kernel.ι π) n w' = 0
    rw [← PostcompositionHomotopy.post_nsmul, htor, PostcompositionHomotopy.post_zero]
  · have hA := hF.a8 _ _ (ZMod.castHom (dvdA p a b) (ZMod (p ^ a))) (sch.obj X) (tw (p ^ a) i) n
    obtain ⟨v, hv⟩ := hA.2 (HK.post _ _ l n w')
    refine ⟨v, hA.1 ?_⟩
    rw [hR _ _ (dvdA p a b) i π' hπ' (sch.obj X) n, map_nsmul, hv]
    change HK.post _ _ π' n (HK.post _ _ (kernel.ι π) n w') = _
    rw [← PostcompositionHomotopy.post_comp, hcomp, PostcompositionHomotopy.post_nsmul]

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison.CyclicComplexMaps

open GlobalTheory.EtC

theorem cyc_dvd (Q q : ℕ) (hQ : Q ≠ 0) (h : q ∣ Q) :
    Polynomial.cyclotomic Q ℤ ∣ (Polynomial.cyclotomic q ℤ).comp (Polynomial.X ^ (Q / q)) := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact hQ (Nat.eq_zero_of_zero_dvd h)
  have hμ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q)) Q := Complex.isPrimitiveRoot_exp Q hQ
  have hm0 : Q / q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) h) (Nat.pos_of_ne_zero hq)).ne'
  have hξ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Q) ^ (Q / q)) q := by
    have := hμ.pow_of_dvd hm0 (Nat.div_dvd_of_dvd h)
    rwa [Nat.div_div_self h hQ] at this
  rw [Polynomial.cyclotomic_eq_minpoly hμ (Nat.pos_of_ne_zero hQ)]
  apply minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (Nat.pos_of_ne_zero hQ))
  rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X,
    Polynomial.cyclotomic_eq_minpoly hξ (Nat.pos_of_ne_zero hq), minpoly.aeval]

theorem prim_pow {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) :
    ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ (Q / q) := by
  have hQ : Q ≠ 0 := NeZero.ne Q
  refine ⟨Subtype.mk (ζ.1 ^ (Q / q)) ⟨?_, ?_⟩, rfl⟩
  · have hmul : (q : A) * ((Q / q : ℕ) : A) = (Q : A) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
    exact isUnit_of_mul_isUnit_left (by rw [hmul]; exact ζ.2.1)
  · obtain ⟨r, hr⟩ := cyc_dvd Q q hQ h
    have h0 : Polynomial.aeval ζ.1 ((Polynomial.cyclotomic q ℤ).comp (Polynomial.X ^ (Q / q))) = 0 := by
      rw [hr, map_mul, ζ.2.2, zero_mul]
    rwa [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] at h0

theorem tw_ext {Q : ℕ} {i : ℤ} {G : Shv (ZMod Q)} (f g : tw Q i ⟶ G)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = Sec.map g (twGen i ζ)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext _ _ _ G.property ?_
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext'
  intro ζ
  apply LinearMap.ext_ring
  exact h U.unop ζ

variable {Q : ℕ} [NeZero Q]

theorem zmod_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} (ZMod Q)) M]
    [Module (ULift.{1} (ZMod Q)) N] (f : M →+ N) (c : ULift.{1} (ZMod Q)) (x : M) : f (c • x) = c • f x := by
  have hc : c = ((c.down.val : ℕ) : ULift.{1} (ZMod Q)) :=
    ULift.ext (ZMod.natCast_zmod_val c.down).symm
  rw [hc]
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

def shHom {F G : Shv (ZMod Q)} (a : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (ha : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U), Sec.res g (a U x) = a V (Sec.res g x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom { toFun := a U.unop, map_add' := map_add _, map_smul' := zmod_smul (a U.unop) }
     naturality := fun U V g => by
       ext x
       exact (ha g.unop x).symm }⟩

def cxHom {I J : GlobalTheory.EtC.Cx (ZMod Q)} (σ : SemiMap I J) : I ⟶ J where
  f s := shHom (fun U => σ.app U s) (fun g x => σ.nat g s x)
  comm' s t _ := by
    apply Sheaf.hom_ext
    ext U x
    exact σ.comm U.unop s t x

theorem ev_comp {R : Type} [CommRing R] {E : Spc} {I J : GlobalTheory.EtC.Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (g : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom g) (add_zero n)) p s h U x = Sec.map (g.f s) (ev α p s h U x) := by
  delta ev Sec.map
  simp [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

private theorem resι_eq_singleObjXSelf_inv_comp {R : Type} [CommRing R] (X : Shv R) :
    resι R X = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).inv ≫
      (injectiveResolution X).ι.f 0 ≫
        (HomologicalComplex.extendXIso (injectiveResolution X).cocomplex ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).inv := by
  delta resι InjectiveResolution.ι' HomologicalComplex.extendSingleIso ComplexShape.Embedding.extendFunctor
  simp [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)]

theorem cpost_of_aug {R : Type} [CommRing R] (K : GlobalTheory.EtC.Cx R) {F G : Shv R} (φ : F ⟶ G)
    (g : (injectiveResolution F).cochainComplex ⟶ (injectiveResolution G).cochainComplex)
    (hg : resι R F ≫ g.f 0 = φ ≫ resι R G) (n : ℤ) (x : HK R K F n) :
    cpost K (Cocycle.ofHom g) n n (add_zero n) x = HK.post R K φ n x := by
  let g₀ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex :=
    { f := fun i => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ g.f (i : ℤ) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom
      comm' := fun i j _ => by
        have hdF : (injectiveResolution F).cochainComplex.d (i : ℤ) (j : ℤ) =
            (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution F).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv :=
          HomologicalComplex.extend_d_eq _ _ rfl rfl
        have hdG : (injectiveResolution G).cochainComplex.d (i : ℤ) (j : ℤ) =
            (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ (injectiveResolution G).cocomplex.d i j ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).inv :=
          HomologicalComplex.extend_d_eq _ _ rfl rfl
        have h1 := g.comm (i : ℤ) (j : ℤ)
        rw [hdF, hdG] at h1
        have h2 := congrArg (fun t => (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ t ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := j) (i' := ((j : ℕ) : ℤ)) rfl).hom) h1
        simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] at h2
        simpa only [Category.assoc] using h2 }
  have hext : g = HomologicalComplex.extendMap g₀ ComplexShape.embeddingUpNat := by
    ext j : 1
    by_cases hj : ∃ i : ℕ, (i : ℤ) = j
    · obtain ⟨i, rfl⟩ := hj
      rw [HomologicalComplex.extendMap_f g₀ ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl]
      show _ = (HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom ≫ ((HomologicalComplex.extendXIso (injectiveResolution F).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv ≫ g.f (i : ℤ) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).hom) ≫ (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := i) (i' := ((i : ℕ) : ℤ)) rfl).inv
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hj ⟨i, hi⟩)).eq_of_src _ _
  have hι : (injectiveResolution F).ι ≫ g₀ =
      (CochainComplex.single₀ (Shv R)).map φ ≫ (injectiveResolution G).ι := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]
    have hg' := hg
    rw [resι_eq_singleObjXSelf_inv_comp, resι_eq_singleObjXSelf_inv_comp] at hg'
    have h3 := congrArg (fun t => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom ≫ t ≫
      (HomologicalComplex.extendXIso (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).hom) hg'
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at h3
    exact h3
  rw [CrystallineSemistableComparison.PostcompositionHomotopy.post_eq K φ g₀ hι n x, ← hext]
  rfl

end CrystallineSemistableComparison.CyclicComplexMaps
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.MorphZeroOfSec
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace KummerTwistLemmas

theorem twLift {Q : ℕ} [NeZero Q] (i : ℤ) (G : Shv (ZMod Q)) (e : ∀ (U : Scheme.{0}), Prim Q Γ(U, ⊤) → Sec G U)
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = (ULift.up ((a ^ i : (ZMod Q)ˣ) : ZMod Q) : ULift.{1} (ZMod Q)) • e U ζ) :
    ∃ f : tw Q i ⟶ G, ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map f (twGen i ζ) = e U ζ := by
  let L : ∀ (U : Scheme.{0}), (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) →ₗ[ULift.{1} (ZMod Q)] Sec G U :=
    fun U => Finsupp.linearCombination (ULift.{1} (ZMod Q)) (e U)
  have hL : ∀ (U : Scheme.{0}), twRel Q i Γ(U, ⊤) ≤ LinearMap.ker (L U) := by
    intro U
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
    rw [hr U ζ ξ a h, sub_self]
  let η : (Scheme.Γ ⋙ twF Q i) ⟶ G.obj :=
    { app := fun U => ModuleCat.ofHom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop))
      naturality := fun U V g => by
        refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
        change (twRel Q i Γ(V.unop, ⊤)).liftQ (L V.unop) (hL V.unop)
            (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g).hom) (Finsupp.single ζ c))) =
          (G.obj.map g).hom ((twRel Q i Γ(U.unop, ⊤)).liftQ (L U.unop) (hL U.unop) (Submodule.Quotient.mk (Finsupp.single ζ c)))
        rw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single]
        simp only [L, Finsupp.linearCombination_single, map_smul]
        congr 1
        exact (he g.unop ζ).symm }
  refine ⟨((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ _).symm η,
    fun U ζ => ?_⟩
  have h := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} (ZMod Q)))).homEquiv _ G).apply_symm_apply η
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim Q Γ(U, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(U, ⊤))
  refine h2.trans ?_
  change (twRel Q i Γ(U, ⊤)).liftQ (L U) (hL U) (Submodule.Quotient.mk (Finsupp.single ζ 1)) = e U ζ
  rw [Submodule.liftQ_apply]
  simp [L]

end KummerTwistLemmas

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem pow_self {Q : ℕ} {A : Type} [CommRing A] (ζ : Prim Q A) : ζ.1 ^ Q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one Q ℤ
  have := congrArg (Polynomial.aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
  exact this

def pw {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ζ.2.1, by
    obtain ⟨c, hc⟩ := CyclicComplexMaps.cyc_dvd Q q (NeZero.ne Q) h
    have := congrArg (Polynomial.aeval ζ.1) hc
    rw [Polynomial.aeval_comp, map_mul, ζ.2.2, zero_mul] at this
    simpa using this⟩

theorem pw_val {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : (pw h ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem pw_map {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    (pw h ζ).map f = pw h (ζ.map f) := Subtype.ext (map_pow f _ _)

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤))
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem redSheaf (hG : E.InGen) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) :
    ∃ π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i), IsRedSh h i π ∧
      ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map π (twGen i ζ) =
        (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)) := by
  obtain ⟨π, hπ⟩ := KummerTwistLemmas.twLift i ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))
    (fun U ζ => (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)))
    (fun g ζ => by
      change Sec.res g (twGen i (pw h ζ)) = twGen i (pw h (ζ.map g.appTop.hom))
      rw [twGen_res, pw_map])
    (fun U ζ ξ a ha => by
      let a' : (ZMod q)ˣ := ZMod.unitsMap h a
      have hξ : (pw h ξ).1 = (pw h ζ).1 ^ (a' : ZMod q).val := by
        rw [pw_val, pw_val, ha, ← pow_mul, mul_comm, pow_mul]
        have h1 : ((pw h ζ).1) ^ q = 1 := pow_self (pw h ζ)
        rw [← pw_val h ζ, pow_eq_pow_mod _ h1, pow_eq_pow_mod ((a' : ZMod q).val) h1]
        have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
          change (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
          rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
        rw [hv, Nat.mod_mod]
      have := ((hG q i).2.2 U (pw h ζ) (pw h ξ) a' hξ)
      change twGen i (pw h ξ) = (ULift.up (ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) : ULift.{1} (ZMod q)) • twGen i (pw h ζ)
      rw [this, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      congr 1
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
      simp only [a', ZMod.unitsMap]
      rw [← map_zpow]
      rfl)
  refine ⟨π, fun U ζ ξ hξ => ?_, hπ⟩
  rw [hπ U ζ, show pw h ζ = ξ from Subtype.ext (show (pw h ζ).1 = ξ.1 from hξ.symm)]

end CrystallineSemistableComparison.TwSeq
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.LocBind
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSec

open GlobalTheory.EtC

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  change (F.obj.map (k ≫ g).op).hom y = (F.obj.map k.op).hom ((F.obj.map g.op).hom y)
  rw [op_comp, Functor.map_comp]
  rfl

theorem loc_bind' {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h' V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

theorem tw_loc (hG : E.InGen) (Q : ℕ) [NeZero Q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw Q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  have hsurj : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF Q i)) y ∈ Scheme.etaleTopology U :=
    Presheaf.imageSieve_mem Scheme.etaleTopology _ (U := op U) y
  refine loc_bind' ⟨_, hsurj, fun V g hg => hg⟩ ?_
  rintro V g ⟨t, ht⟩
  by_cases hP : Nonempty (Prim Q Γ(V, ⊤))
  · obtain ⟨ζ₀⟩ := hP
    obtain ⟨S, hS, hS'⟩ := (hG Q i).1 V ζ₀ (Sec.res g y)
    refine ⟨S, hS, fun W k hk => Or.inr ?_⟩
    obtain ⟨c, hc⟩ := hS' W k hk
    exact ⟨ζ₀.map k.appTop.hom, c, (res_comp k g y).trans hc⟩
  · have : IsEmpty (Prim Q Γ(V, ⊤)) := not_nonempty_iff.mp hP
    have ht0 : t = 0 := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel Q i Γ(V, ⊤))
        (show (Prim Q Γ(V, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(V, ⊤) from t)
      have hf : f = 0 := Finsupp.ext fun a => (IsEmpty.false a).elim
      rw [hf]
      exact Submodule.Quotient.mk_zero _
    have hy : Sec.res g y = 0 := by
      refine ht.symm.trans ?_
      rw [ht0]
      exact map_zero _
    refine ⟨⊤, Scheme.etaleTopology.top_mem V, fun W k _ => Or.inl ?_⟩
    rw [res_comp, hy]
    exact map_zero _

end CrystallineSemistableComparison.TwSec
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SheafSectionLemmas
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.SheafSectionLemmas

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hSP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hSP⟩ := h
  refine ⟨Sieve.bind S.arrows (fun V g hg => (h' V g (hSP V g hg)).choose),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => (h' V g (hSP V g hg)).choose_spec.1), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hSP V g hg)).choose_spec.2 W k hk

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_eq_of_loc {F : Shv R} {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ((isSheaf_types F) S hS).isSeparatedFor.ext fun _ g hg => hSP _ g hg

theorem sec_subsingleton_of_isEmpty (F : Shv R) (U : Scheme.{0}) [IsEmpty U] : Subsingleton (Sec F U) :=
  ⟨fun a b => ((isSheaf_types F).isSheafFor (⊥ : Presieve U)
    (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology U)).isSeparatedFor.ext (fun _ _ h => h.elim)⟩

theorem epi_of_loc {F G : Shv R} (φ : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec G U), Loc U fun V g => ∃ x : Sec F V, Sec.map φ x = Sec.res g y) : Epi φ := by
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro U y
    obtain ⟨S, hS, hSP⟩ := h U y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hSP V g hg
    exact ⟨x, hx⟩
  infer_instance

theorem sec_map_comp {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_injective_of_mono {X Y : Shv R} (f : X ⟶ Y) [Mono f] (U : Scheme.{0}) :
    Function.Injective (Sec.map f (U := U)) := by
  have h1 : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have h2 : Mono (f.hom.app (op U)) := (NatTrans.mono_iff_mono_app f.hom).1 h1 (op U)
  exact (ModuleCat.mono_iff_injective _).1 h2

theorem epi_lift_of_loc {X Y Z : Shv R} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
    (h : ∀ (U : Scheme.{0}) (y : Sec Y U), Sec.map g y = 0 →
      Loc U fun V k => ∃ x : Sec X V, Sec.map f x = Sec.res k y) :
    Epi (kernel.lift g f w) := by
  apply epi_of_loc
  intro U y
  have hy : Sec.map g (Sec.map (kernel.ι g) y) = 0 := by
    rw [← sec_map_comp, kernel.condition]; rfl
  refine loc_mono (h U _ hy) fun V k ⟨x, hx⟩ => ⟨x, ?_⟩
  apply sec_map_injective_of_mono (kernel.ι g)
  rw [← sec_map_comp, kernel.lift_ι, hx, GlobalTheory.EtC.CupSpec.map_res]

theorem ker_comp_zero {X Y Z : Shv R} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ (U : Scheme.{0}) (y : Sec X U), Sec.map f y = 0 → Sec.map g y = 0) : kernel.ι f ≫ g = 0 := by
  apply Sheaf.hom_ext
  ext U y
  refine (h U.unop (Sec.map (kernel.ι f) y) ?_).trans rfl
  rw [← sec_map_comp, kernel.condition]; rfl

end CrystallineSemistableComparison.SheafSectionLemmas
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.RootLoc
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ComapSurjOfLift
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem comap_surj_of_lift {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : A →+* K), ∃ χ : S →+* K, χ.comp (algebraMap A S) = ψ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A S)) := by
  intro p
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let ψ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  obtain ⟨χ, hχ⟩ := h K ψ
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change χ (algebraMap A S a) = 0 ↔ a ∈ p.asIdeal
  rw [← RingHom.comp_apply, hχ]
  simp only [ψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField K).injective]
  rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

theorem etaleCover (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S))) :
    ∃ (W : Scheme.{0}) (π : W ⟶ U) (φ : S →+* Γ(W, ⊤)),
      Sieve.ofArrows (fun _ : Unit => W) (fun _ => π) ∈ Scheme.etaleTopology U ∧
      ∀ a, φ (algebraMap Γ(U, ⊤) S a) = π.appTop.hom a := by
  let φ0 : Γ(U, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)
  have : Etale (Spec.map φ0) := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map φ0) := ⟨hS⟩
  have : Surjective (pullback.fst U.toSpecΓ (Spec.map φ0)) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  refine ⟨pullback U.toSpecΓ (Spec.map φ0), pullback.fst _ _,
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop).hom, ?_, ?_⟩
  · let 𝒰 : U.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Unit
      (fun _ => pullback U.toSpecΓ (Spec.map φ0)) (fun _ => pullback.fst _ _)
      (fun x => ⟨(), (pullback.fst U.toSpecΓ (Spec.map φ0)).surjective x⟩) (fun _ => inferInstance)
    exact 𝒰.mem_grothendieckTopology
  · intro a
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := U.toSpecΓ) (g := Spec.map φ0))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
    have key : φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop =
        (pullback.fst U.toSpecΓ (Spec.map φ0)).appTop := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h, ← Category.assoc, ← Scheme.ΓSpecIso_naturality]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k => k.hom a) key

theorem loc_of_etale (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S)))
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (χ : S →+* Γ(V, ⊤)), (∀ a, χ (algebraMap Γ(U, ⊤) S a) = g.appTop.hom a) → P V g) :
    Loc U P := by
  obtain ⟨W, π, φ, hmem, hφ⟩ := etaleCover U S hS
  refine ⟨_, hmem, fun V g hg => ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  refine hP V (h ≫ π) (h.appTop.hom.comp φ) fun a => ?_
  rw [RingHom.comp_apply, hφ, Scheme.Hom.comp_appTop]
  rfl

theorem kumLoc (U : Scheme.{0}) (m : ℕ) (u : (Γ(U, ⊤))ˣ) (hm : IsUnit (m : Γ(U, ⊤))) :
    Loc U fun V g => ∃ v : Γ(V, ⊤), v ^ m = g.appTop.hom u.1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨1, ?_⟩⟩
    have h01 : (0 : Γ(U, ⊤)) = 1 := by simpa using isUnit_zero_iff.mp (by simpa using hm)
    have h01' : (0 : Γ(V, ⊤)) = 1 := by simpa using congrArg g.appTop.hom h01
    have := subsingleton_of_zero_eq_one h01'
    exact Subsingleton.elim _ _
  · let c : Γ(U, ⊤) := (hm.unit⁻¹ : (Γ(U, ⊤))ˣ)
    have hc : c * (m : Γ(U, ⊤)) = 1 := hm.val_inv_mul
    let Pp : StandardEtalePair Γ(U, ⊤) :=
      { f := X ^ m - C u.1
        monic_f := monic_X_pow_sub_C _ hm0.ne'
        g := X
        cond := ⟨C c * X, 0, m, by
          rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
          have hX : (X : (Γ(U, ⊤))[X]) ^ (m - 1) * X = X ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
          have hC : C (m : Γ(U, ⊤)) * C c = 1 := by rw [← C_mul, mul_comm, hc, C_1]
          linear_combination (X ^ (m - 1) * X) * hC + hX⟩ }
    refine loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_
    · obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ψ u.1) hm0
      let _ := ψ.toAlgebra
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_pow hm0.ne'] at hx
        exact (u.isUnit.map ψ).ne_zero hx.symm
      have hmap : Pp.HasMap x := ⟨by simp [Pp, hx, RingHom.algebraMap_toAlgebra], by simpa [Pp] using hx0⟩
      exact ⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩
    · refine ⟨χ Pp.X, ?_⟩
      have h0 := (StandardEtalePair.hasMap_X (P := Pp)).1
      have h1 : Pp.X ^ m = algebraMap Γ(U, ⊤) Pp.Ring u.1 := by
        simpa [Pp, sub_eq_zero] using h0
      rw [← map_pow, h1, hχ]

end CrystallineSemistableComparison.KummerTwistLemmas
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem cyc_pow (p b : ℕ) (hp : p.Prime) (hb : 0 < b) :
    ∀ a : ℕ, expand ℤ (p ^ a) (cyclotomic (p ^ b) ℤ) = cyclotomic (p ^ (a + b)) ℤ
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ', expand_mul, cyc_pow p b hp hb a,
      cyclotomic_expand_eq_cyclotomic hp (dvd_pow_self p (by omega : a + b ≠ 0))]
    congr 1
    rw [← pow_succ]
    congr 1
    omega

theorem rootLoc (p a b : ℕ) [Fact p.Prime] (hb : 0 < b) (U : Scheme.{0}) (ξ : Prim (p ^ b) Γ(U, ⊤)) :
    Loc U fun V g => ∃ ζ : Prim (p ^ (a + b)) Γ(V, ⊤), ζ.1 ^ (p ^ a) = g.appTop.hom ξ.1 := by
  have hp : p.Prime := Fact.out
  have hpU : IsUnit (p : Γ(U, ⊤)) := by
    have h := ξ.2.1
    rw [Nat.cast_pow] at h
    exact (isUnit_pow_iff hb.ne').1 h
  have hξ1 : ξ.1 ^ (p ^ b) = 1 := by
    obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one (p ^ b) ℤ
    have := congrArg (aeval ξ.1) hh
    rw [map_mul, ξ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  have hξu : IsUnit ξ.1 := by
    refine isUnit_iff_exists_inv.2 ⟨ξ.1 ^ (p ^ b - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)), hξ1]
  obtain ⟨S, hS, hP⟩ := kumLoc U (p ^ a) hξu.unit (by rw [Nat.cast_pow]; exact hpU.pow _)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, hv⟩ := hP V g hg
  rw [IsUnit.unit_spec] at hv
  have hpV : IsUnit (p : Γ(V, ⊤)) := by simpa using hpU.map g.appTop.hom
  refine ⟨⟨v, by rw [Nat.cast_pow]; exact hpV.pow _, ?_⟩, hv⟩
  rw [← cyc_pow p b hp hb a, expand_aeval, hv]
  exact (Prim.map g.appTop.hom ξ).2.2

end CrystallineSemistableComparison.KummerTwistLemmas
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem sec_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map (k • f) x = k • Sec.map f x := map_nsmul (CupSpec.mapHom X Y x) k f

theorem sec_map_nsmul {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) (k : ℕ) {U : Scheme.{0}} (x : Sec X U) :
    Sec.map f (k • x) = k • Sec.map f x := map_nsmul (f.hom.app (op U)).hom k x

theorem res_nsmul {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (k : ℕ) (x : Sec X U) :
    Sec.res g (k • x) = k • Sec.res g x := map_nsmul (X.obj.map g.op).hom k x

theorem res_zero {R : Type} [CommRing R] {X : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec X U) = 0 :=
  map_zero (X.obj.map g.op).hom

theorem sec_map_zero' {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U : Scheme.{0}} : Sec.map f (0 : Sec X U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem sec_char {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (x : Sec F U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_self]
    rfl
  rw [this, zero_smul]

theorem morph_zero_of_sec {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y)
    (h : ∀ (U : Scheme.{0}) (x : Sec X U), Sec.map f x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem loc_of_img {R : Type} [CommRing R] {X Y : Shv R} (f : X ⟶ Y) {U V : Scheme.{0}} (g : V ⟶ U) (y : Sec Y U)
    (x : Sec X V) (hx : Sec.map f x = Sec.res g y) :
    Loc V fun W k => ∃ x' : Sec X W, Sec.map f x' = Sec.res (k ≫ g) y :=
  SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true V) fun W k _ => ⟨Sec.res k x, by rw [← CupSpec.map_res, hx, TwSec.res_comp]⟩

theorem twSeq (hG : E.InGen) : InTwSeq := by
  intro p a b _ i
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, hπ, hπg⟩ := redSheaf hG (dvdB p a b) i
  obtain ⟨π', hπ', hπ'g⟩ := redSheaf hG (dvdA p a b) i
  obtain ⟨m, hmdef⟩ : ∃ m : tw (p ^ (a + b)) i ⟶ tw (p ^ (a + b)) i, m = p ^ b • 𝟙 _ := ⟨_, rfl⟩
  have hm : ∀ (U : Scheme.{0}) (x : Sec (tw (p ^ (a + b)) i) U), Sec.map m x = p ^ b • x := fun U x => by
    rw [hmdef]; exact sec_nsmul _ _ x
  have hw : m ≫ π = 0 := morph_zero_of_sec _ fun U x => by
    change Sec.map π (Sec.map m x) = 0
    rw [hm, sec_map_nsmul]
    exact sec_char (q := p ^ b) (F := tw (p ^ b) i) (Sec.map π x)
  have hQ : p ^ a • m = 0 := by
    rw [hmdef, smul_smul, ← pow_add]
    exact morph_zero_of_sec _ fun U x => by rw [sec_nsmul]; exact sec_char x

  have hπepi : Epi π := by
    refine SheafSectionLemmas.epi_of_loc π fun U y => ?_
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hy : y = 0 := by
        have h0 := sec_char (q := p ^ b) (F := tw (p ^ b) i) y
        have h1 : p ^ b = 1 := by rw [hb, pow_zero]
        exact (one_nsmul y).symm.trans ((congrArg (fun n : ℕ => n • y) h1.symm).trans h0)
      exact SheafSectionLemmas.loc_mono (SheafSectionLemmas.loc_true U) fun V g _ => ⟨0, by rw [sec_map_zero', hy]; exact (res_zero g).symm⟩
    · refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ b) i U y) fun V g hy => ?_
      rcases hy with hy | ⟨ξ, c, hy⟩
      · exact loc_of_img π g y 0 (by rw [sec_map_zero']; exact hy.symm)
      · refine SheafSectionLemmas.loc_mono (KummerTwistLemmas.rootLoc p a b hb V ξ) fun W k ⟨ζ, hζ⟩ => ⟨c • twGen i ζ, ?_⟩
        rw [sec_map_nsmul, hπg]
        change c • twGen i (pw (dvdB p a b) ζ) = Sec.res (k ≫ g) (show Sec (tw (p ^ b) i) U from y)
        rw [TwSec.res_comp, hy, res_nsmul, twGen_res]
        congr 2
        apply Subtype.ext
        change ζ.1 ^ (p ^ (a + b) / p ^ b) = (k.appTop.hom) ξ.1
        rw [← hζ, Nat.pow_div (Nat.le_add_left b a) (Nat.pos_of_ne_zero hp), Nat.add_sub_cancel]

  have hepi : Epi (kernel.lift π m hw) := by
    refine SheafSectionLemmas.epi_lift_of_loc m π hw fun U y hy => ?_
    refine SheafSectionLemmas.loc_bind (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · exact loc_of_img m g y 0 (by rw [sec_map_zero']; exact hy'.symm)
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact loc_of_img m g y 0 ((SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _)
      · have h0 : c • twGen i (pw (dvdB p a b) ζ) = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', sec_map_nsmul, hπg] at this
          exact this
        obtain ⟨d, rfl⟩ := (hG (p ^ b) i).2.1 V (pw (dvdB p a b) ζ) c h0
        exact loc_of_img m g y (d • twGen i ζ) (by rw [hm, smul_smul, hy'])

  have hker : kernel.ι m ≫ π' = 0 := by
    refine SheafSectionLemmas.ker_comp_zero m π' fun U y hy => ?_
    refine SheafSectionLemmas.sec_eq_of_loc _ _ (SheafSectionLemmas.loc_mono (TwSec.tw_loc hG (p ^ (a + b)) i U y) fun V g hy' => ?_)
    rw [res_zero, CupSpec.map_res]
    rcases hy' with hy' | ⟨ζ, c, hy'⟩
    · rw [hy', sec_map_zero']
    · rcases isEmpty_or_nonempty V with hV | hV
      · exact (SheafSectionLemmas.sec_subsingleton_of_isEmpty _ V).elim _ _
      · have h0 : (p ^ b * c) • twGen i ζ = 0 := by
          have := congrArg (Sec.res g) hy
          rw [res_zero, CupSpec.map_res, hy', hm, smul_smul] at this
          exact this
        have hd := (hG (p ^ (a + b)) i).2.1 V ζ _ h0
        rw [pow_add, mul_comm (p ^ a)] at hd
        obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos (Nat.pos_of_ne_zero hp) b) hd
        rw [hy', sec_map_nsmul, hπ'g, ← smul_smul]
        exact sec_char (q := p ^ a) (F := tw (p ^ a) i) _

  obtain ⟨e, hedef⟩ : ∃ e, e = kernel.lift π m hw := ⟨_, rfl⟩
  have he : e ≫ kernel.ι π = m := by rw [hedef]; exact kernel.lift_ι _ _ _
  have : Epi e := by rw [hedef]; exact hepi
  have hz : kernel.ι e ≫ π' = 0 := by
    have h1 : kernel.ι e ≫ m = 0 := by rw [← he, kernel.condition_assoc, zero_comp]
    rw [← kernel.lift_ι m (kernel.ι e) h1, Category.assoc, hker, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l, e ≫ l = π' := ⟨Abelian.epiDesc e π' hz, Abelian.comp_epiDesc e π' hz⟩
  have hcomp : kernel.ι π ≫ π' = p ^ b • l := by
    apply (cancel_epi e).1
    have h2 : e ≫ kernel.ι π ≫ π' = m ≫ π' := by rw [← Category.assoc, he]
    rw [h2, Preadditive.comp_nsmul, hl, hmdef, Preadditive.nsmul_comp, Category.id_comp]
  have htor : p ^ a • kernel.ι π = 0 := by
    apply (cancel_epi e).1
    rw [Preadditive.comp_nsmul, he, hQ, comp_zero]
  exact ⟨π, π', l, hπ, hπ', hπepi, htor, hcomp⟩

end CrystallineSemistableComparison.TwSeq
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
end
end

namespace CrystallineSemistableComparison

theorem bock : BocksteinInputFromFormal := fun hF => bock_tw (TwSeq.twSeq hF.et.gen) hF

end CrystallineSemistableComparison
