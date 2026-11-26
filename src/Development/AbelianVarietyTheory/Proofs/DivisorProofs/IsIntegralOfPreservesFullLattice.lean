module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem aeval_restrict_coe_of_stable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) {N : Submodule R M} (h : ∀ x ∈ N, f x ∈ N) (q : R[X]) (x : N) :
    ((aeval (f.restrict h) q x : N) : M) = aeval f q x := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    have hpow : ∀ (k : ℕ) (y : N), ((((f.restrict h) ^ k) y : N) : M) = (f ^ k) y := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]

theorem isIntegral_of_lat_stable : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  intro K B u L hL hu
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End K.O B.A := LinearMap.mulLeft K.O u
  have hf : ∀ x ∈ L, f x ∈ L := hu
  obtain ⟨p, hpm, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero K.O (f.restrict hf)
  refine ⟨p, hpm, ?_⟩
  have hlmul : aeval f p = LinearMap.mulLeft K.O (aeval u p) := by
    have : f = Algebra.lmul K.O B.A u := rfl
    rw [this, Polynomial.aeval_algHom_apply]
    rfl
  have key : ∀ x ∈ L, aeval u p * x = 0 := by
    intro x hx
    have h1 := aeval_restrict_coe_of_stable f hf p ⟨x, hx⟩
    rw [hp, hlmul] at h1
    simpa using h1.symm
  have hall : ∀ a : B.A, aeval u p * a = 0 := by
    intro a
    have ha : a ∈ Submodule.span K.E (L : Set B.A) := hL.2 ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have := hall 1
  rw [mul_one] at this
  exact this

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLatticeStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_preserves_fullLattice : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  first | exact @GlobalTheory.UnitLemma.isIntegral_of_lat_stable | exact GlobalTheory.UnitLemma.isIntegral_of_lat_stable | (intros; apply GlobalTheory.UnitLemma.isIntegral_of_lat_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIff
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CongConj

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {m : ℕ}

theorem v_le_one_of_mem_KGL {c : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m)) (i j : Fin m) :
    Valued.v (c.val i j) ≤ 1 := by
  obtain ⟨a, rfl⟩ := hc
  exact (a.val i j).2

theorem v_mul_left_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ γ) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hB l j)

theorem v_mul_right_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ γ) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) (hB l j)

theorem conj_imp (k : ℕ) {c N : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w (n := m))
    (hN : N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) :
    c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j -
      (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  refine ⟨mul_mem (mul_mem (inv_mem hc) hN.1) hc, fun i j => ?_⟩
  have hid : (c⁻¹ * N * c).val - 1 = (c⁻¹).val * (N.val - 1) * c.val := by
    have h1 : (c⁻¹).val * c.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have := v_mul_right_le (v_mul_left_le (B := N.val - 1) (v_le_one_of_mem_KGL (inv_mem hc)) (fun a b => by
    rw [Matrix.sub_apply]; exact hN.2 a b)) (v_le_one_of_mem_KGL hc) i j
  rw [← hid, Matrix.sub_apply] at this
  exact this

end GlobalTheory.CongConj

theorem GlobalTheory.congConj_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w (n := m) → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  intro E _ _ w m k c N hc
  constructor
  · intro h
    have h2 := GlobalTheory.CongConj.conj_imp k (inv_mem hc) h
    simpa [mul_assoc] using h2
  · exact GlobalTheory.CongConj.conj_imp k hc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIffStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w (n := m) → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  first | exact @GlobalTheory.congConj_iff | exact GlobalTheory.congConj_iff | (intros; apply GlobalTheory.congConj_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_eval_regular_at_fieldPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z),
      ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k,
        (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧
        ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u →
          ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  intro F _ Y Z _ k _ w
  set z := w (IsLocalRing.closedPoint k) with hz
  let ι := algebraMap (Z.presheaf.stalk z) Z.functionField
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  let e : Z.presheaf.stalk z ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let s : Z.presheaf.stalk z →+* k := (Scheme.stalkClosedPointTo (R := .of k) w).hom
  haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w
  have he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a := fun a => e.symm_apply_eq.2 rfl
  refine ⟨s.comp e.symm.toRingHom, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩
    change s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _
    rw [he]
    constructor
    · intro h0
      exact ⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [← hι hba]
      exact (hb.map s).ne_zero
  · intro q _ u ⟨a, ha⟩
    subst ha
    have hm := functionFieldMap_algebraMap q z a
    refine ⟨⟨_, hm.symm⟩, ?_⟩
    have h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) =
        ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩ := Subtype.ext hm
    change s (e.symm _) = _
    rw [h1, he]
    have hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z) := by
      conv_lhs => rw [← spMap_stalkClosedPointTo w]
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
      congr 1
      rw [spMap, spMap, ← Spec.map_comp]
      rfl
    have hv := val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a
    exact hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z), ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k, (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧ ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u → ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  first | exact @GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | exact GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | (intros; apply GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncSameDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    resG X h2 (resG X h1 z) = resG X (h2.trans h1) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_elim {X : Scheme.{0}} {U W : X.Opens} (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (o : Option (Fin d)) : resG X h (o.elim 1 t) = o.elim 1 (fun a => resG X h (t a)) := by
  cases o <;> simp

theorem relSnc_of_sameDiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ)
    (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec),
    RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  intro R _ X f d s L σ L' σ' hR hL' hS
  refine ⟨hL', fun x => ?_⟩
  obtain ⟨C, hxC⟩ := hR.chart x
  choose U a b ha hb v hxU hv using fun i => hS i x
  let V : X.Opens := C.U ⊓ ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hxV : x ∈ V := ⟨hxC, Set.mem_iInter.2 hxU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWC : W ≤ C.U := fun y hy => (hWV hy).1
  have hWU : ∀ i, W ≤ U i := fun i y hy => Set.mem_iInter.1 (hWV hy).2 i
  have hWca : ∀ i, W ≤ (L i).U (C.c i) ⊓ (L i).U (a i) := fun i => le_inf (hWC.trans (C.le i)) ((hWU i).trans (ha i))
  let G : ∀ i, Γ(X, W)ˣ := fun i => Units.map (resG X (hWca i)).toMonoidHom ((L i).g (C.c i) (a i)) *
    Units.map (resG X (hWU i)).toMonoidHom (v i)
  refine ⟨{
    U := W
    affine := hW
    t := fun j => resG X hWC (C.t j)
    etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f C.U W hWC d C.t C.affine hW C.etale
    c := b
    le := fun i => (hWU i).trans (hb i)
    e := C.e
    inj := C.inj
    u := fun i => Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹
    eq := fun i => ?_ }, hxW⟩

  have h1 := congrArg (resG X hWC) (C.eq i)
  rw [resG_resG', map_mul, resG_elim] at h1

  have h2 := congrArg (resG X (hWca i)) ((σ i).compat (C.c i) (a i))
  simp only [resG_resG', map_mul] at h2

  have h3 := congrArg (resG X (hWU i)) (hv i)
  simp only [resG_resG', map_mul] at h3
  have hG : (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * (G i : Γ(X, W)) = 1 := Units.inv_mul _
  have hG' : (G i : Γ(X, W)) = resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) *
      resG X (hWU i) (v i : Γ(X, U i)) := by
    simp only [G, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  show _ = ((Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * _
  rw [Units.val_mul, Units.coe_map]
  rw [hG'] at hG
  linear_combination (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h1 - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h2
    - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) * h3
    - resG X (le_trans (hWU i) (hb i)) ((σ' i).f (b i)) * hG

end GlobalTheory.LogPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrised
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.ClSumParam

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, _root_.mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem rep_mk (θ : G →* G) (x : G) : ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g :=
  (twCl_eq_iff θ _ _).1 (Quot.out_eq (Quot.mk _ x : TwCl θ)).symm

theorem clSum_eq_finsum_param : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G)
    (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) →
    (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) →
    (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) →
    clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  intro G _ _ θ Kg S f C ι N hιS hsurj hinj hSinv horb hN
  let φ : C → TwCl θ := fun c => Quot.mk _ (ι c)
  have hφinj : Function.Injective φ := fun c c' h => hinj c c' ((twCl_eq_iff θ _ _).1 h)
  set F : TwCl θ → ℂ := fun c => if c.rep ∈ S then (fun _ => (1 : ℂ)) c.rep * twOrb θ Kg c.rep f else 0 with hF
  have hsupp : Function.support F ⊆ Set.range φ := by
    intro c hc
    by_contra hnot
    apply hc
    have : c.rep ∉ S := by
      intro hrep
      obtain ⟨c', g, hg⟩ := hsurj _ hrep
      apply hnot
      refine ⟨c', ?_⟩
      have h1 : (Quot.mk _ (ι c') : TwCl θ) = Quot.mk _ c.rep := (twCl_eq_iff θ _ _).2 ⟨g, hg⟩
      exact h1.trans (Quot.out_eq c)
    simp [F, this]
  have hcomp : ∀ c, F (φ c) = N c := by
    intro c
    obtain ⟨g, hg⟩ := rep_mk θ (ι c)
    have hmem : TwCl.rep (θ := θ) (φ c) ∈ S := by
      show TwCl.rep (θ := θ) (Quot.mk _ (ι c)) ∈ S
      rw [hg, hSinv]; exact hιS c
    simp only [F, if_pos hmem, one_mul]
    show twOrb θ Kg (TwCl.rep (θ := θ) (Quot.mk _ (ι c))) f = N c
    rw [hg, horb, hN]
  unfold clSum
  show ∑ᶠ c, F c = _
  rw [← finsum_congr hcomp, ← finsum_mem_range hφinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp,
    finsum_mem_support]

end GlobalTheory.BCT.ClSumParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrisedStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G) (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) → (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) → (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) → clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  first | exact @GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | exact GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | (intros; apply GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem ev_int_exsplit {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).eventually

theorem coeff_zero_ne_zero_of_mem_ell {E : Type} [Field E] [NumberField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨hmon, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hne : P.map τ ≠ 0 := (hmon.map τ).ne_zero
  have hr : (0 : ℂ) ∈ (P.map τ).roots := by
    rw [mem_roots hne, IsRoot.def, eval_map, eval₂_at_zero, h0, map_zero]
  have := hroots τ 0 hr
  simp at this

theorem exists_mat_charpoly {E : Type} [Field E] {n : ℕ} {P : E[X]} (hmon : P.Monic) (hdeg : P.natDegree = n) :
    ∃ M : Matrix (Fin n) (Fin n) E, M.charpoly = P := by
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have hdim : pb.dim = n := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix pb.basis pb.gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon]

theorem exists_int_charpoly_atPl_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ _ n _ P hP
  obtain ⟨M, hM⟩ := exists_mat_charpoly hP.1 hP.2.1
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (coeff_zero_ne_zero_of_mem_ell hP)
  have hev1 : ∀ᶠ w : Pl E in cofinite, ∀ ij : Fin n × Fin n,
      algebraMap E (w.adicCompletion E) (M ij.1 ij.2) ∈ w.adicCompletionIntegers E :=
    Filter.eventually_all.2 fun ij => ev_int_exsplit (M ij.1 ij.2)
  have hev2 := ev_int_exsplit (E := E) M.det⁻¹
  filter_upwards [hev1, hev2] with w hent hinv hs
  let N : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨_, hent (i, j)⟩
  have hN : (Ov E w).subtype.mapMatrix N = M.map (algebraMap E (w.adicCompletion E)) := by
    ext i j; rfl
  have hdetN : ((N.det : Ov E w) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) M.det := by
    have := RingHom.map_det (Ov E w).subtype N
    rw [hN] at this
    exact this.trans (RingHom.map_det _ M).symm
  have hu : IsUnit N.det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    change ((N.det : Ov E w) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) M.det⁻¹ = 1
    rw [hdetN, ← map_mul, mul_inv_cancel₀ hdet, map_one]
  let g : GL (Fin n) (Ov E w) := ((Matrix.isUnit_iff_isUnit_det N).2 hu).unit
  have hmemU : bc (Ov E w).subtype g ∈ UL n w := by
    simp only [UL, if_pos hs]; exact Subgroup.mem_top _
  refine ⟨⟨_, hmemU⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    exact ⟨g, rfl⟩
  · change ((Ov E w).subtype.mapMatrix (g : Matrix (Fin n) (Fin n) (Ov E w))).charpoly = atPl w P
    rw [IsUnit.unit_spec, hN, Matrix.charpoly_map, hM]

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_integral_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.BCT.exists_int_charpoly_atPl_split | exact GlobalTheory.BCT.exists_int_charpoly_atPl_split | (intros; apply GlobalTheory.BCT.exists_int_charpoly_atPl_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraFurther
namespace GlobalTheory.MulVecZeroDenominator

private lemma mulVec_eq_zero_of_map_mulVec_eq_zero {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {m c : ℕ} (D : Matrix (Fin m) (Fin c) O) (x : Fin c → L) (v : Fin c → O)
    (d : O) (hv : ∀ i, algebraMap O L (v i) = d • x i)
    (hD : Matrix.mulVec (Matrix.map D (algebraMap O L)) x = 0) : Matrix.mulVec D v = 0 := by
  funext i
  apply IsFractionRing.injective O L
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  have hvx : (algebraMap O L ∘ v) = d • x := funext hv
  rw [hvx, Matrix.mulVec_smul, hD, smul_zero, Pi.zero_apply]

private lemma exists_common_denominator_divisor {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {c : ℕ} (x : Fin c → L) :
    ∃ (d : O) (v : Fin c → O), algebraMap O L d ≠ 0 ∧ ∀ i, algebraMap O L (v i) = d • x i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose v hv using hd
  exact ⟨d, v, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hv⟩

theorem target : ∀ {O L : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field L] [inst_3 : Algebra O L] [IsFractionRing O L] {a b c : ℕ} (B : GlobalTheory.WachPlace.Mx O a c) (C : GlobalTheory.WachPlace.Mx O b c), (∀ (v : Fin c → O), Matrix.mulVec B v = (0 : Fin a → O) → Matrix.mulVec C v = (0 : Fin b → O) → v = (0 : Fin c → O)) → ∀ (x : Fin c → L), Matrix.mulVec (Matrix.map B (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin a → L) → Matrix.mulVec (Matrix.map C (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin b → L) → x = (0 : Fin c → L) := by
  intro O L _ _ _ _ _ a b c B C h x hB hC
  obtain ⟨d, v, hd, hv⟩ := exists_common_denominator_divisor (O := O) x
  have hv0 : v = 0 := h v (mulVec_eq_zero_of_map_mulVec_eq_zero B x v d hv hB) (mulVec_eq_zero_of_map_mulVec_eq_zero C x v d hv hC)
  funext i
  have hi := hv i
  rw [hv0, Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd

end GlobalTheory.MulVecZeroDenominator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwist
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FullRankSum

theorem joint_inj {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] {a b c : ℕ}
    (B : Mx O a c) (C : Mx O b c) (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) (x : Fin c → L)
    (hB : (B.map (algebraMap O L)).mulVec x = 0) (hC : (C.map (algebraMap O L)).mulVec x = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6; revert O L h_2 h_3 h_4 h_5 h_6 a b c B C h x hB hC; exact @_root_.GlobalTheory.MulVecZeroDenominator.target)
  | exact @_root_.GlobalTheory.MulVecZeroDenominator.target
  | exact _root_.GlobalTheory.MulVecZeroDenominator.target
  | (apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecZeroDenominator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecZeroDenominator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecZeroDenominator.target ..)

theorem exists_equiv {L : Type} [Field L] {n : ℕ} (B : Mx L n (n + 1)) (C : Mx L 1 (n + 1))
    (h : ∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) :
    ∃ e : (Fin (n + 1) → L) ≃ₗ[L] (Fin n → L) × (Fin 1 → L), ∀ v, e v = (B.mulVec v, C.mulVec v) := by
  let φ : (Fin (n + 1) → L) →ₗ[L] (Fin n → L) × (Fin 1 → L) := (Matrix.toLin' B).prod (Matrix.toLin' C)
  have hi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  exact ⟨φ.linearEquivOfInjective hi (by simp), fun v => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l}

theorem tw_mulVec {a b : ℕ} {r : ↥(GK K) →* GL (Fin b) ↥(OL LL)} {r' : ↥(GK K) →* GL (Fin a) ↥(OL LL)}
    {A : Mx ↥(OL LL) a b} (hA : Tw r r' A) (g : ↥(GK K)) (y : Fin b → ↥LL.1) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
      repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := by
  rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
    hA g]

theorem matGood_sum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  intro l _ P AI T K LL f n emb r ρ r₂ U U' B C hr hρ hB hC hinj
  obtain ⟨_, -, -, -, -, -, hF⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨e, he⟩ := exists_equiv (B.map (algebraMap ↥(OL LL) ↥LL.1)) (C.map (algebraMap ↥(OL LL) ↥LL.1))
    (joint_inj B C hinj)
  have hq : ∀ g v, e (repOf r₂ g v) = (repOf r g (e v).1, repOf ρ g (e v).2) := fun g v => by
    rw [he, he, tw_mulVec hB, tw_mulVec hC]
  obtain ⟨-, hc, hm⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T K LL _ (repOf r₂) _ (repOf r) _ (repOf ρ) e hq
  refine ⟨fun a b => ?_, hc.2 ⟨hr.2.1, hρ.2.1⟩, fun i τ hτ a => ?_⟩
  · have c1 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) := LinearMap.continuous_on_pi _
    have c2 : Continuous (e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _) := LinearMap.continuous_on_pi _
    have d1 : Continuous fun g => repOf r g (e (Pi.single b 1)).1 := (latOf r hr.1).cont _
    have d2 : Continuous fun g => repOf ρ g (e (Pi.single b 1)).2 := (latOf ρ hρ.1).cont _
    have d := (continuous_apply a).comp ((c1.comp d1).add (c2.comp d2))
    refine d.congr fun g => ?_
    have : repOf r₂ g (Pi.single b 1) = e.symm (repOf r g (e (Pi.single b 1)).1, 0) +
        e.symm (0, repOf ρ g (e (Pi.single b 1)).2) := by
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, ← hq, e.symm_apply_apply]
    have h2 := congrFun this a
    rw [repOf_apply, Matrix.mulVec_single_one] at h2
    exact h2.symm
  · rw [hm, hr.2.2 i τ hτ a, hρ.2.2 i τ hτ a, Multiset.count_add]
    push_cast
    rfl

end GlobalTheory.WachPlace.FullRankSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatGoodOfBlockExtensionTwistStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGood_of_block_extension_twist : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (ρ : ↥(GK K) →* GL (Fin 1) ↥(OL LL)) (r₂ : ↥(GK K) →* GL (Fin (n + 1)) ↥(OL LL)) (U U' : ZMod f → Multiset ℤ) (B : Mx ↥(OL LL) n (n + 1)) (C : Mx ↥(OL LL) 1 (n + 1)), MatGood P emb r U → MatGood P emb ρ U' → Tw r₂ r B → Tw r₂ ρ C → (∀ v, B.mulVec v = 0 → C.mulVec v = 0 → v = 0) → MatGood P emb r₂ (fun i => U i + U' i) := by
  first | exact @GlobalTheory.WachPlace.FullRankSum.matGood_sum | exact GlobalTheory.WachPlace.FullRankSum.matGood_sum | (intros; apply GlobalTheory.WachPlace.FullRankSum.matGood_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundFamilyOfIsCompact
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma le_fintype_sum_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.exists_bound_smooth_data : ∀ {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) →
    ContDiffOn ℝ ∞ ρ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ K, |ρ v| ≤ C ∧
      (∀ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ ≤ C) ∧
      (∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ ≤ C) ∧
      ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ ≤ C := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ
  let F : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => |ρ v|
    + ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖
    + ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖
    + ∑ a, ∑ b, ∑ i, ∑ j,
        ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖
  have hFc : ContinuousOn F K := by
    intro v hv
    have hvU : v ∈ U := hKU hv
    have hρv : ContDiffAt ℝ ∞ ρ v := hρ.contDiffAt (hU.mem_nhds hvU)
    have h1 : ContinuousAt ρ v := hρv.continuousAt
    have h2 : ∀ b, ContinuousAt
        (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x (_root_.GlobalTheory.GoodMetric.coordVec b)) v :=
      fun b => continuousAt_dbar_ofReal_of_contDiffAt_one (hρv.of_le (by simp)) _
    have h3 : ∀ a i j, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) i j) v := fun a i j =>
      ((hG₀ v hvU).1.conn (j := 0) (hG₀ v hvU).2 (by simp)
        (_root_.GlobalTheory.GoodMetric.coordVec a) i j).continuousAt
    have h4 : ∀ a b i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G₀ x
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j) v :=
      fun a b i j =>
      ((hG₀ v hvU).1.curv (j := 0) (hG₀ v hvU).2
        (by rw [zero_add]; exact WithTop.coe_le_coe.2 le_top)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j).continuousAt
    apply ContinuousAt.continuousWithinAt
    simp only [F]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFc
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  have hFv : F v ≤ max C 0 := ((le_abs_self _).trans (hC v hv)).trans (le_max_left _ _)
  have hA : 0 ≤ |ρ v| := abs_nonneg _
  have hB : 0 ≤ ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v
      (_root_.GlobalTheory.GoodMetric.coordVec b)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC3 : 0 ≤ ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  have hD : 0 ≤ ∑ a, ∑ b, ∑ i, ∑ j,
      ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [F] at hFv
  refine ⟨by linarith, fun b => ?_, fun a i j => ?_, fun a b i j => ?_⟩
  · have := le_fintype_sum_of_nonneg
      (fun b => ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖)
      (fun _ => norm_nonneg _) b
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun a => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun b => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) b
    have e4 := le_fintype_sum_of_nonneg
      (fun a => ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMulEqZeroImp
namespace GlobalTheory.TraceMulVanishing

theorem trace_mul_eq_zero_imp {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [IsReduced A] (x : A)
    (h : ∀ z : A, (Algebra.trace F A : A → F) (x * z) = (0 : F)) : x = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one] at hy

  have h1 : x ^ (n + 1) = x ^ (n + 1) * (x * y) := by
    calc x ^ (n + 1) = x * x ^ n := by rw [pow_succ']
      _ = x * (x ^ (n + 1) * y) := by rw [hy]
      _ = x ^ (n + 1) * (x * y) := by ring
  have h2 : ∀ j : ℕ, x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ (x * y) j, ← mul_assoc, ← ih]; exact h1
  have h3 : x ^ (n + 1) = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by
    calc x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ (n + 1) := h2 (n + 1)
      _ = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by rw [mul_pow]; ring
  have he : IsIdempotentElem (x ^ (n + 1) * y ^ (n + 1)) := by
    unfold IsIdempotentElem
    calc x ^ (n + 1) * y ^ (n + 1) * (x ^ (n + 1) * y ^ (n + 1))
        = (x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1)) * y ^ (n + 1) := by ring
      _ = x ^ (n + 1) * y ^ (n + 1) := by rw [← h3]
  have htr : Algebra.trace F A (x ^ (n + 1) * y ^ (n + 1)) = 0 := by
    have := h (x ^ n * y ^ (n + 1))
    rwa [show x * (x ^ n * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) by ring] at this
  have hl : IsIdempotentElem (Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1))) := he.map _
  have hz : Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1)) = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hl).1 (by rw [← Algebra.trace_apply]; exact htr)
  have he0 : x ^ (n + 1) * y ^ (n + 1) = 0 := by
    have := congrArg (fun f : Module.End F A => f 1) hz
    simpa using this
  have hxn : x ^ (n + 1) = 0 := by
    rw [h3, mul_assoc, he0, mul_zero]
  exact IsReduced.eq_zero x ⟨n + 1, hxn⟩

end GlobalTheory.TraceMulVanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegral
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.GramUnit

theorem isReduced_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (P : F[X]) (hP : P.Separable) (hu : aeval u P = 0) (hadj : Algebra.adjoin F {u} = ⊤) :
    IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨N, hN⟩ := hx
  have hxmem : x ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have hdvdP : minpoly F u ∣ P := minpoly.dvd F u hu
  have hsq : Squarefree (minpoly F u) := (hP.of_dvd hdvdP).squarefree
  have hfN : minpoly F u ∣ f ^ N := minpoly.dvd F u (by rw [map_pow]; exact hN)
  obtain ⟨g, hg⟩ := hsq.isRadical N f hfN
  subst hg
  change aeval u (minpoly F u * g) = 0
  rw [map_mul, minpoly.aeval, zero_mul]

theorem eq_zero_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    [IsReduced A] (x : A) (h : ∀ z, Algebra.trace F A (x * z) = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7; revert F A h_2 h_3 h_4 h_5 h_6 h_7 x h; exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp)
  | exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | (apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp ..)

theorem det_gram_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) [IsReduced B.A] {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (hβ : IsUnit β) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set y := ∑ i, v i • b i with hy
  have hlin : ∀ z, B.herm β y z = ∑ i, v i * B.herm β (b i) z := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.UnitLemma.InvAlg.herm, hy, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hj : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    rw [hlin]
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct] using this
  have hsemi : ∀ (d : K.E) (a : B.A), B.σ (d • a) = K.c d • B.σ a := by
    intro d a
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hall : ∀ z, Algebra.trace K.E B.A (β * y * z) = 0 := by
    intro z
    have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hsemi]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    have := hj j
    simp only [GlobalTheory.UnitLemma.InvAlg.herm] at this
    rw [this, mul_zero]
  have hβy : β * y = 0 := eq_zero_of_trace_mul (β * y) hall
  have hy0 : y = 0 := by
    obtain ⟨u, rfl⟩ := hβ
    have := congrArg (fun t => ((u⁻¹ : B.Aˣ) : B.A) * t) hβy
    simpa [← mul_assoc] using this
  exact hv0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hy0))

end GlobalTheory.TwLat.GramUnit


open GlobalTheory.TwLat.GramUnit in
theorem GlobalTheory.TwLat.isUnit_gram_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b u P hP hu hadj β hβ
  haveI : IsReduced B.A := isReduced_of_adjoin u P hP hu hadj
  have hd := det_gram_ne_zero B b β hβ
  have hmap : GlobalTheory.TwLat.gram e b β = (Matrix.of fun i j => B.herm β (b i) (b j)).map e := by
    ext i j; rfl
  rw [hmap, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := RingHom.map_det (e : K.E →+* w.adicCompletion E) (Matrix.of fun i j => B.herm β (b i) (b j))
  rw [show ((Matrix.of fun i j => B.herm β (b i) (b j)).map e) =
    (e : K.E →+* w.adicCompletion E).mapMatrix (Matrix.of fun i j => B.herm β (b i) (b j)) from rfl, ← this]
  exact (map_ne_zero_iff _ e.injective).mpr hd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegralStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_element_basis_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  first | exact @GlobalTheory.TwLat.isUnit_gram_of_separable | exact GlobalTheory.TwLat.isUnit_gram_of_separable | (intros; apply GlobalTheory.TwLat.isUnit_gram_of_separable <;> assumption)
end
end
