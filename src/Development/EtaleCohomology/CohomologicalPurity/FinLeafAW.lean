module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.KummerTheory.CupAWCut
public import Development.EtaleCohomology.EtaleSheaves.AffinePf
public import Development.EtaleCohomology.EtaleSheaves.StalkGermPf
public import Development.EtaleCohomology.EtaleSheaves.TorEtPf
public import Development.EtaleCohomology.TateTwists.conePf
public import Development.EtaleCohomology.TateTwists.ColumnOf
public import Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart
public import Development.EtaleCohomology.CohomologicalPurity.LeafAWCutTw

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorCycleLocallyLowersTopDegreeOfRowExact
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorCyclesLocallyLiftOfRowExactAndDescent
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorComplexLocallyExactOfLiftedSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem stair_loc_bind (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hSP⟩ := hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => Classical.choose (h V g (hSP V g hg))), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => (Classical.choose_spec (h V g (hSP V g hg))).1)
  · rintro W f ⟨V, k, g, hg, hk, rfl⟩
    exact (Classical.choose_spec (h V g (hSP V g hg))).2 W k hk

theorem stair_loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem stair_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have := congrArg (fun m => (ModuleCat.Hom.hom m) y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem stair_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  simp [Sec.res]

def EtaleTensorCyclesLocallyLiftOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x)

theorem etale_tensor_complex_locally_exact_of_lifted_sections (hL : EtaleTensorCyclesLocallyLiftOfFlatBounded) : EtaleTensorComplexLocallyExactOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w U y hy
  refine stair_loc_bind U _ _ (hτ.1 U w y) ?_
  rintro V g ⟨x, hx⟩
  have hcyc : Sec.map (T.sc w).g (τ.lift V w x) = 0 := by
    have h1 := stair_map_res (T.sc w).g g y
    have h2 : Sec.map (T.sc w).g (τ.lift V w x) = Sec.map (T.sc w).g (Sec.res g y) := congrArg _ hx
    refine h2.trans (h1.trans ?_)
    rw [hy]
    simp
  refine stair_loc_mono V _ _ (hL R a b τ hτ hJ hC w V x hcyc) ?_
  rintro W k ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact hz.trans ((congrArg (Sec.res k) hx).trans (stair_res_res k g y))

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

theorem stair_tens_top {R : Type} [CommRing R] {C J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens C J U w) :
    ∃ s : ℤ, ∀ p, s < p.1.1 → x p = 0 := by
  classical
  refine ⟨((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ), fun p hp => ?_⟩
  by_contra h
  have hm : p ∈ DFinsupp.support x := (DFinsupp.mem_support_iff).2 h
  have h1 : p.1.1.toNat ≤ (DFinsupp.support x).sup fun p => p.1.1.toNat := Finset.le_sup (f := fun p => p.1.1.toNat) hm
  have h2 : p.1.1 ≤ (p.1.1.toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((p.1.1.toNat : ℕ) : ℤ) ≤ (((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ) : ℤ) := by exact_mod_cast h1
  omega

theorem stair_loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem stair_sec_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) (U : Scheme.{0}) (y : Sec F U) : y = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have := congrArg (fun m : F ⟶ F => (m.hom.app (op U)).hom y) h
  simpa using this

theorem stair_tens_low {R : Type} [CommRing R] {C J : Cx R} (a : ℤ) [C.IsStrictlyGE a] {U : Scheme.{0}} {w : ℤ}
    (x : Tens C J U w) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (hp : p.1.1 < a) : x p = 0 := by
  have hz := C.isZero_of_isStrictlyGE a p.1.1 hp
  have key : ∀ y : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U, y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul u v => rw [stair_sec_zero hz U u, TensorProduct.zero_tmul]
    | add u v hu hv => rw [hu, hv, add_zero]
  exact key _

theorem stair_fg_zero {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.sc w).X₁ V) :
    Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = 0 := by
  have h1 : Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = ((((T.sc w).f ≫ (T.sc w).g).hom.app (op V)).hom z) := rfl
  rw [h1, (T.sc w).zero]
  rfl

def stair_row (R : Type) [CommRing R] (C J : Cx R) : Prop :=
  ∀ (s t : ℤ) (V : Scheme.{0}) (x : Sec (C.X s) V ⊗[ULift.{1} R] Sec (J.X t) V),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x = 0 →
    Loc V fun W k => ∃ z : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] Sec (J.X t) W,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id z =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom x

def EtaleTensorWithFlatPreservesLocalExactness : Prop :=
  ∀ (R : Type) [CommRing R] {C J : Cx R}, (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    stair_row R C J

def EtaleTensorCycleLocallyLowersTopDegree : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → stair_row R C J →
    ∀ (w s : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, s < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ x' : Tens C J V w, (∀ p, s - 1 < p.1.1 → x' p = 0) ∧
        ∃ z : Sec (T.sc w).X₁ V, τ.lift V w x' = Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)

theorem etale_tensor_cycles_locally_lift_of_row_exact_and_descent (hA : EtaleTensorWithFlatPreservesLocalExactness)
    (hS : EtaleTensorCycleLocallyLowersTopDegree) : EtaleTensorCyclesLocallyLiftOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC
  have hrow := hA R hJ hC
  have key : ∀ n : ℕ, ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, a - 1 + n < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x) := by
    intro n
    induction n with
    | zero =>
      intro w U x hx _
      have h0 : x = 0 := by
        ext p
        by_cases hp : p.1.1 < a
        · simpa using stair_tens_low a x p hp
        · simpa using hx p (by push_cast; omega)
      refine stair_loc_top _ _ fun V g => ⟨0, ?_⟩
      simp [h0] <;> rfl
    | succ n ih =>
      intro w U x hx hc
      refine stair_loc_bind U _ _ (hS R τ hτ hrow w (a - 1 + (n + 1 : ℕ)) U x hx hc) ?_
      rintro V g ⟨x', hx', z, hz⟩
      have hc' : Sec.map (T.sc w).g (τ.lift V w x') = 0 := by
        rw [hz]
        have e1 : Sec.map (T.sc w).g (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
            Sec.map (T.sc w).g (Sec.res g (τ.lift U w x)) - Sec.map (T.sc w).g (Sec.map (T.sc w).f z) := by
          exact map_sub _ _ _
        rw [e1, stair_fg_zero, sub_zero]
        exact (stair_map_res (T.sc w).g g (τ.lift U w x)).trans ((congrArg (Sec.res g) hc).trans (map_zero _))
      refine stair_loc_mono V _ _ (ih w V x' (fun p hp => hx' p (by push_cast at hp ⊢; omega)) hc') ?_
      rintro W k ⟨z', hz'⟩
      refine ⟨z' + Sec.res k z, ?_⟩
      have e2 : Sec.map (T.sc w).f (z' + Sec.res k z) = Sec.map (T.sc w).f z' + Sec.map (T.sc w).f (Sec.res k z) := by
        simp only [Sec.map, map_add (f := _)]
      have e3 : Sec.res k (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
          Sec.res k (Sec.res g (τ.lift U w x)) - Sec.res k (show Sec (T.X w) V from Sec.map (T.sc w).f z) := by
        exact map_sub _ _ _
      rw [e2, hz', hz, e3, stair_map_res, stair_res_res]
      exact sub_add_cancel _ _
  intro w U x hx
  obtain ⟨s, hs⟩ := stair_tens_top x
  exact key (s - (a - 1)).toNat w U x (fun p hp => hs p (by omega)) hx

end LateralTheory.EtaleFoundations
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

abbrev TensorDegreeIndex (w : ℤ) : Type := {p : ℤ × ℤ // p.1 + p.2 = w}

abbrev TensorDegreeSummand {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w : ℤ)
    (p : TensorDegreeIndex w) : Type 1 :=
  Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U

def stD {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') :
    Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
      ((p.1.1.negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

theorem stD_lof {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (a b : ℤ) (hab : a + b = w)
    (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    stD C J U w w' h (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w) (TensorDegreeSummand C J U w) ⟨(a, b), hab⟩ v) =
      DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a + 1, b), by omega⟩
          (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) +
        (a.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a, b + 1), by omega⟩
          (TensorProduct.map LinearMap.id ((J.d b (b + 1)).hom.app (op U)).hom v) := by
  unfold stD
  rw [DirectSum.toModule_lof]
  rfl

theorem lift_lof {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : TensorDegreeIndex w)
    (v : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) : τ.lift U w (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w) (TensorDegreeSummand C J U w) p v) =
      TensorProduct.lift (τ.mul U p.1.1 p.1.2 w p.2) v := by
  unfold Pair.lift
  rw [DirectSum.toModule_lof]

theorem stD_lift {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : τ.lift U w' (stD C J U w w' h y) = Sec.map (T.d w w') (τ.lift U w y) := by
  subst h
  have key : (τ.lift U (w + 1)).comp (stD C J U w (w + 1) rfl) =
      ((T.d w (w + 1)).hom.app (op U)).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [stD_lof, map_add (f := _), map_zsmul, lift_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    have := τ.leibniz U a b w hab u v
    rw [Units.smul_def] at this
    exact this.symm
  exact LinearMap.congr_fun key y

theorem stD_res {R : Type} [CommRing R] (C J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : stD C J V w w' h (Tens.res g w y) = Tens.res g w' (stD C J U w w' h y) := by
  have key : (stD C J V w w' h).comp (Tens.res g w) = (Tens.res g w').comp (stD C J U w w' h) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    have n1 := stair_map_res (C.d a (a + 1)) g u
    have n2 := stair_map_res (J.d b (b + 1)) g v
    simp only [Sec.map, Sec.res] at n1 n2
    simp only [LinearMap.comp_apply]
    rw [Tens.res, Tens.res, DirectSum.lmap_lof, stD_lof, stD_lof, map_add (f := _), map_zsmul, DirectSum.lmap_lof, DirectSum.lmap_lof]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [n1, n2]
  exact LinearMap.congr_fun key y

theorem lift_res {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (y : Tens C J U w) : τ.lift V w (Tens.res g w y) = Sec.res g (τ.lift U w y) := by
  have key : (τ.lift V w).comp (Tens.res g w) = ((T.X w).obj.map g.op).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [Tens.res, DirectSum.lmap_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    exact (τ.nat g _ _ _ p.2 u v).symm
  exact LinearMap.congr_fun key y

theorem lof_reidx {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w' a a' b : ℤ) (ha : a + 1 = a')
    (h1 : a + 1 + b = w') (h2 : a' + b = w') (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a + 1, b), h1⟩
        (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) =
      DirectSum.lof (ULift.{1} R) (TensorDegreeIndex w') (TensorDegreeSummand C J U w') ⟨(a', b), h2⟩
        (TensorProduct.map ((C.d a a').hom.app (op U)).hom LinearMap.id v) := by
  subst ha; rfl

theorem stD_low {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (n : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TensorDegreeIndex w, n < p.1.1 → y p = 0) :
    ∀ q : TensorDegreeIndex w', n + 1 < q.1.1 → stD C J U w w' h y q = 0 := by
  classical
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_of y, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpn : p.1.1 ≤ n := by
    by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hpn
  rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
  · intro he; rw [he] at hq; simp only at hq; omega
  · intro he; rw [he] at hq; simp only at hq; omega

theorem stD_top {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (s : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TensorDegreeIndex w, s < p.1.1 → y p = 0) (h0 : s + (w - s) = w) (h1 : s + 1 + (w - s) = w') :
    stD C J U w w' h y ⟨(s + 1, w - s), h1⟩ =
      TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(s, w - s), h0⟩) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, DirectSum.sum_apply]
  have hz : ∀ p ∈ DFinsupp.support y, p ≠ ⟨(s, w - s), h0⟩ →
      stD C J U w w' h (DirectSum.of (TensorDegreeSummand C J U w) p (y p)) ⟨(s + 1, w - s), h1⟩ = 0 := by
    intro p hp hne
    have hps : p.1.1 < s := by
      have hle : p.1.1 ≤ s := by
        by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exact absurd (Subtype.ext (Prod.ext h' (by have := p.2; simp only at this ⊢; omega))) hne
    obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at hps
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    · intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
    · intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
  by_cases hm : (⟨(s, w - s), h0⟩ : TensorDegreeIndex w) ∈ DFinsupp.support y
  · rw [Finset.sum_eq_single_of_mem _ hm hz]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    intro he; have := congrArg (fun q : TensorDegreeIndex w' => q.1.1) he; simp only at this; omega
  · rw [Finset.sum_eq_zero fun p hp => hz p hp (fun he => hm (he ▸ hp))]
    have : y ⟨(s, w - s), h0⟩ = 0 := by simpa [DFinsupp.mem_support_iff] using hm
    rw [this, map_zero]

theorem next_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {U : Scheme.{0}} (y : Sec (T.X w) U)
    (h : Sec.map (T.sc w).g y = 0) : Sec.map (T.d w (w + 1)) y = 0 := by
  change Sec.map (T.d w ((ComplexShape.up ℤ).next w)) y = 0 at h
  rwa [CochainComplex.next ℤ w] at h

theorem prev_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.X (w - 1)) V) :
    ∃ z' : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z' = Sec.map (T.d (w - 1) w) z := by
  change ∃ z' : Sec (T.X ((ComplexShape.up ℤ).prev w)) V, Sec.map (T.d ((ComplexShape.up ℤ).prev w) w) z' = _
  rw [CochainComplex.prev ℤ w]
  exact ⟨z, rfl⟩

theorem etale_tensor_cycle_locally_lowers_top_degree_of_row_exact : EtaleTensorCycleLocallyLowersTopDegree := by
  intro R _ C J T τ hτ hrow w s U x hx hc
  have hc' : τ.lift U (w + 1) (stD C J U w (w + 1) rfl x) = 0 := by
    rw [stD_lift]; exact next_fix T w _ hc
  refine stair_loc_bind U _ _ (hτ.2 U (w + 1) _ hc') ?_
  intro V g hV
  have hy : ∀ p : TensorDegreeIndex w, s < p.1.1 → Tens.res g w x p = 0 := by
    intro p hp; rw [Tens.res, DirectSum.lmap_apply, hx p hp, map_zero]
  have hrow0 : TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id
      (Tens.res g w x ⟨(s, w - s), by omega⟩) = 0 := by
    rw [← stD_top C J V w (w + 1) rfl s _ hy (by omega) (by omega), stD_res, hV]; rfl
  refine stair_loc_mono V _ _ (hrow s (w - s) V _ hrow0) ?_
  rintro W k ⟨e, he⟩
  have hlow : ∀ q : TensorDegreeIndex (w - 1), s - 1 < q.1.1 →
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e) q = 0 := by
    intro q hq
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    intro he'; rw [he'] at hq; simp only at hq; omega
  refine ⟨Tens.res k w (Tens.res g w x) - stD C J W (w - 1) w (by omega)
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e), ?_, ?_⟩
  · intro p hp
    rw [DFinsupp.sub_apply]
    rcases lt_or_eq_of_le (show s ≤ p.1.1 by omega) with hps | hps
    · rw [stD_low C J W (w - 1) w (by omega) (s - 1) _ hlow p (by omega), sub_zero,
        show Tens.res k w (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map k.op).hom
          ((J.X p.1.2).obj.map k.op).hom (Tens.res g w x p) from DirectSum.lmap_apply _ _ _, hy p hps, map_zero]
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at hps
      subst hps
      obtain rfl : b = w - s := by simp only at hab; omega
      rw [stD_lof, lof_reidx C J W w (s - 1) s (w - s) (by omega) _ (by omega), DFinsupp.add_apply, DFinsupp.smul_apply,
        DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero,
        sub_eq_zero]
      · exact he.symm
      · intro he'; have := congrArg (fun q : TensorDegreeIndex w => q.1.1) he'; simp only at this; omega
  · obtain ⟨z', hz'⟩ := prev_fix T w (τ.lift W (w - 1)
      (DirectSum.lof (ULift.{1} R) (TensorDegreeIndex (w - 1)) (TensorDegreeSummand C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e))
    refine ⟨z', ?_⟩
    rw [map_sub, lift_res, lift_res, stair_res_res, stD_lift]
    exact congrArg (fun t => _ - t) hz'.symm

end LateralTheory.EtaleFoundations
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorComplexUniversalOfDegreewise
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorUniversalPropertyOfDegreewise
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairUniversalProperty
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensUnivPf

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  have := congrArg (fun φ : F ⟶ F => (φ.hom.app (op U)).hom x) h1
  simpa using this

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

def postPair {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (μ.mul _ s t w h a b)) ((u.f w).hom.naturality g.op)).symm
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = Sec.map (u.f (w+1)) (Sec.map (K.d w (w+1)) (μ.mul U s t w h a b)) := by
      rw [← secMap_comp, ← secMap_comp, u.comm]
    change Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz]
    simp [map_add (f := _)]

theorem part3 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {K' : Cx R} (u : K ⟶ K') :
    ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u :=
  ⟨postPair τ u, fun U s t w h a b => rfl⟩

theorem sep {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sep_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  exact sep S hS y z hh

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h _ _).trans (h _ _).symm

theorem lift_ind {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (V : Scheme.{0}) (w : ℤ)
    (P : Sec (K.X w) V → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V), P (μ.mul V s t w h a b))
    (x : Tens I J V w) : P (μ.lift V w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using h0
  | of p t =>
    simp only [Pair.lift]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa using hm p.1.1 p.1.2 p.2 a b
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb

theorem part2 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) :
    I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0 := by
  intro hI hJ
  rw [CochainComplex.isStrictlyGE_iff]
  intro w hw
  apply isZero_of_sec
  intro U y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hh V g hg
  rw [← hx]
  simp only [map_zero]
  refine lift_ind τ V w (fun z => z = 0) rfl (fun a b ha hb => by rw [ha, hb]; simp) ?_ x
  intro s t h a b
  rcases (show s < 0 ∨ t < 0 by omega) with hs | ht
  · rw [sec_eq_zero_of_isZero (I.isZero_of_isStrictlyGE 0 s hs) a]; simp
  · rw [sec_eq_zero_of_isZero (J.isZero_of_isStrictlyGE 0 t ht) b]; simp

theorem uniq {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u v : K ⟶ K')
    (hu : τ.Compat ν f g u) (hv : τ.Compat ν f g v) : u = v := by
  ext w U y
  obtain ⟨U⟩ := U
  change Sec.map (u.f w) y = Sec.map (v.f w) y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  have nu : ∀ (φ : K ⟶ K') (z : Sec (K.X w) U), Sec.res e (Sec.map (φ.f w) z) = Sec.map (φ.f w) (Sec.res e z) :=
    fun φ z => (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) ((φ.f w).hom.naturality e.op)).symm
  rw [nu, nu, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (u.f w) z = Sec.map (v.f w) z) (by simp) ?_ ?_ x
  · intro a b ha hb
    simp only [Sec.map, map_add (f := _)] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    rw [hu, hv]

theorem nat_sec {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (e : V ⟶ U) (z : Sec F U) :
    Sec.res e (Sec.map φ z) = Sec.map φ (Sec.res e z) :=
  (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) (φ.hom.naturality e.op)).symm

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

theorem secMap_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ a

theorem exists_of_degreewise {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : ∀ w, K.X w ⟶ K'.X w)
    (hm : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (m w) (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)) :
    ∃ u : K ⟶ K', τ.Compat ν f g u := by
  refine ⟨{ f := m, comm' := ?_ }, fun U s t w h a b => hm U s t w h a b⟩
  rintro w _ rfl
  ext U y
  obtain ⟨U⟩ := U
  change Sec.map (K'.d w (w+1)) (Sec.map (m w) y) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) y)
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  rw [nat_sec, nat_sec, nat_sec, nat_sec, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (K'.d w (w+1)) (Sec.map (m w) z) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) z))
    (by simp [Sec.map]) ?_ ?_ x
  · intro a b ha hb
    simp only [secMap_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    have cf : Sec.map (f.f (s+1)) (Sec.map (I.d s (s+1)) a) = Sec.map (I'.d s (s+1)) (Sec.map (f.f s) a) := by
      rw [← secMap_comp, ← secMap_comp, f.comm]
    have cg : Sec.map (g.f (t+1)) (Sec.map (J.d t (t+1)) b) = Sec.map (J'.d t (t+1)) (Sec.map (g.f t) b) := by
      rw [← secMap_comp, ← secMap_comp, g.comm]
    rw [hm, τ.leibniz, secMap_add, secMap_zsmul, hm, hm, ν.leibniz, cf, cg]

end LateralTheory.EtaleFoundations.TensUnivPf

def LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ),
      ∃ m : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
        Sec.map m (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise (hdeg : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists) :
    LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  intro R _ I J K τ hτ
  refine ⟨fun {I' J' K'} ν f g => ?_, LateralTheory.EtaleFoundations.TensUnivPf.part2 τ hτ,
    fun u => LateralTheory.EtaleFoundations.TensUnivPf.part3 τ u⟩
  obtain ⟨u, hu⟩ := LateralTheory.EtaleFoundations.TensUnivPf.exists_of_degreewise τ hτ ν f g
    (fun w => (hdeg R τ hτ ν f g w).choose) (fun U s t w h a b => (hdeg R τ hτ ν f g w).choose_spec U s t h a b)
  exact ⟨u, hu, fun v hv => LateralTheory.EtaleFoundations.TensUnivPf.uniq τ hτ ν f g v u hv hu⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorPairingDegreewiseUniversalOfSheafific
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensUnivDeg

variable {R : Type} [CommRing R]

theorem tens_ind {I J : Cx R} (V : Scheme.{0}) (w : ℤ) (P : Tens I J V w → Prop) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V),
      P (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (a ⊗ₜ b)))
    (x : Tens I J V w) : P x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p t =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact hm p a b
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  | add a b ha hb => exact hadd _ _ ha hb

theorem res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V)) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  classical
  simp [Tens.res, Sec.res]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  simp [Pair.lift]

def Tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Tens I' J' U w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op U)).hom ((g.f p.1.2).hom.app (op U)).hom

theorem tmap_lof {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tmap f g U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I'.X p.1.1) U ⊗[ULift.{1} R] Sec (J'.X p.1.2) U)) p (Sec.map (f.f p.1.1) a ⊗ₜ Sec.map (g.f p.1.2) b) := by
  classical
  simp [Tmap, Sec.map]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => Tens.res (𝟙 U.unop) w x = x) (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb]
    · rw [res_lof]; simp [Sec.res]
  map_comp g h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind _ w (fun x => Tens.res (g ≫ h).unop w x = Tens.res h.unop w (Tens.res g.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    · rw [res_lof, res_lof, res_lof]; simp [Sec.res]

def alpha {I J K : Cx R} (τ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (τ.lift U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => τ.lift V.unop w (Tens.res g.unop w x) = Sec.res g.unop (τ.lift U.unop w x))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, lift_lof, lift_lof, τ.nat]

def beta {I J I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : TP I J w ⟶ (K'.X w).obj where
  app U := ModuleCat.ofHom (ν.lift U.unop w ∘ₗ Tmap f g U.unop w)
  naturality U V e := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine tens_ind U.unop w (fun x => ν.lift V.unop w (Tmap f g V.unop w (Tens.res e.unop w x)) =
        Sec.res e.unop (ν.lift U.unop w (Tmap f g U.unop w x)))
      (by simp) (fun a b ha hb => ?_) (fun p a b => ?_) x
    · simp only [map_add (f := _), ha, hb]
    · rw [res_lof, tmap_lof, tmap_lof, lift_lof, lift_lof, ν.nat, TensUnivPf.nat_sec, TensUnivPf.nat_sec]

theorem alpha_locSurj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology (alpha τ w) where
  imageSieve_mem {U} y := by
    obtain ⟨S, hS, hh⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    obtain ⟨x, hx⟩ := hh V g hg
    exact ⟨x, hx⟩

theorem etale_tensor_pairing_lift_eq_locally_res_eq {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) {U : Scheme.{0}}
    (x y : Tens I J U w) (h : τ.lift U w x = τ.lift U w y) :
    Loc U fun _ g => Tens.res g w x = Tens.res g w y := by
  obtain ⟨S, hS, hh⟩ := hτ.2 U w (x - y) (by rw [map_sub, h, sub_self])
  exact ⟨S, hS, fun V g hg => sub_eq_zero.1 (by rw [← map_sub]; exact hh V g hg)⟩

theorem alpha_locInj {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology (alpha τ w) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨S, hS, hh⟩ := etale_tensor_pairing_lift_eq_locally_res_eq τ hτ w x y h
    exact Scheme.etaleTopology.superset_covering (fun V g hg => hh V g hg) hS

end LateralTheory.EtaleFoundations.TensUnivDeg

open LateralTheory.EtaleFoundations.TensUnivDeg in
theorem LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  have := alpha_locSurj τ hτ w
  have := alpha_locInj τ hτ w
  have hW : Scheme.etaleTopology.W (alpha τ w) := GrothendieckTopology.W_of_isLocallyBijective _ _
  obtain ⟨m, hm⟩ := (hW (K'.X w).obj (K'.X w).property).2 (beta ν f g w)
  refine ⟨⟨m⟩, fun U s t h a b => ?_⟩
  have e := congrArg (fun φ : TP I J w ⟶ (K'.X w).obj => (φ.app (op U)).hom
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)) ⟨(s, t), h⟩ (a ⊗ₜ b))) hm
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  change Sec.map ⟨m⟩ (τ.lift U w _) = (ν.lift U w ∘ₗ Tmap f g U w) _ at e
  rw [lift_lof, LinearMap.comp_apply, tmap_lof, lift_lof] at e
  exact e
end

namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorProductSheafExistsOfComponents
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex
section -- merged from Development.EtaleCohomology.TateTwists.EtaleComplexTensorPairingExists
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

def tensPure {R : Type} [CommRing R] {I J : Cx R} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
    (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)

def EtaleSheafTensorComplexExists : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R)
    (φ : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
      Sec.res g (φ U w x) = φ V w (Tens.res g w x)) ∧
    (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (K.d w (w + 1)) (φ U w (tensPure s t w h a b)) =
        φ U (w + 1) (tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b) +
        s.negOnePow • φ U (w + 1) (tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b))) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, φ V w x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), φ U w x = 0 → Loc U fun _ g => Tens.res g w x = 0)

theorem etale_tensor_complex_exists_of_sheaf_tensor_complex (hS : EtaleSheafTensorComplexExists) : EtaleComplexTensorPairingExists := by
  intro R _ I J
  obtain ⟨K, φ, hnat, hd, hsurj, hinj⟩ := hS R I J
  let μ : Pair I J K :=
    { mul := fun U s t w h => (TensorProduct.mk (ULift.{1} R) _ _).compr₂
          ((φ U w).comp (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
            (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩))
      nat := by
        intro V U g s t w h a b
        have := hnat g w (tensPure s t w h a b)
        simpa [tensPure, Tens.res, DirectSum.lmap_lof] using this
      leibniz := by
        intro U s t w h a b
        simpa [tensPure] using hd U s t w h a b }
  have hlift : ∀ U w, μ.lift U w = φ U w := by
    intro U w
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp [Pair.lift, μ]
  refine ⟨K, μ, ?_, ?_⟩
  · intro U w y
    simpa [hlift] using hsurj U w y
  · intro U w x hx
    exact hinj U w x (by simpa [hlift] using hx)

end LateralTheory.EtaleFoundations
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafTensorComplexExists
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma sec_map_dd (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  change ((I.d i j ≫ I.d j k).hom.app (op U)).hom a = 0
  rw [HomologicalComplex.d_comp_d]; rfl

def etaleTensorPresheafOfComplexes (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  map_comp f g := by
    ext1; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp [Tens.res]

def dB (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U →ₗ[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩)).compl₁₂
      ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • ((TensorProduct.mk (ULift.{1} R) _ _).compr₂ (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w + 1}
      (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩)).compl₁₂
      LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (dB I J U w p)

lemma dT_pure (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (tensPure s t w h a b) =
      tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b +
      s.negOnePow • tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b) := by
  simp [dT, tensPure, dB, DirectSum.toModule_lof, Units.smul_def, Sec.map]

lemma tensPure_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res g w (tensPure s t w h a b) = tensPure s t w h (Sec.res g a) (Sec.res g b) := by
  simp [Tens.res, tensPure, Sec.res]

lemma tens_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (H : ∀ s t (h : s + t = w) a b, f (tensPure s t w h a b) = g (tensPure s t w h a b)) : f = g := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  exact H p.1.1 p.1.2 p.2 a b

def dP (I J : Cx R) (w : ℤ) : etaleTensorPresheafOfComplexes I J w ⟶ etaleTensorPresheafOfComplexes I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality V U g := by
    ext1
    refine tens_ext fun s t h a b => ?_
    change dT I J U.unop w (Tens.res g.unop w (tensPure s t w h a b)) =
      Tens.res g.unop (w + 1) (dT I J V.unop w (tensPure s t w h a b))
    simp only [tensPure_res, dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_res]

lemma tensPure_zero_left (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (b : Sec (J.X t) U) :
    tensPure (I := I) s t w h 0 b = 0 := by simp [tensPure]

lemma tensPure_zero_right (I J : Cx R) {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) :
    tensPure (J := J) s t w h a 0 = 0 := by simp [tensPure]

lemma tensorDifferential_comp_tensorDifferential (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  apply NatTrans.ext; funext U; apply ModuleCat.hom_ext
  refine tens_ext (M := Tens I J U.unop (w + 1 + 1)) fun s t h a b => ?_
  change dT I J U.unop (w + 1) (dT I J U.unop w (tensPure s t w h a b)) = 0
  simp only [dT_pure, map_add (f := _), Units.smul_def, map_zsmul, sec_map_dd, tensPure_zero_left, tensPure_zero_right,
    smul_zero, zero_add, add_zero, Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

end

theorem etale_sheaf_tensor_complex_exists : EtaleSheafTensorComplexExists := by
  intro R _ I J
  let K : Cx R := CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (etaleTensorPresheafOfComplexes I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_tensorDifferential, Functor.map_zero])
  refine ⟨K, fun U w => ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U)).hom, ?_, ?_, ?_, ?_⟩
  · intro V U g w x
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).app (op U) ≫ (sheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).map g.op).hom x = _
    rw [← (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)).naturality]; rfl
  · intro U s t w h a b
    have hd : K.d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map (dP I J w) := by
      simp [K, CochainComplex.of_d]
    rw [hd]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w) ≫ sheafifyMap Scheme.etaleTopology (dP I J w)).app (op U)).hom (tensPure s t w h a b) = _
    rw [← toSheafify_naturality]
    change ((toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J (w + 1))).app (op U)).hom (dT I J U w (tensPure s t w h a b)) = _
    simp only [dT_pure, Units.smul_def]
    exact (LinearMap.map_add _ _ _).trans (congrArg _ (map_zsmul _ _ _))
  · intro U w y
    obtain h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (U := op U) y
    exact ⟨_, h, fun V g hg => hg⟩
  · intro U w x hx
    have h := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (etaleTensorPresheafOfComplexes I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx)
    exact ⟨_, h, fun V g hg => (show Tens.res g w x = Tens.res g w 0 from hg).trans (map_zero _)⟩

end LateralTheory.EtaleFoundations
end
end

namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAWCutFin
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAWCut
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCut

def LeafTwSec : Prop := EtaleTateTwistSectionsLocallyGenerated

theorem of_pair (h : LateralTheory.E.CupProductRingLaws.LeafTwPairExists) : LateralTheory.CohomologicalPurity.LeafAW := by
  intro q _ i j
  exact ⟨pick_spec (h q i j), fun E n m α β => LateralTheory.KummerTheory.CupAW_of (ZMod q) (twPair q i j) E rfl α β⟩

theorem row : EtaleTensorWithFlatPreservesLocalExactness := by
  intro R _ C J hJ hC s t V x hx
  have hA : C.Acyclic := fun n => (etale_short_complex_exact_iff_locally_surjective_on_kernel R (C.sc n)).2 (hC n)
  exact acyc.column_of R C J hJ ((acyc.acycIff_of R C).1 hA) V s t x hx

theorem tensAcyc : EtaleTensorAcyclicOfFlatBounded :=
  etale_tensor_complex_acyclic_of_locally_exact_flat etale_short_complex_exact_iff_locally_surjective_on_kernel (etale_tensor_complex_locally_exact_of_lifted_sections
    (etale_tensor_cycles_locally_lift_of_row_exact_and_descent row etale_tensor_cycle_locally_lowers_top_degree_of_row_exact))

theorem tensQis : EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_preserves_quasiIso_of_acyclic_and_cone tensAcyc tqis.cone_of

theorem pair_of (hq : EtaleTensorPairQuasiIsoOfFlatQuasiIso) (hm : EtaleTateTwistSingletonTensorGenMul) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LateralTheory.E.LeafTwPairExistsPf.LeafTwPairExists_of' LateralTheory.E.LeafTwTensExPf.LeafTwTensEx_of
    (LateralTheory.E.LeafTwTensResPf.leafTwTensRes_of
      (etale_tensor_twisted_resolution_of_existence_bound_and_sides LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange
        (fun R _ _ _ _ μ hI hJ hμ => (LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange R μ hμ).2.1 hI hJ)
        (tt_twist_side_of hm LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange hq)
        (tt_res_side_of LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange hq))
      (fun q _ j t => (LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange q j).2.1 t))

theorem twMul (hT : LeafTwSec) : EtaleTateTwistSingletonTensorGenMul :=
  etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange) (etale_tate_twist_multiplication_generator_map_of_section_description hT)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation
      (etale_tate_twist_generator_map_surjective_of_local_and_root (fun q _ i => (hT q i).1)
        (fun q _ j => ⟨(hT q j).2.2.2.1, fun U ζ ξ => (hT q j).2.1 U ζ (twGen j ξ)⟩))
      (etale_tate_twist_generator_map_injective_of_sections_glue hT LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange))

theorem goal_of (h2 : LeafTwSec) : LateralTheory.CohomologicalPurity.LeafAW :=
  of_pair (pair_of tensQis (twMul h2))

end LateralTheory.CohomologicalPurity.LeafAWCut
end

theorem LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of : LateralTheory.CohomologicalPurity.LeafAW :=
  LateralTheory.CohomologicalPurity.LeafAWCut.goal_of LateralTheory.CohomologicalPurity.LeafAWCutTw.twSec
end

namespace LateralTheory.Fin.LeafAW
theorem etale_purity_aw : LateralTheory.CohomologicalPurity.LeafAW := by
  apply LateralTheory.CohomologicalPurity.LeafAWCut.LeafAW_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafAW := etale_purity_aw
end LateralTheory.Fin.LeafAW
