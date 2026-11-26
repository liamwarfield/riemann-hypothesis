module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.ColumnOf
public import Development.EtaleCohomology.TateTwists.conePf

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.TensorVanishing.TensZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h; exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  have H : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → ∃ T : Sieve V, T ∈ Scheme.etaleTopology V ∧
      ∀ (W : Scheme.{0}) (k : W ⟶ V), T.arrows k → Q W (k ≫ g) := fun V g hg => hPQ V g (hP V g hg)
  choose T hT hQ using H
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg W k hk

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this.symm

theorem map_dd {C : Cx R} {U : Scheme.{0}} (i j k : ℤ) (x : Sec (C.X i) U) :
    Sec.map (C.d j k) (Sec.map (C.d i j) x) = 0 := by
  change ((C.d i j ≫ C.d j k).hom.app (op U)).hom x = 0
  rw [C.d_comp_d]; simp

theorem sec_zero {C : Cx R} (a : ℤ) [C.IsStrictlyGE a] {s : ℤ} (hs : s < a) {U : Scheme.{0}}
    (x : Sec (C.X s) U) : x = 0 := by
  have hz := C.isZero_of_isStrictlyGE a s hs
  have := congrArg (fun f : C.X s ⟶ C.X s => (f.hom.app (op U)).hom x) (hz.eq_of_src (𝟙 _) 0)
  simpa using this

theorem tens_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hM : ∀ m : M, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hM m, TensorProduct.zero_tmul]
  | add a b ha hb => rw [ha, hb, add_zero]

abbrev Ix (w : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = w}

variable {C J T : Cx R}

abbrev Cmp (C J : Cx R) (U : Scheme.{0}) (w : ℤ) : Ix w → Type 1 :=
  fun q => Sec (C.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U

def Dm (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') : Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤ)) • (DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w')
      ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem Dm_lof (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (p : Ix w) (v : Cmp C J U w p) :
    Dm U w w' hw (DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) p v) =
      DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id v) +
      ((p.1.1.negOnePow : ℤ)) • DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w')
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        (TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom v) := by
  classical
  unfold Dm
  convert DirectSum.toModule_lof (ULift.{1} R) p v using 1

theorem lift_lof (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : Ix w) (a : Sec (C.X p.1.1) U)
    (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  unfold Pair.lift
  convert DirectSum.toModule_lof (ULift.{1} R) (M := Cmp C J U w) p (a ⊗ₜ[ULift.{1} R] b) using 1
  simp

theorem lift_Dm (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (x : Tens C J U w) :
    τ.lift U (w + 1) (Dm U w (w + 1) rfl x) = Sec.map (T.d w (w + 1)) (τ.lift U w x) := by
  classical
  have : (τ.lift U (w + 1)) ∘ₗ Dm U w (w + 1) rfl = ((T.d w (w + 1)).hom.app (op U)).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, Dm_lof, map_add (f := _), map_zsmul, TensorProduct.map_tmul, LinearMap.id_apply]
    erw [lift_lof, lift_lof, lift_lof]
    have := τ.leibniz U p.1.1 p.1.2 w p.2 a b
    simp only [Sec.map] at this
    rw [this, Units.smul_def]
  exact LinearMap.congr_fun this x

theorem lift_res (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    τ.lift V w (Tens.res g w x) = Sec.res g (τ.lift U w x) := by
  classical
  have : (τ.lift V w) ∘ₗ Tens.res g w = ((T.X w).obj.map g.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, Tens.res]
    rw [DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [lift_lof, lift_lof]
    exact (τ.nat g p.1.1 p.1.2 w p.2 a b).symm
  exact LinearMap.congr_fun this x

end LateralTheory.EtaleFoundations.stairPf
end
end

section -- merged from Development.EtaleCohomology.TateTwists.TensorVanishing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_zero' {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hN : ∀ m : N, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hN n, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

theorem res_apply {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) (p : Ix w) :
    (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := by
  unfold Tens.res; rw [DirectSum.lmap_apply]

theorem nat_tens {V U : Scheme.{0}} (g : V ⟶ U) (s s' t : ℤ) (v : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    TensorProduct.map ((C.d s s').hom.app (op V)).hom LinearMap.id
        (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom v) =
      TensorProduct.map ((C.X s').obj.map g.op).hom ((J.X t).obj.map g.op).hom
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1; exact map_res (C.d s s') g a
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem lift_Dm' (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (x : Tens C J U w) :
    τ.lift U w' (Dm U w w' hw x) = Sec.map (T.d w w') (τ.lift U w x) := by
  subst hw; exact lift_Dm τ U w x

theorem lof_shift (U : Scheme.{0}) (n s s' t : ℤ) (hs : s + 1 = s') (h1 : (s + 1) + t = n) (h2 : s' + t = n)
    (y : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s + 1, t), h1⟩
        (TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id y) =
      DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s', t), h2⟩
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id y) := by
  subst hs; rfl

theorem lof_ne (U : Scheme.{0}) (n : ℤ) (i j : Ix n) (h : i.1.2 ≠ j.1.2) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) j = 0 := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne _ _ _ (fun e => h (by rw [e]))

theorem lof_same (U : Scheme.{0}) (n : ℤ) (i : Ix n) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) i = v := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_same _ _

theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sres_sub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ _ _
theorem sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

def Step : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → LateralTheory.EtaleFoundations.acyc.ColExact C J →
    ∀ (n t0 : ℤ) (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < t0 → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ (x' : Tens C J W n) (Y : Tens C J W (n - 1)),
        (∀ p : Ix n, p.1.2 < t0 + 1 → x' p = 0) ∧ Tens.res h n x = x' + Dm W (n - 1) n (by ring) Y

theorem main (hS : Step) (τ : Pair C J T) (a : ℤ) [C.IsStrictlyGE a] (hτ : τ.IsTensor)
    (hc : LateralTheory.EtaleFoundations.acyc.ColExact C J) (n : ℤ) :
    ∀ k : ℕ, ∀ (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < n - a + 1 - k → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ y : Sec (T.X (n - 1)) W, Sec.map (T.d (n - 1) n) y = Sec.res h (τ.lift V n x) := by
  intro k
  induction k with
  | zero =>
    intro V x hx _
    obtain rfl : x = 0 := DFinsupp.ext fun p => by
      by_cases hp : p.1.2 < n - a + 1 - ((0 : ℕ) : ℤ)
      · exact hx p hp
      · exact tens_zero (fun m => sec_zero a (by have := p.2; push_cast at hp; omega) m) (x p)
    exact loc_all fun W h => ⟨0, by rw [smap_zero, map_zero, sres_zero]⟩
  | succ k ih =>
    intro V x hx hd
    refine loc_bind (hS R τ hτ hc n (n - a + 1 - ((k + 1 : ℕ) : ℤ)) V x hx hd) fun W h hW => ?_
    obtain ⟨x', Y, hv, he⟩ := hW
    have hl : τ.lift W n x' = Sec.res h (τ.lift V n x) - Sec.map (T.d (n - 1) n) (τ.lift W (n - 1) Y) := by
      rw [← lift_res, he, map_add (f := _), lift_Dm']; abel
    have hd' : Sec.map (T.d n (n + 1)) (τ.lift W n x') = 0 := by
      rw [hl, smap_sub, map_res, hd, sres_zero, map_dd, sub_zero]
    refine loc_mono (ih W x' (fun p hp => hv p (by push_cast at hp ⊢; omega)) hd') fun W' h' hy => ?_
    obtain ⟨y, hy⟩ := hy
    refine ⟨y + Sec.res h' (τ.lift W (n - 1) Y), ?_⟩
    rw [smap_add, map_res, hy, hl, sres_sub, res_comp]; abel

end LateralTheory.EtaleFoundations.stairPf

open LateralTheory.EtaleFoundations.acyc LateralTheory.EtaleFoundations.stairPf in
theorem LateralTheory.EtaleFoundations.acyc.stair_of (hS : Step) : LateralTheory.EtaleFoundations.acyc.stair := by
  intro R _ C J T a b _ _ τ hτ hc U n z hz
  refine loc_bind (hτ.1 U n z) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  have key := main hS τ a hτ hc n ((n - a + 1 - b).toNat) V x
    (fun p hp => tens_zero' (fun m => sec_zero (C := J) b
      (by have := Int.self_le_toNat (n - a + 1 - b); have := p.2; omega) m) (x p))
    (by rw [hx, map_res, hz, sres_zero])
  exact loc_mono key fun W h hy => by
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, by rw [hy, hx, res_comp]⟩
end
end

section -- merged from Development.EtaleCohomology.TateTwists.StepPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.StepPf
open LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    Tens.res (k ≫ g) w x = Tens.res k w (Tens.res g w x) := by
  ext p
  rw [res_apply, res_apply, res_apply]
  generalize x p = v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ix_eq {w : ℤ} (p : Ix w) (a b : ℤ) (h : p.1.2 = b) (ha : a + b = w) : p = ⟨(a, b), ha⟩ :=
  Subtype.ext (Prod.ext (show p.1.1 = a by have := p.2; omega) h)

theorem lof_back {U : Scheme.{0}} {w : ℤ} (i j : Ix w) (h : i = j) (v : Cmp C J U w i) :
    DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) j ((DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v) j) =
      DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v := by
  subst h; rw [lof_same]

theorem ev_zsmul {U : Scheme.{0}} {w : ℤ} (c : ℤ) (f : Tens C J U w) (q : Ix w) : (c • f) q = c • f q := rfl

theorem Dm_comp (U : Scheme.{0}) (n t0 : ℤ) (y : Tens C J U n) :
    (Dm U n (n + 1) rfl y) ⟨(n - t0 + 1, t0), by omega⟩ =
      TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(n - t0, t0), by omega⟩) +
      (Dm U n (n + 1) rfl (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(n - t0 + 1, t0 - 1), by omega⟩
        (y ⟨(n - t0 + 1, t0 - 1), by omega⟩))) ⟨(n - t0 + 1, t0), by omega⟩ := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add (f := _), DirectSum.add_apply] at ha hb ⊢
    rw [ha, hb]; abel
  | of p v =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    by_cases h0 : p.1.2 = t0
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at h0; subst h0
      obtain rfl : a = n - b := by omega
      rw [Dm_lof, DirectSum.add_apply, ev_zsmul]
      dsimp only
      rw [lof_same, lof_ne _ _ _ _ (by simp), smul_zero, add_zero,
        lof_same, lof_ne _ _ _ _ (by simp; omega), map_zero, map_zero, DirectSum.zero_apply, add_zero]
    by_cases h1 : p.1.2 = t0 - 1
    · rw [lof_back p _ (ix_eq p (n - t0 + 1) (t0 - 1) h1 (by omega)), lof_ne _ _ _ _ h0, map_zero, zero_add]
    · rw [Dm_lof, DirectSum.add_apply, ev_zsmul, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ (by simp; omega),
        smul_zero, add_zero, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ h1, map_zero, map_zero, map_zero,
        DirectSum.zero_apply, add_zero]

theorem Step_of : LateralTheory.EtaleFoundations.stairPf.Step := by
  intro R _ C J T τ hτ hc n t0 V x hx hd
  have hD : τ.lift V (n + 1) (Dm V n (n + 1) rfl x) = 0 := by rw [lift_Dm, hd]
  refine loc_bind (hτ.2 V (n + 1) _ hD) fun W g hW => ?_
  have hc0 : TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op W)).hom LinearMap.id
      (Tens.res g n x ⟨(n - t0, t0), by omega⟩) = 0 := by
    rw [res_apply, nat_tens]
    have h1 := congrArg (fun z => z ⟨(n - t0 + 1, t0), by omega⟩) hW
    simp only at h1
    rw [res_apply, Dm_comp, hx ⟨(n - t0 + 1, t0 - 1), by omega⟩ (by simp)] at h1
    simp only [map_zero, DirectSum.zero_apply, add_zero] at h1
    exact h1
  refine loc_mono (hc W (n - t0) t0 _ hc0) fun W' k hk => ?_
  obtain ⟨y0, hy0⟩ := hk
  refine ⟨Tens.res (k ≫ g) n x - Dm W' (n - 1) n (by ring)
      (DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0),
    DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0, ?_,
    (sub_add_cancel _ _).symm⟩
  intro p hp
  rw [DirectSum.sub_apply, Dm_lof, DirectSum.add_apply, ev_zsmul]
  rcases lt_or_eq_of_le (show p.1.2 ≤ t0 by omega) with h | h
  · rw [res_apply, hx p h, map_zero, lof_ne _ _ _ _ (by simp; omega), lof_ne _ _ _ _ (by simp; omega),
      smul_zero, add_zero, sub_zero]
  · obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at h; subst h
    obtain rfl : a = n - b := by omega
    dsimp only
    rw [lof_shift W' n (n - b - 1) (n - b) b (by ring) (by omega) (by omega), lof_same,
      lof_ne _ _ _ _ (by simp), smul_zero, add_zero, hy0, tens_res_comp, res_apply k, sub_self]

end LateralTheory.EtaleFoundations.StepPf
end
end

namespace LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
theorem etale_complex_acyclic_iff_local_exactness : LateralTheory.EtaleFoundations.acyc.acycIff := by
  apply LateralTheory.EtaleFoundations.acyc.acycIff_of
theorem etale_tensor_column_acyclic_of_flat : LateralTheory.EtaleFoundations.acyc.column := by
  apply LateralTheory.EtaleFoundations.acyc.column_of
theorem etale_tensor_staircase_lifting_inductive : LateralTheory.EtaleFoundations.stairPf.Step := by
  apply LateralTheory.EtaleFoundations.StepPf.Step_of
theorem etale_tensor_acyclic_of_staircase_lifting : LateralTheory.EtaleFoundations.acyc.stair := by
  apply LateralTheory.EtaleFoundations.acyc.stair_of <;> first | exact etale_tensor_staircase_lifting_inductive
theorem etale_tensor_acyclic_cone_of_flat : LateralTheory.EtaleFoundations.tqis.acyc := by
  apply LateralTheory.EtaleFoundations.tqis.acyc_of <;> first | exact etale_complex_acyclic_iff_local_exactness | exact etale_tensor_column_acyclic_of_flat | exact etale_tensor_acyclic_of_staircase_lifting
theorem etale_tensor_mappingCone_commutes : LateralTheory.EtaleFoundations.tqis.cone := by
  apply LateralTheory.EtaleFoundations.tqis.cone_of
theorem etale_tensor_quasiIso_of_acyclic_cone : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  apply LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone <;> first | exact etale_tensor_acyclic_cone_of_flat | exact etale_tensor_mappingCone_commutes
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_quasiIso_of_acyclic_cone
end LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
