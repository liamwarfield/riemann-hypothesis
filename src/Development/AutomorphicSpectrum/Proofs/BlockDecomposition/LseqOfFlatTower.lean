module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHCompEqSmul
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

namespace GlobalTheory.CompanionTheory.LsRho

variable {W : Type} [CommRing W]

theorem mapH_eq_self {K : Cx.{1} W} (φ : Cx.Hom K K (RingHom.id W)) (n : ℕ)
    (h : ∀ x, φ.f n x = x) (u : K.H n) : φ.mapH n u = u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_of_comp {K L P : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L P (RingHom.id W))
    (χ : Cx.Hom K P (RingHom.id W)) (n : ℕ) (h : ∀ x, χ.f n x = ψ.f n (φ.f n x)) (u : K.H n) :
    χ.mapH n u = ψ.mapH n (φ.mapH n u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_comp_eq_smul {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L K (RingHom.id W))
    (s : W) (n : ℕ) (h : ∀ x, ψ.f n (φ.f n x) = s • x) (u : K.H n) :
    ψ.mapH n (φ.mapH n u) = s • u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem kill (l : ℕ) (K : Cx.{1} W) (j n : ℕ) (x : (qsys l K j).M n) : ((l : W) ^ n) • x = 0 := by
  change ((l : W) ^ n) • (x : (quo l K n).H j) = 0
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : ((l : W) ^ n) • z = 0 := by
    refine Subtype.ext ?_
    change ((l : W) ^ n) • z.1 = 0
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ z.1
    rw [← hw]
    change Submodule.Quotient.mk (((l : W) ^ n) • w) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [← Submodule.Quotient.mk_smul, hz]
  rfl

end GlobalTheory.CompanionTheory.LsRho

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkOfMemB
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls GlobalTheory.CompanionTheory.LsRho

namespace GlobalTheory.CompanionTheory.TowFlat

variable {W : Type} [CommRing W]

theorem mem_B_of_mk {L : Cx.{1} W} {n : ℕ} (z : L.Z n) (hz : (Submodule.Quotient.mk z : L.H n) = 0) :
    z.1 ∈ L.B n :=
  (Submodule.Quotient.mk_eq_zero ((L.B n).submoduleOf (L.Z n))).1 hz

theorem mk_of_mem_B {L : Cx.{1} W} {n : ℕ} (z : L.Z n) (h : z.1 ∈ L.B n) :
    (Submodule.Quotient.mk z : L.H n) = 0 :=
  (Submodule.Quotient.mk_eq_zero ((L.B n).submoduleOf (L.Z n))).2 h

theorem d_of_B {L : Cx.{1} W} {n : ℕ} {x : L.X n} (h : x ∈ L.B n) : L.d n x = 0 := by
  cases n with
  | zero =>
    have e : x = 0 := h
    rw [e, map_zero]
  | succ n =>
    obtain ⟨y, rfl⟩ := h
    exact L.dd n y

def Ses {A B C : Cx.{1} W} (f : Cx.Hom A B (RingHom.id W)) (g : Cx.Hom B C (RingHom.id W)) : Prop :=
  (∀ i, Function.Injective (f.f i)) ∧ (∀ i, Function.Surjective (g.f i)) ∧
    ∀ i x, g.f i x = 0 ↔ ∃ y, f.f i y = x

section Conn

variable {A B C : Cx.{1} W} {f : Cx.Hom A B (RingHom.id W)} {g : Cx.Hom B C (RingHom.id W)}

theorem lift_B (hS : Ses f g) {n : ℕ} {z : C.X n} (h : z ∈ C.B n) : ∃ b ∈ B.B n, g.f n b = z := by
  cases n with
  | zero =>
    have e : z = 0 := h
    exact ⟨0, Submodule.zero_mem _, by rw [e, map_zero]⟩
  | succ n =>
    obtain ⟨c, rfl⟩ := h
    obtain ⟨b, rfl⟩ := hS.2.1 n c
    exact ⟨B.d n b, ⟨b, rfl⟩, (g.comm n b).symm⟩

def Rel (f : Cx.Hom A B (RingHom.id W)) (g : Cx.Hom B C (RingHom.id W)) (j : ℕ) (x : C.H j) (v : A.H (j + 1)) : Prop :=
  ∃ (z : C.Z j) (β : B.X j) (w : A.Z (j + 1)), Submodule.Quotient.mk z = x ∧ Submodule.Quotient.mk w = v ∧
    g.f j β = z.1 ∧ f.f (j + 1) w.1 = B.d j β

theorem rel_total (hS : Ses f g) (j : ℕ) (x : C.H j) : ∃ v, Rel f g j x v := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨β, hβ⟩ := hS.2.1 j z.1
  have h0 : g.f (j + 1) (B.d j β) = 0 := by
    rw [← g.comm, hβ]
    exact z.2
  obtain ⟨w, hw⟩ := (hS.2.2 (j + 1) _).1 h0
  have hd : A.d (j + 1) w = 0 := by
    apply hS.1 (j + 2)
    rw [← f.comm, hw, B.dd, map_zero]
  exact ⟨_, z, β, ⟨w, hd⟩, rfl, rfl, hβ, hw⟩

theorem rel_add {j : ℕ} {x x' : C.H j} {v v' : A.H (j + 1)} (h : Rel f g j x v) (h' : Rel f g j x' v') :
    Rel f g j (x + x') (v + v') := by
  obtain ⟨z, β, w, rfl, rfl, h1, h2⟩ := h
  obtain ⟨z', β', w', rfl, rfl, h1', h2'⟩ := h'
  refine ⟨z + z', β + β', w + w', rfl, rfl, ?_, ?_⟩
  · rw [map_add (f := _), h1, h1']; rfl
  · change f.f (j + 1) (w.1 + w'.1) = _
    rw [map_add (f := _), map_add (f := _), h2, h2']

theorem rel_smul {j : ℕ} (s : W) {x : C.H j} {v : A.H (j + 1)} (h : Rel f g j x v) :
    Rel f g j (s • x) (s • v) := by
  obtain ⟨z, β, w, rfl, rfl, h1, h2⟩ := h
  refine ⟨s • z, s • β, s • w, rfl, rfl, ?_, ?_⟩
  · rw [map_smul, h1]; rfl
  · change f.f (j + 1) (s • w.1) = _
    simp only [map_smul, h2, RingHom.id_apply]

theorem rel_zero (hS : Ses f g) {j : ℕ} {v : A.H (j + 1)} (h : Rel f g j 0 v) : v = 0 := by
  obtain ⟨z, β, w, hz, rfl, h1, h2⟩ := h
  obtain ⟨b, hbB, hb⟩ := lift_B hS (mem_B_of_mk z hz)
  have h0 : g.f j (β - b) = 0 := by rw [map_sub, h1, hb, sub_self]
  obtain ⟨a, ha⟩ := (hS.2.2 j _).1 h0
  have e : w.1 = A.d j a := by
    apply hS.1 (j + 1)
    rw [h2, ← f.comm, ha, map_sub, d_of_B hbB, sub_zero]
  exact mk_of_mem_B w ⟨a, e.symm⟩

theorem rel_unique (hS : Ses f g) {j : ℕ} {x : C.H j} {v v' : A.H (j + 1)} (h : Rel f g j x v)
    (h' : Rel f g j x v') : v = v' := by
  have h2 := rel_add h (rel_smul (-1) h')
  rw [neg_one_smul, neg_one_smul, add_neg_cancel] at h2
  exact add_neg_eq_zero.1 (rel_zero hS h2)

def cn (hS : Ses f g) (j : ℕ) : C.H j →ₗ[W] A.H (j + 1) where
  toFun x := Classical.choose (rel_total hS j x)
  map_add' x y := rel_unique hS (Classical.choose_spec (rel_total hS j (x + y)))
    (rel_add (Classical.choose_spec (rel_total hS j x)) (Classical.choose_spec (rel_total hS j y)))
  map_smul' s x := rel_unique hS (Classical.choose_spec (rel_total hS j (s • x)))
    (rel_smul s (Classical.choose_spec (rel_total hS j x)))

theorem cn_rel (hS : Ses f g) (j : ℕ) (x : C.H j) : Rel f g j x (cn hS j x) :=
  Classical.choose_spec (rel_total hS j x)

theorem cn_eq (hS : Ses f g) {j : ℕ} {x : C.H j} {v : A.H (j + 1)} (h : Rel f g j x v) : cn hS j x = v :=
  rel_unique hS (cn_rel hS j x) h

theorem ex_mid (hS : Ses f g) (j : ℕ) (x : B.H j) (h : g.mapH j x = 0) : ∃ y, f.mapH j y = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hb : g.f j z.1 ∈ C.B j := mem_B_of_mk (g.mapZ j z) h
  obtain ⟨b, hbB, hbg⟩ := lift_B hS hb
  have h0 : g.f j (z.1 - b) = 0 := by rw [map_sub, hbg, sub_self]
  obtain ⟨a, ha⟩ := (hS.2.2 j _).1 h0
  have da : A.d j a = 0 := by
    apply hS.1 (j + 1)
    have hz : B.d j z.1 = 0 := z.2
    rw [map_zero, ← f.comm, ha, map_sub, d_of_B hbB, hz, sub_zero]
  refine ⟨Submodule.Quotient.mk ⟨a, da⟩, ?_⟩
  change Submodule.Quotient.mk (f.mapZ j ⟨a, da⟩) = Submodule.Quotient.mk z
  rw [Submodule.Quotient.eq]
  change f.f j a - z.1 ∈ B.B j
  rw [ha, sub_sub_cancel_left]
  exact Submodule.neg_mem _ hbB

theorem ex_cn (hS : Ses f g) (j : ℕ) (x : C.H j) (h : cn hS j x = 0) : ∃ y, g.mapH j y = x := by
  obtain ⟨z, β, w, rfl, hw, h1, h2⟩ := cn_rel hS j x
  rw [h] at hw
  obtain ⟨a, ha⟩ := mem_B_of_mk w hw
  have hd : B.d j (β - f.f j a) = 0 := by
    rw [map_sub, f.comm, ha, h2, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨_, hd⟩, ?_⟩
  change Submodule.Quotient.mk (g.mapZ j ⟨_, hd⟩) = Submodule.Quotient.mk z
  congr 1
  refine Subtype.ext ?_
  change g.f j (β - f.f j a) = z.1
  rw [map_sub, h1, (hS.2.2 j _).2 ⟨a, rfl⟩, sub_zero]

theorem cn_nat {A' B' C' : Cx.{1} W} {f' : Cx.Hom A' B' (RingHom.id W)} {g' : Cx.Hom B' C' (RingHom.id W)}
    (hS : Ses f g) (hS' : Ses f' g') (α : Cx.Hom A A' (RingHom.id W)) (μ : Cx.Hom B B' (RingHom.id W))
    (γ : Cx.Hom C C' (RingHom.id W)) (j : ℕ)
    (hf : ∀ x, f'.f (j + 1) (α.f (j + 1) x) = μ.f (j + 1) (f.f (j + 1) x))
    (hg : ∀ x, g'.f j (μ.f j x) = γ.f j (g.f j x)) (x : C.H j) :
    cn hS' j (γ.mapH j x) = α.mapH (j + 1) (cn hS j x) := by
  obtain ⟨z, β, w, rfl, hw, h1, h2⟩ := cn_rel hS j x
  rw [← hw]
  refine cn_eq hS' ⟨γ.mapZ j z, μ.f j β, α.mapZ (j + 1) w, rfl, rfl, ?_, ?_⟩
  · change g'.f j (μ.f j β) = γ.f j z.1
    rw [hg, h1]
  · change f'.f (j + 1) (α.f (j + 1) w.1) = _
    rw [hf, h2, μ.comm]

end Conn

theorem mapH_bij {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (h : ∀ i, Function.Bijective (φ.f i))
    (j : ℕ) : Function.Bijective (φ.mapH j) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hb : φ.f j z.1 ∈ L.B j := mem_B_of_mk (φ.mapZ j z) hx
    refine mk_of_mem_B z ?_
    cases j with
    | zero =>
      have e : φ.f 0 z.1 = 0 := hb
      have e' : z.1 = 0 := (h 0).1 (by rw [e, map_zero])
      rw [e']
      exact Submodule.zero_mem _
    | succ j =>
      obtain ⟨y, hy⟩ := hb
      obtain ⟨y, rfl⟩ := (h j).2 y
      exact ⟨y, (h (j + 1)).1 (by rw [← φ.comm, hy])⟩
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy⟩ := (h j).2 z.1
    have hd : K.d j y = 0 := by
      apply (h (j + 1)).1
      have hz : L.d j z.1 = 0 := z.2
      rw [map_zero, ← φ.comm, hy, hz]
    refine ⟨Submodule.Quotient.mk ⟨y, hd⟩, ?_⟩
    change Submodule.Quotient.mk (φ.mapZ j ⟨y, hd⟩) = Submodule.Quotient.mk z
    congr 1
    exact Subtype.ext hy

theorem mem_lpow {l : ℕ} {M : Type 1} [AddCommGroup M] [Module W M] {n : ℕ} {x : M} :
    x ∈ lpow (W := W) l M n ↔ ∃ y : M, ((l : W) ^ n) • y = x := by
  simp [lpow, LinearMap.mem_range]

def mulc (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0) :
    Cx.Hom (quo l K a) K (RingHom.id W) where
  f i := Submodule.liftQ _ (((l : W) ^ (c - a)) • LinearMap.id) (by
    rintro _ ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add,
      Nat.sub_add_cancel h, hk])
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (K.d i).map_smul _ x

theorem mulc_mk (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0)
    (i : ℕ) (x : K.X i) : (mulc l K h hk).f i (Submodule.Quotient.mk x) = ((l : W) ^ (c - a)) • x := rfl

theorem ses_flat {l c : ℕ} {K : Cx.{1} W} (hK : FlatL l c K) {a b : ℕ} (hc : a + b = c) (h : a ≤ c)
    (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0) : Ses (mulc l K h hk) (prj l K b) := by
  have hb : c - a = b := by omega
  refine ⟨fun i => (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun i => Submodule.mkQ_surjective _,
    fun i x => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mulc_mk, hb] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hK i).2 a b hc x hx)
  · constructor
    · intro hx
      obtain ⟨y, rfl⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      exact ⟨Submodule.Quotient.mk y, by rw [mulc_mk, hb]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [mulc_mk, hb]
      exact (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨y, rfl⟩)

theorem ses_red {l e : ℕ} {L : Cx.{1} W} (hL : FlatL l e L) {a b c : ℕ} (hc : a + b = c) (he : c ≤ e)
    (ha : a ≤ c) (hb : b ≤ c) : Ses (nug l L ha) (redg l L hb) := by
  have hb' : c - a = b := by omega
  refine ⟨fun i => (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun i x => ?_, fun i x => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.Quotient.mk (((l : W) ^ (c - a)) • y) = (0 : (quo l L c).X i) := hx
    rw [hb'] at h1
    obtain ⟨t, ht⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
    have h2 : ((l : W) ^ b) • (y - ((l : W) ^ a) • t) = 0 := by
      rw [smul_sub, smul_smul, ← pow_add, Nat.add_comm b a, hc, ht, sub_self]
    obtain ⟨s, hs⟩ := mem_lpow.1 ((hL i).2 (e - b) b (by omega) _ h2)
    refine (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨((l : W) ^ (e - b - a)) • s + t, ?_⟩)
    rw [smul_add, smul_smul, ← pow_add, show a + (e - b - a) = e - b by omega, hs, sub_add_cancel]
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : Submodule.Quotient.mk t = (0 : (quo l L b).X i) := hx
      obtain ⟨s, rfl⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
      refine ⟨Submodule.Quotient.mk s, ?_⟩
      change Submodule.Quotient.mk (((l : W) ^ (c - a)) • s) = _
      rw [hb']
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have h1 : Submodule.Quotient.mk (((l : W) ^ (c - a)) • y) = (Submodule.Quotient.mk t : (quo l L c).X i) := hy
      rw [hb'] at h1
      rw [← h1]
      change Submodule.Quotient.mk (((l : W) ^ b) • y) = (0 : (quo l L b).X i)
      exact (Submodule.Quotient.mk_eq_zero _).2 (mem_lpow.2 ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.TowFlat

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls GlobalTheory.CompanionTheory.LsRho

namespace GlobalTheory.CompanionTheory.TowFlat

variable {W : Type} [CommRing W]

section General

variable {l : ℕ}

theorem redg_qred {K L : Cx.{1} W} {c : ℕ} (f : Cx.Hom K (quo l L c) (RingHom.id W)) {b b' : ℕ} (hbb : b ≤ b')
    (hb : b' ≤ c) (i : ℕ) (x : (quo l K b').X i) :
    (redg l L hbb).f i ((qred l f hb).f i x) = (qred l f (hbb.trans hb)).f i ((redg l K hbb).f i x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (f.f i y)
  change (redg l L hbb).f i ((redg l L hb).f i (f.f i y)) = (redg l L (hbb.trans hb)).f i (f.f i y)
  rw [← ht]
  rfl

theorem redg_prj_H (K : Cx.{1} W) {b c : ℕ} (hb : b ≤ c) (j : ℕ) (x : K.H j) :
    (redg l K hb).mapH j ((prj l K c).mapH j x) = (prj l K b).mapH j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem qred_prj_H {K L : Cx.{1} W} {c : ℕ} (f : Cx.Hom K (quo l L c) (RingHom.id W)) {b : ℕ} (h : b ≤ c)
    (j : ℕ) (u : K.H j) :
    (qred l f h).mapH j ((prj l K b).mapH j u) = (redg l L h).mapH j (f.mapH j u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem redg_self_H (K : Cx.{1} W) (c j : ℕ) (u : (quo l K c).H j) : (redg l K (le_refl c)).mapH j u = u := by
  refine mapH_eq_self _ j (fun x => ?_) u
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem nug_qred {K L : Cx.{1} W} {c a : ℕ} (f : Cx.Hom K (quo l L c) (RingHom.id W)) (h : a ≤ c)
    (hk : ∀ i (x : K.X i), ((l : W) ^ c) • x = 0) (i : ℕ) (x : (quo l K a).X i) :
    (nug l L h).f i ((qred l f h).f i x) = f.f i ((mulc l K h hk).f i x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mulc_mk, map_smul]
  change (nug l L h).f i ((redg l L h).f i (f.f i y)) = _
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (f.f i y)
  rw [← ht]
  rfl

theorem nug_redg (L : Cx.{1} W) {a c : ℕ} (h : a ≤ c) (h1 : a + 1 ≤ c + 1)
    (hk : ∀ i (x : L.X i), ((l : W) ^ (c + 1)) • x = 0) (i : ℕ) (x : (quo l L (a + 1)).X i) :
    (nug l L h).f i ((redg l L (Nat.le_succ a)).f i x) = (prj l L c).f i ((mulc l L h1 hk).f i x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mulc_mk]
  change Submodule.Quotient.mk (((l : W) ^ (c - a)) • y) = Submodule.Quotient.mk (((l : W) ^ (c + 1 - (a + 1))) • y)
  rw [Nat.add_sub_add_right]

end General

section Tower

variable (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W))

def tr {b m : ℕ} (hb : b ≤ m) {c : ℕ} (h : m ≤ c) : Cx.Hom (quo l (Kt m) b) (quo l (Kt c) b) (RingHom.id W) :=
  Nat.leRec (motive := fun c _ => Cx.Hom (quo l (Kt m) b) (quo l (Kt c) b) (RingHom.id W))
    (Cx.Hom.id _) (fun c hc t => t.comp (qred l (ψ c) (hb.trans hc))) h

theorem tr_self_f {b m : ℕ} (hb : b ≤ m) (i : ℕ) (x : (quo l (Kt m) b).X i) :
    (tr l Kt ψ hb (le_refl m)).f i x = x := by
  unfold tr
  rw [Nat.leRec_self]
  rfl

theorem tr_succ_f {b m : ℕ} (hb : b ≤ m) {c : ℕ} (h : m ≤ c) (h' : m ≤ c + 1) (i : ℕ) (x : (quo l (Kt m) b).X i) :
    (tr l Kt ψ hb h').f i x = (qred l (ψ c) (hb.trans h)).f i ((tr l Kt ψ hb h).f i x) := by
  unfold tr
  rw [Nat.leRec_succ]
  rfl

theorem tr_succ_H {b m : ℕ} (hb : b ≤ m) {c : ℕ} (h : m ≤ c) (h' : m ≤ c + 1) (j : ℕ) (u : (quo l (Kt m) b).H j) :
    (tr l Kt ψ hb h').mapH j u = (qred l (ψ c) (hb.trans h)).mapH j ((tr l Kt ψ hb h).mapH j u) :=
  mapH_of_comp _ _ _ j (tr_succ_f l Kt ψ hb h h' j) u

theorem tr_bij (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    {b m : ℕ} (hb : b ≤ m) {c : ℕ} (h : m ≤ c) (j : ℕ) : Function.Bijective ((tr l Kt ψ hb h).mapH j) := by
  induction c, h using Nat.le_induction with
  | base =>
    have e : ⇑((tr l Kt ψ hb (le_refl m)).mapH j) = id :=
      funext fun u => mapH_eq_self _ j (tr_self_f l Kt ψ hb j) u
    rw [e]
    exact Function.bijective_id
  | succ c hc ih =>
    have e : ⇑((tr l Kt ψ hb (Nat.le_succ_of_le hc)).mapH j) =
        ⇑((qred l (ψ c) (hb.trans hc)).mapH j) ∘ ⇑((tr l Kt ψ hb hc).mapH j) :=
      funext fun u => tr_succ_H l Kt ψ hb hc _ j u
    rw [e]
    exact (hq _ _ _ j).comp ih

theorem redg_tr {b b' m : ℕ} (hbb : b ≤ b') (hb : b' ≤ m) {c : ℕ} (h : m ≤ c) (i : ℕ) (x : (quo l (Kt m) b').X i) :
    (redg l (Kt c) hbb).f i ((tr l Kt ψ hb h).f i x) =
      (tr l Kt ψ (hbb.trans hb) h).f i ((redg l (Kt m) hbb).f i x) := by
  induction c, h using Nat.le_induction with
  | base => rw [tr_self_f, tr_self_f]
  | succ c hc ih =>
    rw [tr_succ_f l Kt ψ hb hc, tr_succ_f l Kt ψ (hbb.trans hb) hc, redg_qred, ih]

theorem redg_tr_H {b b' m : ℕ} (hbb : b ≤ b') (hb : b' ≤ m) {c : ℕ} (h : m ≤ c) (j : ℕ) (u : (quo l (Kt m) b').H j) :
    (redg l (Kt c) hbb).mapH j ((tr l Kt ψ hb h).mapH j u) =
      (tr l Kt ψ (hbb.trans hb) h).mapH j ((redg l (Kt m) hbb).mapH j u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (redg_tr l Kt ψ hbb hb h j z.1))

theorem tr_first {a c : ℕ} (hb : a ≤ a + 1) (h : a + 1 ≤ c) (h' : a ≤ c) (i : ℕ) (x : (quo l (Kt a) a).X i) :
    (tr l Kt ψ hb h).f i ((qred l (ψ a) (le_refl a)).f i x) = (tr l Kt ψ (le_refl a) h').f i x := by
  induction c, h using Nat.le_induction with
  | base =>
    rw [tr_self_f, tr_succ_f l Kt ψ (le_refl a) (le_refl a), tr_self_f]
  | succ c hc ih =>
    rw [tr_succ_f l Kt ψ hb hc, tr_succ_f l Kt ψ (le_refl a) (hb.trans hc), ih (hb.trans hc)]

theorem tr_first_H {a c : ℕ} (hb : a ≤ a + 1) (h : a + 1 ≤ c) (h' : a ≤ c) (j : ℕ) (v : (quo l (Kt a) a).H j) :
    (tr l Kt ψ hb h).mapH j ((qred l (ψ a) (le_refl a)).mapH j v) = (tr l Kt ψ (le_refl a) h').mapH j v := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact congrArg Submodule.Quotient.mk (Subtype.ext (tr_first l Kt ψ hb h h' j z.1))

def theta (j : ℕ) {b c : ℕ} (h : b ≤ c) : (Kt b).H j →ₗ[W] (quo l (Kt c) b).H j :=
  ((tr l Kt ψ (le_refl b) h).mapH j).comp ((prj l (Kt b) b).mapH j)

theorem theta_apply (j : ℕ) {b c : ℕ} (h : b ≤ c) (x : (Kt b).H j) :
    theta l Kt ψ j h x = (tr l Kt ψ (le_refl b) h).mapH j ((prj l (Kt b) b).mapH j x) := rfl

theorem theta_self (j c : ℕ) (x : (Kt c).H j) :
    theta l Kt ψ j (le_refl c) x = (prj l (Kt c) c).mapH j x :=
  mapH_eq_self _ j (tr_self_f l Kt ψ (le_refl c) j) _

theorem theta_succ (j : ℕ) {b c : ℕ} (h : b ≤ c) (h' : b ≤ c + 1) (x : (Kt b).H j) :
    theta l Kt ψ j h' x = (qred l (ψ c) h).mapH j (theta l Kt ψ j h x) :=
  tr_succ_H l Kt ψ (le_refl b) h h' j _

theorem prj_bij (hF : ∀ c, FlatL l c (Kt c)) (b j : ℕ) : Function.Bijective ((prj l (Kt b) b).mapH j) := by
  refine mapH_bij _ (fun i => ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, Submodule.mkQ_surjective _⟩) j
  obtain ⟨y, rfl⟩ := mem_lpow.1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
  exact (hF b i).1 y

variable {l Kt ψ}

theorem theta_bij (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j : ℕ) {b c : ℕ} (h : b ≤ c) : Function.Bijective (theta l Kt ψ j h) :=
  (tr_bij l Kt ψ hq (le_refl b) h j).comp (prj_bij l Kt hF b j)

def thetaE (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j : ℕ) {b c : ℕ} (h : b ≤ c) : (Kt b).H j ≃ₗ[W] (quo l (Kt c) b).H j :=
  LinearEquiv.ofBijective (theta l Kt ψ j h) (theta_bij hF hq j h)

theorem theta_thetaE (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j : ℕ) {b c : ℕ} (h : b ≤ c) (y : (quo l (Kt c) b).H j) :
    theta l Kt ψ j h ((thetaE hF hq j h).symm y) = y :=
  (thetaE hF hq j h).apply_symm_apply y

def rhoT (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j c b : ℕ) : (Kt c).H j →ₗ[W] (Kt b).H j :=
  if h : b ≤ c then (thetaE hF hq j h).symm.toLinearMap ∘ₗ (prj l (Kt c) b).mapH j else 0

theorem theta_rho (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j : ℕ) {b c : ℕ} (h : b ≤ c) (x : (Kt c).H j) :
    theta l Kt ψ j h (rhoT hF hq j c b x) = (prj l (Kt c) b).mapH j x := by
  rw [rhoT, dite_eq_left h]
  exact theta_thetaE hF hq j h _

def nuT (hF : ∀ c, FlatL l c (Kt c)) (j a c : ℕ) : (Kt a).H j →ₗ[W] (Kt c).H j :=
  if h : a ≤ c then ((mulc l (Kt c) h (fun i => (hF c i).1)).mapH j) ∘ₗ theta l Kt ψ j h else 0

theorem nu_eq (hF : ∀ c, FlatL l c (Kt c)) (j : ℕ) {a c : ℕ} (h : a ≤ c) (y : (Kt a).H j) :
    nuT (ψ := ψ) hF j a c y = (mulc l (Kt c) h (fun i => (hF c i).1)).mapH j (theta l Kt ψ j h y) := by
  rw [nuT, dite_eq_left h]
  rfl

theorem le_left {a b c : ℕ} (hc : a + b = c) : a ≤ c := by omega

theorem le_right {a b c : ℕ} (hc : a + b = c) : b ≤ c := by omega

def deltaG (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j a b c : ℕ) (hc : a + b = c) : (Kt b).H j →ₗ[W] (Kt a).H (j + 1) :=
  (thetaE hF hq (j + 1) (le_left hc)).symm.toLinearMap ∘ₗ
    cn (ses_flat (hF c) hc (le_left hc) (fun i => (hF c i).1)) j ∘ₗ theta l Kt ψ j (le_right hc)

theorem theta_delta (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j a b c : ℕ) (hc : a + b = c) (x : (Kt b).H j) :
    theta l Kt ψ (j + 1) (le_left hc) (deltaG hF hq j a b c hc x) =
      cn (ses_flat (hF c) hc (le_left hc) (fun i => (hF c i).1)) j (theta l Kt ψ j (le_right hc) x) :=
  theta_thetaE hF hq (j + 1) (le_left hc) _

theorem deltaG_congr (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j a b c c' : ℕ) (hc : a + b = c) (hc' : a + b = c') (x : (Kt b).H j) :
    deltaG hF hq j a b c hc x = deltaG hF hq j a b c' hc' x := by
  subst hc
  subst hc'
  rfl

variable (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j))

theorem psi_r (j n : ℕ) (x : (Kt (n + 1)).H j) :
    (ψ n).mapH j ((tsys l Kt ψ hψ j).r n x) = (prj l (Kt (n + 1)) n).mapH j x :=
  (LinearEquiv.ofBijective ((ψ n).mapH j) (hψ n j)).apply_symm_apply _

theorem redg_theta (j a c : ℕ) (h : a + 1 ≤ c) (h' : a ≤ c) (y : (Kt (a + 1)).H j) :
    (redg l (Kt c) (Nat.le_succ a)).mapH j (theta l Kt ψ j h y) =
      theta l Kt ψ j h' ((tsys l Kt ψ hψ j).r a y) := by
  rw [theta_apply, theta_apply, redg_tr_H l Kt ψ (Nat.le_succ a) (le_refl (a + 1)) h j, redg_prj_H,
    ← tr_first_H l Kt ψ (Nat.le_succ a) h h' j, qred_prj_H, redg_self_H, psi_r]

theorem rho_succT (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j c b : ℕ) (h : b ≤ c) (x : (Kt (c + 1)).H j) :
    rhoT hF hq j (c + 1) b x = rhoT hF hq j c b ((tsys l Kt ψ hψ j).r c x) := by
  have h' : b ≤ c + 1 := h.trans (Nat.le_succ c)
  apply (theta_bij hF hq j h').1
  rw [theta_rho hF hq j h', theta_succ l Kt ψ j h h', theta_rho hF hq j h, qred_prj_H, psi_r, redg_prj_H]

theorem nu_rT (hF : ∀ c, FlatL l c (Kt c)) (j a c : ℕ) (h : a ≤ c) (y : (Kt (a + 1)).H j) :
    (tsys l Kt ψ hψ j).r c (nuT (ψ := ψ) hF j (a + 1) (c + 1) y) =
      nuT (ψ := ψ) hF j a c ((tsys l Kt ψ hψ j).r a y) := by
  have h1 : a + 1 ≤ c + 1 := Nat.succ_le_succ h
  have h2 : a ≤ c + 1 := h.trans (Nat.le_succ c)
  apply (hψ c j).1
  rw [psi_r, nu_eq hF j h1, nu_eq hF j h]
  have e1 : ∀ v : (quo l (Kt c) a).H j, (ψ c).mapH j ((mulc l (Kt c) h (fun i => (hF c i).1)).mapH j v) =
      (nug l (Kt (c + 1)) h).mapH j ((qred l (ψ c) h).mapH j v) := by
    intro v
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact congrArg Submodule.Quotient.mk (Subtype.ext (nug_qred (ψ c) h (fun i => (hF c i).1) j z.1).symm)
  have e2 : ∀ v : (quo l (Kt (c + 1)) (a + 1)).H j,
      (prj l (Kt (c + 1)) c).mapH j ((mulc l (Kt (c + 1)) h1 (fun i => (hF (c + 1) i).1)).mapH j v) =
      (nug l (Kt (c + 1)) h).mapH j ((redg l (Kt (c + 1)) (Nat.le_succ a)).mapH j v) := by
    intro v
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact congrArg Submodule.Quotient.mk (Subtype.ext (nug_redg _ h h1 (fun i => (hF (c + 1) i).1) j z.1).symm)
  rw [e1, e2, ← theta_succ l Kt ψ j h h2, redg_theta hψ j a (c + 1) h1 h2]

theorem delta_rT (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j a b c : ℕ) (hc : a + b = c) (hc' : a + 1 + b = c + 1) (x : (Kt b).H j) :
    (tsys l Kt ψ hψ (j + 1)).r a (deltaG hF hq j (a + 1) b (c + 1) hc' x) = deltaG hF hq j a b c hc x := by
  have ha : a ≤ c := le_left hc
  have hb : b ≤ c := le_right hc
  have ha' : a ≤ c + 1 := ha.trans (Nat.le_succ c)
  have hb' : b ≤ c + 1 := hb.trans (Nat.le_succ c)
  apply (theta_bij hF hq (j + 1) ha').1
  rw [← redg_theta hψ (j + 1) a (c + 1) (le_left hc') ha', theta_delta hF hq j (a + 1) b (c + 1) hc',
    theta_succ l Kt ψ (j + 1) ha ha', theta_delta hF hq j a b c hc]
  have S2 := ses_red (hF (c + 1)) hc (Nat.le_succ c) ha hb
  have n1 := cn_nat (ses_flat (hF c) hc (le_left hc) (fun i => (hF c i).1)) S2
    (qred l (ψ c) ha) (ψ c) (qred l (ψ c) hb) j
    (fun y => nug_qred (ψ c) ha (fun i => (hF c i).1) (j + 1) y) (fun y => rfl) (theta l Kt ψ j hb x)
  have n2 := cn_nat (ses_flat (hF (c + 1)) hc' (le_left hc') (fun i => (hF (c + 1) i).1)) S2
    (redg l (Kt (c + 1)) (Nat.le_succ a)) (prj l (Kt (c + 1)) c) (Cx.Hom.id _) j
    (fun y => nug_redg _ ha (le_left hc') (fun i => (hF (c + 1) i).1) (j + 1) y) (fun y => rfl)
    (theta l Kt ψ j hb' x)
  rw [← n1, ← n2, ← theta_succ l Kt ψ j hb hb', mapH_eq_self (Cx.Hom.id _) j (fun _ => rfl)]

theorem rho_selfT (hF : ∀ c, FlatL l c (Kt c)) (hq : ∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j))
    (j c : ℕ) (x : (Kt c).H j) : rhoT hF hq j c c x = x := by
  apply (theta_bij hF hq j (le_refl c)).1
  rw [theta_rho hF hq j (le_refl c), theta_self]

theorem kill_H (hF : ∀ c, FlatL l c (Kt c)) (j n : ℕ) (x : (Kt n).H j) : ((l : W) ^ n) • x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : ((l : W) ^ n) • z = 0 := Subtype.ext ((hF n j).1 z.1)
  rw [← Submodule.Quotient.mk_smul, hz]
  rfl

end Tower

theorem nonempty_lSeq_tsys : ∀ (W : Type) [CommRing W] (l : ℕ) (Kt : ℕ → Cx.{1} W)
    (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W))
    (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)), (∀ c, FlatL l c (Kt c)) →
    (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) →
    ∀ j, Nonempty (LSeq l (tsys l Kt ψ hψ j) (tsys l Kt ψ hψ (j + 1))) := by
  intro W _ l Kt ψ hψ hF hq j
  refine ⟨{
    ρ := fun c b => rhoT hF hq j c b
    ν := fun a c => nuT (ψ := ψ) hF j a c
    δ := fun b a => deltaG hF hq j a b (a + b) rfl
    kill := kill_H hF j
    ρ_self := fun c x => rho_selfT hF hq j c x
    ρ_succ := fun c b h x => rho_succT hψ hF hq j c b h x
    ν_ρ := fun a c h x => ?_
    ν_r := fun a c h y => nu_rT hψ hF j a c h y
    ex₁ := fun a b c hc x hx => ?_
    δ_r := fun b a x => ?_
    ex₂ := fun a b c hc x hx => ?_ }⟩
  · change nuT (ψ := ψ) hF j a c (rhoT hF hq j c a x) = _
    rw [nu_eq hF j h, theta_rho hF hq j h]
    exact mapH_comp_eq_smul _ _ _ j (fun _ => rfl) x
  · subst hc
    have hx' : rhoT hF hq j (a + b) b x = 0 := hx
    have h0 := theta_rho hF hq j (le_right (rfl : a + b = a + b)) x
    rw [hx', map_zero] at h0
    obtain ⟨y, hy⟩ := ex_mid (ses_flat (hF (a + b)) rfl (le_left rfl) (fun i => (hF (a + b) i).1)) j x h0.symm
    refine ⟨(thetaE hF hq j (le_left (rfl : a + b = a + b))).symm y, ?_⟩
    change nuT (ψ := ψ) hF j a (a + b) _ = x
    rw [nu_eq hF j (le_left rfl), theta_thetaE, hy]
  · change (tsys l Kt ψ hψ (j + 1)).r a (deltaG hF hq j (a + 1) b (a + 1 + b) rfl x) = deltaG hF hq j a b (a + b) rfl x
    rw [deltaG_congr hF hq j (a + 1) b (a + 1 + b) (a + b + 1) rfl (by omega) x]
    exact delta_rT hψ hF hq j a b (a + b) rfl (by omega) x
  · subst hc
    have hx' : deltaG hF hq j a b (a + b) rfl x = 0 := hx
    have h0 := theta_delta hF hq j a b (a + b) rfl x
    rw [hx', map_zero] at h0
    obtain ⟨y, hy⟩ := ex_cn _ j _ h0.symm
    refine ⟨y, ?_⟩
    change rhoT hF hq j (a + b) b y = x
    apply (theta_bij hF hq j (le_right (rfl : a + b = a + b))).1
    rw [theta_rho hF hq j (le_right rfl), hy]

end GlobalTheory.CompanionTheory.TowFlat

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTowerStatement
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseq_of_flat_tower : ∀ (W : Type) [CommRing W] (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W)) (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)), (∀ c, FlatL l c (Kt c)) → (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) → ∀ j, Nonempty (LSeq l (tsys l Kt ψ hψ j) (tsys l Kt ψ hψ (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | exact GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | (intros; apply GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys <;> assumption)
end
