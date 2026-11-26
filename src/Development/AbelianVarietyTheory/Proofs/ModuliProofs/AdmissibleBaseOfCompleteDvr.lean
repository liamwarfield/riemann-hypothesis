module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPullbackDegenerationOfValuesIsoDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphism
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.InvariantMorDescent

theorem exists_equalizer_ideal {Z Y S : Scheme.{0}} (z : Y ⟶ S) [IsSeparated z] (a b : Z ⟶ Y)
    (h : a ≫ z = b ≫ z) :
    ∃ I : Z.IdealSheafData, ∀ (T : Scheme.{0}) (t : T ⟶ Z), I ≤ t.ker ↔ t ≫ a = t ≫ b := by
  let i := pullback.fst (pullback.lift a b h) (pullback.diagonal z)
  have hi : i ≫ a = i ≫ b := by
    have c : i ≫ _ = _ := pullback.condition (f := pullback.lift a b h) (g := pullback.diagonal z)
    have c₁ := congrArg (· ≫ pullback.fst z z) c
    have c₂ := congrArg (· ≫ pullback.snd z z) c
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at c₁ c₂
    exact c₁.trans c₂.symm
  refine ⟨i.ker, fun T t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [← IsClosedImmersion.lift_fac i t ht, Category.assoc, Category.assoc, hi]
  · have e : t ≫ pullback.lift a b h = (t ≫ a) ≫ pullback.diagonal z := by
      apply pullback.hom_ext
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd, ht]
    rw [← pullback.lift_fst t (t ≫ a) e]
    exact Scheme.Hom.le_ker_comp _ _

theorem fst_comp_eq_snd_comp {K L : Type} [Field K] [Field L] [Algebra K L] {G : Type*}
    (s : G → L →ₐ[K] L) (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    {X X' Y S : Scheme.{0}} {p : X ⟶ Spec (.of K)} {q : X' ⟶ Spec (.of L)} {π : X' ⟶ X}
    (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (z : Y ⟶ S) [IsSeparated z] (f : X' ⟶ Y) (u : X ⟶ S) (hu : f ≫ z = π ≫ u)
    (hf : ∀ g, GaloisDescent.twist H (s g) ≫ f = f) :
    pullback.fst π π ≫ f = pullback.snd π π ≫ f := by
  have hp : IsPullback (pullback.fst π π) (pullback.snd π π ≫ q) (π ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsPullback.of_hasPullback π π).paste_vert H
  obtain ⟨I, hI⟩ := exists_equalizer_ideal z (pullback.fst π π ≫ f) (pullback.snd π π ≫ f) (by
    rw [Category.assoc, Category.assoc, hu, pullback.condition_assoc])
  have h₂ : ∀ g, GaloisDescent.twist hp (s g) ≫ pullback.snd π π =
      pullback.snd π π ≫ GaloisDescent.twist H (s g) := fun g => by
    apply H.hom_ext
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst, ← pullback.condition,
        GaloisDescent.twist_fst_assoc]
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_snd, GaloisDescent.twist_snd,
        Category.assoc]
  obtain ⟨J, hJ, -⟩ := (GaloisDescent.idealSheaf_stable_iff_exists_comap hp s hs I).1 fun g => by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    refine (hI _ _).2 ?_
    rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst_assoc, reassoc_of% (h₂ g), hf]
    exact (hI _ _).1 I.ker_subschemeι.ge
  have h₃ : I ≤ (pullback.diagonal π).ker := (hI _ _).2 (by simp)
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le, ← hJ,
    ← Scheme.IdealSheafData.comap_comp, pullback.diagonal_fst,
    Scheme.IdealSheafData.comap_id, le_bot_iff] at h₃
  rw [h₃, Scheme.IdealSheafData.comap_bot] at hJ
  simpa using (hI _ (𝟙 _)).1 (hJ ▸ bot_le)

theorem existsUnique_desc : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  intro K C _ _ _ _ _ S b X Y hY κ hκ f hf
  have f₁ : Flat κ.left := by
    rw [hκ]
    change Flat (spMap (algebraMap K C))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective κ.left := ⟨fun y =>
    ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have f₃ : QuasiCompact κ.left := by
    rw [hκ]
    exact inferInstanceAs (QuasiCompact (spMap (algebraMap K C)))
  have H : IsPullback (κ ▷ X).left (fst _ X).left (fst (Over.mk b) X).left
      (Spec.map (CommRingCat.ofHom (algebraMap K C))) := by
    have := (SemiRigid.isPullback_whiskerRight κ X).flip
    rw [hκ] at this
    exact this
  have key := fst_comp_eq_snd_comp (fun σ : C ≃ₐ[K] C => σ.toAlgHom)
    GaloisDescent.mem_range_algebraMap_of_forall_algEquiv H Y.hom f.left (Over.mk b ⊗ X).hom
    ((Over.w f).trans (Over.w (κ ▷ X)).symm) fun σ => by
      have hσ : spMap (σ : C →+* C) ≫ spMap (algebraMap K C) = spMap (algebraMap K C) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact σ.toAlgHom.comp_algebraMap
      let s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b) :=
        Over.homMk (spMap (σ : C →+* C)) (by
          change spMap (σ : C →+* C) ≫ spMap (algebraMap K C) ≫ b = spMap (algebraMap K C) ≫ b
          rw [reassoc_of% hσ])
      have hsκ : s ≫ κ = κ := Over.OverMorphism.ext (by
        rw [Over.comp_left, hκ]; exact hσ)
      have e : GaloisDescent.twist H σ.toAlgHom = (s ▷ X).left := by
        apply H.hom_ext
        · rw [GaloisDescent.twist_fst, ← Over.comp_left, ← comp_whiskerRight, hsκ]
        · rw [GaloisDescent.twist_snd]
          exact congrArg (·.left) (whiskerRight_fst s X).symm
      rw [e]
      exact congrArg (·.left) (hf σ s rfl)
  obtain ⟨g, hg⟩ := SemiRigid.exists_desc (κ ▷ X) f fun Z a c h => by
    have h' : a.left ≫ (κ ▷ X).left = c.left ≫ (κ ▷ X).left := congrArg (·.left) h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← pullback.lift_fst a.left c.left h', Category.assoc, key,
      pullback.lift_snd_assoc]
  have := SemiRigid.epi_of_fpqc (κ ▷ X)
  exact ⟨g, hg, fun g' hg' => (cancel_epi (κ ▷ X)).1 (hg'.trans hg.symm)⟩

end GlobalTheory.InvariantMorDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphismStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_descent_automorphism_invariant_morphism : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  first | exact @GlobalTheory.InvariantMorDescent.existsUnique_desc | exact GlobalTheory.InvariantMorDescent.existsUnique_desc | (intros; apply GlobalTheory.InvariantMorDescent.existsUnique_desc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SummableEvTOfQMap
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
open scoped BigOperators
noncomputable section
namespace GlobalTheory.SeriesCompare
section Alg
variable {O : Type} [CommRing O] {N : NumD O}

theorem wp_level {k m L : ℕ} (hL : L = k * m) (P Q : N.QT L) (p q : N.QT k) (h₁ : p.1.1 = P.1.1) (h₂ : p.1.2 = P.1.2 ^ m)
    (h₃ : Q.1.1.toAdd = m • q.1.1.toAdd) (h₄ : Q.1.2 = q.1.2) : N.wp P Q = N.wp p q := by
  have a := WpPairing.s_nsmul N P.1.2 m q.1.1.toAdd
  have b := P.1.2.pow_s m q.1.1.toAdd
  have c := CubeBalance.cubN_mul N.cub m k q.1.2.b P.1.2.b
  have d := CubeBalance.cubN_mul N.cub k m P.1.2.b q.1.2.b
  have e := CubeBalance.cubN_swap N.cub k m q.1.2.b P.1.2.b
  rw [N.QT_pow_b] at c e
  rw [mul_comm m k, ← hL] at c
  rw [← hL] at d
  rw [NumD.wp, NumD.wp, NumD.tk, NumD.tk, NumD.tk, NumD.tk, h₁, h₂, h₃, h₄, NumD.Gt.pow_b, c, d]
  have E := fun {p q : Oˣ} (e : p = q) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have e := E e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a b e ⊢
  linear_combination (norm := abel) a - b - e

def cg (N : NumD O) : N.Gt →* N.Gt ⧸ N.ioHom.range := QuotientGroup.mk' _

theorem cg_eq_one {g : N.Gt} : cg N g = 1 ↔ ∃ y, g = N.io y :=
  (QuotientGroup.eq_one_iff g).trans ⟨fun ⟨y, h⟩ => ⟨y.toAdd, h.symm⟩, fun ⟨y, h⟩ => ⟨Multiplicative.ofAdd y, h.symm⟩⟩

theorem cg_pow {k : ℕ} (p : N.QT k) : cg N p.1.2 ^ k = 1 := by
  rw [← map_pow]; exact cg_eq_one.2 ⟨_, N.mem_QT.1 p.2⟩

theorem exists_rep {g : N.Gt} {d : ℕ} (h : cg N g ^ d = 1) : ∃ p : N.QT d, p.1.2 = g := by
  rw [← map_pow] at h
  obtain ⟨y, hy⟩ := cg_eq_one.1 h
  exact ⟨⟨(Multiplicative.ofAdd y, g), hy⟩, rfl⟩

theorem cg_of_qEq {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') : cg N p.1.2 = cg N p'.1.2 := by
  obtain ⟨z, -, h⟩ := h
  rw [h, map_mul, cg_eq_one.2 ⟨z, rfl⟩, mul_one]

theorem qEq_iff_cg (hio : Function.Injective N.io) {k : ℕ} {p p' : N.QT k} : N.QEq p p' ↔ cg N p.1.2 = cg N p'.1.2 := by
  refine ⟨cg_of_qEq, fun h => ?_⟩
  obtain ⟨z, hz⟩ := cg_eq_one.1 (show cg N (p.1.2⁻¹ * p'.1.2) = 1 by rw [map_mul, map_inv, h, inv_mul_cancel])
  have e : p'.1.2 = p.1.2 * N.io z := by rw [← hz, mul_inv_cancel_left]
  refine ⟨z, hio ?_, e⟩
  rw [N.io_add, N.io_nsmul, ← N.mem_QT.1 p.2, ← N.mem_QT.1 p'.2, e, mul_pow]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.wp p q = N.wp p' q' := by
  rw [WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]

def up {k m L : ℕ} (hL : L = k * m) (p : N.QT k) : N.QT L :=
  ⟨(p.1.1 ^ m, p.1.2), by rw [NumD.mem_QT, hL, pow_mul, N.mem_QT.1 p.2, toAdd_pow, NumD.io_nsmul]⟩

theorem wp_level_cg (hio : Function.Injective N.io) {k m L : ℕ} (hL : L = k * m) (P Q : N.QT L) (p q : N.QT k)
    (h₂ : cg N p.1.2 = cg N P.1.2 ^ m) (h₄ : cg N Q.1.2 = cg N q.1.2) : N.wp P Q = N.wp p q := by
  let p₀ : N.QT k := ⟨(P.1.1, P.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, mul_comm m k, ← hL]; exact N.mem_QT.1 P.2⟩
  rw [wp_congr (show N.QEq P P from ⟨0, by simp, by simp⟩) ((qEq_iff_cg hio (p' := up hL q)).2 h₄),
    wp_congr ((qEq_iff_cg hio (p' := p₀)).2 (h₂.trans (map_pow _ _ _).symm)) (show N.QEq q q from ⟨0, by simp, by simp⟩)]
  exact wp_level hL _ _ _ _ rfl rfl rfl rfl
end Alg

theorem io_injective {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (h : N.Int q) :
    Function.Injective N.io := by
  refine fun a b hab => Multiplicative.ofAdd.injective ((injective_iff_map_eq_one N.ioHom).2 (fun y hy => ?_) hab)
  by_contra h0
  have e := h.norm_τ y.toAdd y.toAdd
  have t : N.τ y.toAdd y.toAdd = 1 := congrArg (fun g : N.Gt => g.s y.toAdd) hy
  rw [t, Units.val_one, norm_one, eq_comm, Real.exp_eq_one_iff, QuadraticMap.polar_self, neg_eq_zero, two_smul] at e
  have q0 : q y.toAdd = 0 := by linarith
  have inj : Function.Injective fun m : ℤ => m • y.toAdd := smul_left_injective ℤ (fun h => h0 h)
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have : (q : N.X → ℝ) ∘ (fun m : ℤ => m • y.toAdd) = fun _ => 0 := funext fun m => by
    simp [QuadraticMap.map_smul, q0]
  rw [this] at t₁
  exact (Filter.not_tendsto_const_atTop (0 : ℝ) Filter.cofinite) t₁

section Tower
variable {C : Type} [Field C] {N N' : NumD C} {n : ℕ} (w : TowerIso N N' n)

def Gr (x : N.Gt ⧸ N.ioHom.range) (x' : N'.Gt ⧸ N'.ioHom.range) : Prop :=
  ∃ j a, cg N a.1.2 = x ∧ cg N' (w.io j a).1.2 = x'

theorem gr_up {j j' : ℕ} (h : j ≤ j') (a : N.QT ((n ^ j) ^ 2)) :
    ∃ a' : N.QT ((n ^ j') ^ 2), cg N a'.1.2 = cg N a.1.2 ∧ cg N' (w.io j' a').1.2 = cg N' (w.io j a).1.2 := by
  induction j', h using Nat.le_induction with
  | base => exact ⟨a, rfl, rfl⟩
  | succ i _ ih =>
    obtain ⟨b, h₁, h₂⟩ := ih
    have e : (n ^ (i + 1)) ^ 2 = (n ^ i) ^ 2 * n ^ 2 := by ring
    exact ⟨up e b, h₁, (cg_of_qEq (w.incl i b (up e b) (up e (w.io i b)) rfl rfl rfl rfl)).trans h₂⟩

variable {w}
theorem Gr.common {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : ∃ j a b, cg N a.1.2 = x ∧ cg N' (w.io j a).1.2 = x' ∧
    cg N b.1.2 = y ∧ cg N' (w.io j b).1.2 = y' := by
  obtain ⟨i, a, rfl, rfl⟩ := h
  obtain ⟨j, b, rfl, rfl⟩ := h'
  obtain ⟨a', h₁, h₂⟩ := gr_up w (le_max_left i j) a
  obtain ⟨b', h₃, h₄⟩ := gr_up w (le_max_right i j) b
  exact ⟨_, a', b', h₁, h₂, h₃, h₄⟩

theorem Gr.mul {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : Gr w (x * y) (x' * y') := by
  obtain ⟨j, a, b, rfl, rfl, rfl, rfl⟩ := h.common h'
  exact ⟨j, a * b, map_mul _ _ _, (cg_of_qEq (w.mul j a b)).trans (map_mul _ _ _)⟩

theorem gr_one : Gr w 1 1 := by
  refine ⟨0, 1, map_one _, ?_⟩
  have := (cg_of_qEq (w.mul 0 1 1)).trans (map_mul _ _ _)
  rw [mul_one] at this
  exact left_eq_mul.1 this

theorem Gr.pow {x x'} (h : Gr w x x') (m : ℕ) : Gr w (x ^ m) (x' ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact gr_one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

variable (hio : Function.Injective N.io) (hio' : Function.Injective N'.io)
include hio hio'
theorem Gr.eq_iff {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : x = y ↔ x' = y' := by
  obtain ⟨j, a, b, rfl, rfl, rfl, rfl⟩ := h.common h'
  rw [← qEq_iff_cg hio, ← qEq_iff_cg hio', w.eqv]

theorem Gr.pow_eq_one_iff {x x'} (h : Gr w x x') (m : ℕ) : x ^ m = 1 ↔ x' ^ m = 1 := (h.pow m).eq_iff hio hio' gr_one

theorem Gr.wp (hd : ∀ (j : ℕ) (g : N.Gt), ∃ g' : N.Gt, g' ^ n ^ j = g) {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (h : Gr w (cg N p.1.2) (cg N' p'.1.2)) (h' : Gr w (cg N q.1.2) (cg N' q'.1.2)) : N'.wp p' q' = N.wp p q := by
  obtain ⟨j, a, b, a₁, a₂, b₁, b₂⟩ := h.common h'
  obtain ⟨k₀, hk⟩ := Nat.gcd_dvd_left k ((n ^ j) ^ 2)
  obtain ⟨l₀, hl⟩ := Nat.gcd_dvd_right k ((n ^ j) ^ 2)
  generalize hdd : Nat.gcd k ((n ^ j) ^ 2) = d at hk hl
  have t₁ : cg N p.1.2 ^ d = 1 := hdd ▸ pow_gcd_eq_one.2 ⟨cg_pow p, a₁ ▸ cg_pow a⟩
  have t₂ : cg N q.1.2 ^ d = 1 := hdd ▸ pow_gcd_eq_one.2 ⟨cg_pow q, b₁ ▸ cg_pow b⟩
  obtain ⟨p₁, hp₁⟩ := exists_rep t₁
  obtain ⟨q₁, hq₁⟩ := exists_rep t₂
  obtain ⟨p₁', hp₁'⟩ := exists_rep ((h.pow_eq_one_iff hio hio' d).1 t₁)
  obtain ⟨q₁', hq₁'⟩ := exists_rep ((h'.pow_eq_one_iff hio hio' d).1 t₂)
  rw [wp_level_cg hio hk p q (p₁ ^ k₀) q₁ (by rw [← hp₁, ← map_pow]; rfl) (by rw [hq₁]),
    wp_level_cg hio' hk p' q' (p₁' ^ k₀) q₁' (by rw [← hp₁', ← map_pow]; rfl) (by rw [hq₁']),
    WpPairing.wp_pow_left, WpPairing.wp_pow_left]
  congr 1
  obtain ⟨g, hg⟩ := hd (j * 2) p.1.2
  have hg' : cg N (g ^ d) ^ l₀ = cg N p.1.2 := by rw [← map_pow, ← pow_mul, ← hl, ← pow_mul, hg]
  obtain ⟨P, hP⟩ := exists_rep (g := g ^ d) (d := (n ^ j) ^ 2) (by rw [hl, mul_comm, pow_mul, hg', t₁])
  have G : Gr w (cg N P.1.2 ^ l₀) (cg N' (w.io j P).1.2 ^ l₀) := Gr.pow ⟨j, P, rfl, rfl⟩ l₀
  rw [← wp_level_cg hio hl P b p₁ q₁ (by rw [hp₁, hP, hg']) (by rw [hq₁, b₁]),
    ← wp_level_cg hio' hl (w.io j P) (w.io j b) p₁' q₁'
      (by rw [hp₁']; exact (h.eq_iff hio hio' G).1 (by rw [hP, hg'])) (by rw [hq₁', b₂]), w.wp]
end Tower

section MatchTower
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

def SameMatch (mt : Match N N' n) (w : TowerIso N N' n) : Prop :=
  ∀ j p p', mt.r ((n ^ j) ^ 2) p p' ↔ N'.QEq (w.io j p) p'

theorem exists_match (hio : Function.Injective N.io) (hio' : Function.Injective N'.io) (hn : n ≠ 0)
    (hd : ∀ (j : ℕ) (g : N.Gt), ∃ g' : N.Gt, g' ^ n ^ j = g)
    (hc : ∀ j (p p' : N'.QT ((n ^ j) ^ 2)), N'.QEq p p' → N'.tx (n ^ j) p' = N'.tx (n ^ j) p)
    (w : TowerIso N N' n) {c₀ : C} (h0 : c₀ ≠ 0) (hw : w.Proportional c₀) :
    ∃ mt : Match N N' n, mt.c₀ = c₀ ∧ SameMatch mt w := by
  have key : ∀ j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)),
      Gr w (cg N p.1.2) (cg N' p'.1.2) ↔ N'.QEq (w.io j p) p' := fun j p p' => by
    have G : Gr w (cg N p.1.2) (cg N' (w.io j p).1.2) := ⟨j, p, rfl, rfl⟩
    rw [qEq_iff_cg hio']
    exact ⟨fun h => (G.eq_iff hio hio' h).1 rfl, fun h => h ▸ G⟩
  refine ⟨{
    r := fun k p p' => k ≠ 0 ∧ Gr w (cg N p.1.2) (cg N' p'.1.2)
    tot := fun j p => ?_
    cotot := fun j p' => ?_
    mul := fun k p q p' q' h h' => ⟨h.1, by
      have := h.2.mul h'.2
      rwa [← map_mul, ← map_mul] at this⟩
    eqv := fun k p q p' q' h e => ?_
    inj := fun k p q p' h h' => (qEq_iff_cg hio).2 ((h.2.eq_iff hio hio' h'.2).2 rfl)
    incl := fun k k' p p' q q' hk _ b _ d => by rw [b, d, mul_ne_zero_iff, and_iff_left hk]
    wp := fun k p q p' q' h h' => Gr.wp hio hio' hd h.2 h'.2
    c₀ := c₀
    c₀_ne := h0
    tx := fun j p p' h => ?_ }, rfl,
    fun j p p' => (and_iff_right (pow_ne_zero _ (pow_ne_zero _ hn))).trans (key j p p')⟩
  · have G : Gr w (cg N p.1.2) _ := ⟨j, up (sq (n ^ j)) p, rfl, rfl⟩
    obtain ⟨p', hp'⟩ := exists_rep ((G.pow_eq_one_iff hio hio' _).1 (cg_pow p))
    exact ⟨p', pow_ne_zero _ hn, hp' ▸ G⟩
  · obtain ⟨a, ha⟩ := w.onto j (up (sq (n ^ j)) p')
    have G : Gr w (cg N a.1.2) (cg N' p'.1.2) := ⟨j, a, rfl, cg_of_qEq ha⟩
    obtain ⟨p, hp⟩ := exists_rep ((G.pow_eq_one_iff hio hio' _).2 (cg_pow p'))
    exact ⟨p, pow_ne_zero _ hn, hp ▸ G⟩
  · rw [qEq_iff_cg hio', ← cg_of_qEq e]
    exact ⟨fun h' => (h.2.eq_iff hio hio' h'.2).1 rfl, fun h' => ⟨h.1, h' ▸ h.2⟩⟩
  · obtain ⟨v, h₁, h₂⟩ := hw j p
    rw [hc j _ _ ((key j p p').1 h.2), NumD.tx, NumD.tx, h₁.tsum_eq, h₂.tsum_eq]

theorem r_incl (mt : Match N N' n) {k m L : ℕ} (hL : L = k * m) (hm : m ≠ 0) (p : N.QT k) (p' : N'.QT k) (q : N.QT L)
    (q' : N'.QT L) (a : q.1.1 = p.1.1 ^ m) (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ m) (d : q'.1.2 = p'.1.2) :
    mt.r k p p' ↔ mt.r L q q' := by
  subst hL
  exact mt.incl k m p p' q q' hm a b c d

theorem exists_tower (hn : n ≠ 0) (mt : Match N N' n) : ∃ w : TowerIso N N' n, SameMatch mt w := by
  have t : ∀ j (p : N.QT ((n ^ j) ^ 2)), ∃ p', mt.r _ p p' := fun j => by rw [← pow_mul]; exact mt.tot _
  have t' : ∀ j (p' : N'.QT ((n ^ j) ^ 2)), ∃ p, mt.r _ p p' := fun j => by rw [← pow_mul]; exact mt.cotot _
  choose f hf using t
  have key : ∀ j p p', mt.r ((n ^ j) ^ 2) p p' ↔ N'.QEq (f j p) p' := fun j p p' =>
    mt.eqv _ p p _ _ (hf j p) (show N.QEq p p from ⟨0, by simp, by simp⟩)
  exact ⟨{
    io := f
    eqv := fun j p q => ⟨fun h => mt.inj _ _ _ _ ((key j _ _).2 h) (hf j q), fun h => (mt.eqv _ _ _ _ _ (hf j p) h).1 (hf j q)⟩
    onto := fun j p' => (t' j p').imp fun p h => (key j _ _).1 h
    mul := fun j p q => (key j _ _).1 (mt.mul _ _ _ _ _ (hf j p) (hf j q))
    incl := fun j p q q' a b c d => (key _ _ _).1 ((r_incl mt (m := n ^ 2) (by ring) (pow_ne_zero _ hn) p (f j p) q q'
      (Multiplicative.toAdd.injective a) b (Multiplicative.toAdd.injective c) d).1 (hf j p))
    wp := fun j p q => mt.wp _ _ _ _ _ (hf j p) (hf j q) }, key⟩

theorem SameMatch.proportional {mt : Match N N' n} {w : TowerIso N N' n} (h : SameMatch mt w)
    (hs : ∀ j p, Summable (N.txT (n ^ j) p)) (hs' : ∀ j p, Summable (N'.txT (n ^ j) p)) : w.Proportional mt.c₀ :=
  fun j p => ⟨_, (hs j p).hasSum, by
    have := mt.tx j p _ ((h j p _).2 (show N'.QEq (w.io j p) (w.io j p) from ⟨0, by simp, by simp⟩))
    rw [NumD.tx, NumD.tx] at this
    rw [← this]
    exact (hs' j _).hasSum⟩
end MatchTower

section Sum
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem summable_evT (h : N.Int q) {m j : ℕ} (hm : m ≠ 0) (hj : j ≠ 0) (p : N.QT (m ^ 2)) (r : N.QT j) :
    Summable (N.evT m p r.1.2) := by
  obtain ⟨s, hs⟩ := exists_rep (g := (r.1.2 * p.1.2) ^ m) (d := m * j) (by
    rw [map_pow, ← pow_mul, ← mul_assoc, ← sq, map_mul, mul_pow, pow_mul (cg N p.1.2), cg_pow, mul_comm (m ^ 2) j, pow_mul,
      cg_pow, one_pow, one_pow, mul_one])
  have := summable_vt_QT C N q h _ (mul_ne_zero hm hj) s
  rw [hs] at this
  exact this.mul_left _

theorem summable_txT (h : N.Int q) {m : ℕ} (hm : m ≠ 0) (p : N.QT (m ^ 2)) : Summable (N.txT m p) :=
  (summable_evT h hm one_ne_zero p 1).congr (TateInh.evT_one N m p)
end Sum

section Hom
variable {O : Type} [CommRing O] {N N' : NumD O} (I : NumD.Hom (RingHom.id O) N N')

def gMap : N.Gt →* N'.Gt :=
  have H := NumD.hom_transport O O _ N N' I
  MonoidHom.mk' (fun g => (H.1 g).choose) fun g h =>
    (H.1 _).unique (H.1 _).choose_spec.1 (H.2.1 _ _ _ _ (H.1 g).choose_spec.1 (H.1 h).choose_spec.1)

theorem rel_iff {g : N.Gt} {g' : N'.Gt} : I.Rel g g' ↔ g' = gMap I g :=
  have H := (NumD.hom_transport O O _ N N' I).1 g
  ⟨fun h => H.unique h H.choose_spec.1, fun h => h ▸ H.choose_spec.1⟩

theorem gMap_io (y : N.X) : gMap I (N.io y) = N'.io (I.e y) :=
  ((rel_iff I).1 ((NumD.hom_transport O O _ N N' I).2.2.1 y)).symm

def qMap (k : ℕ) : N.QT k →* N'.QT k :=
  MonoidHom.mk' (fun p => ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), gMap I p.1.2), by
    rw [NumD.mem_QT, ← map_pow, N.mem_QT.1 p.2]; exact gMap_io I _⟩)
    fun p q => Subtype.ext (Prod.ext (map_add I.e _ _) (map_mul (gMap I) _ _))

theorem qMap_iff {k : ℕ} {p : N.QT k} {p' : N'.QT k} :
    (p'.1.1.toAdd = I.e p.1.1.toAdd ∧ I.Rel p.1.2 p'.1.2) ↔ p' = qMap I k p :=
  ⟨fun h => Subtype.ext (Prod.ext h.1 ((rel_iff I).1 h.2)), fun h => h ▸ ⟨rfl, (rel_iff I).2 rfl⟩⟩

theorem qMap_qTriv (k : ℕ) (z : N.X) : qMap I k (N.qTriv k z) = N'.qTriv k (I.e z) :=
  Subtype.ext (Prod.ext (map_nsmul I.e k z) (gMap_io I z))

theorem qEq_qMap {k : ℕ} (hi : Function.Injective (qMap I k)) {p q : N.QT k} :
    N'.QEq (qMap I k p) (qMap I k q) ↔ N.QEq p q := by
  rw [NumD.qEq_iff, NumD.qEq_iff, ← I.e.exists_congr_right]
  exact exists_congr fun z => by rw [← hi.eq_iff, map_mul, qMap_qTriv]; rfl

theorem wp_qMap {k : ℕ} (p q : N.QT k) : N'.wp (qMap I k p) (qMap I k q) = N.wp p q :=
  (NumD.hom_transport O O _ N N' I).2.2.2.1 k p q _ _ rfl ((rel_iff I).2 rfl) rfl ((rel_iff I).2 rfl)
end Hom

section Move
variable {C : Type} [NormedField C] {N N' M M' : NumD C} {n : ℕ} (I : NumD.Hom (RingHom.id C) N M)
  (I' : NumD.Hom (RingHom.id C) N' M')

theorem hasSum_qMap (hl : I.lam = 1) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (v : C) :
    HasSum (M.txT m (qMap I _ p)) v ↔ HasSum (N.txT m p) v := by
  rw [← I.e.toEquiv.hasSum_iff]
  refine iff_of_eq (congrArg (HasSum · v) (funext fun χ => ?_))
  have := ((NumD.hom_transport C C _ N M I).2.2.2.2 m hm p (qMap I _ p) rfl ((rel_iff I).2 rfl) χ).1
  rw [hl, Units.val_one, one_mul] at this
  exact this

theorem summable_evT_of_qMap {m j : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (r : N.QT j)
    (h : Summable (M.evT m (qMap I _ p) (qMap I _ r).1.2)) : Summable (N.evT m p r.1.2) := by
  refine ((I.e.toEquiv.summable_iff.2 h).mul_left (((I.lam * I.h r.1.2.b ^ (m ^ 2))⁻¹ : Cˣ) : C)).congr fun χ => ?_
  have := ((NumD.hom_transport C C _ N M I).2.2.2.2 m hm p (qMap I _ p) rfl ((rel_iff I).2 rfl) χ).2 r.1.2 _ ((rel_iff I).2 rfl)
  exact (congrArg _ this).trans (Units.inv_mul_cancel_left _ _)

theorem exists_move (hI : ∀ k, Function.Bijective (qMap I k)) (hI' : ∀ k, Function.Bijective (qMap I' k))
    (w : TowerIso N N' n) : ∃ w₀ : TowerIso M M' n, ∀ j p, w₀.io j (qMap I _ p) = qMap I' _ (w.io j p) := by
  let E := fun k => MulEquiv.ofBijective (qMap I k) (hI k)
  have hE : ∀ k p, qMap I k ((E k).symm p) = p := fun k p => (E k).apply_symm_apply p
  have g : ∀ {k l} (p : N.QT k) (q : N.QT l), (qMap I _ q).1.2 = (qMap I _ p).1.2 → q.1.2 = p.1.2 := fun p q h => by
    have := (hI 0).1 (a₁ := ⟨(1, q.1.2), by rw [NumD.mem_QT, pow_zero]; exact N.io_zero.symm⟩)
      (a₂ := ⟨(1, p.1.2), by rw [NumD.mem_QT, pow_zero]; exact N.io_zero.symm⟩) (Subtype.ext (Prod.ext rfl h))
    exact congrArg (fun x : N.QT 0 => x.1.2) this
  refine ⟨{
    io := fun j p => qMap I' _ (w.io j ((E _).symm p))
    eqv := fun j p q => by rw [qEq_qMap I' (hI' _).1, w.eqv, ← qEq_qMap I (hI _).1, hE, hE]
    onto := fun j p' => ?_
    mul := fun j p q => by rw [← map_mul, map_mul (E _).symm, qEq_qMap I' (hI' _).1]; exact w.mul _ _ _
    incl := fun j p q q' a b c d => ?_
    wp := fun j p q => by rw [wp_qMap, w.wp, ← wp_qMap I, hE, hE] }, fun j p =>
      congrArg (fun x => qMap I' _ (w.io j x)) ((E _).symm_apply_apply p)⟩
  · obtain ⟨p', rfl⟩ := (hI' _).2 p'
    obtain ⟨p, hp⟩ := w.onto j p'
    exact ⟨E _ p, by rw [MulEquiv.symm_apply_apply, qEq_qMap I' (hI' _).1]; exact hp⟩
  · have e : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    have h' : q' = qMap I' _ (up e (w.io j ((E _).symm p))) :=
      Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (c.trans (map_nsmul I'.e _ _).symm)) d)
    rw [h', qEq_qMap I' (hI' _).1]
    refine w.incl j _ _ _ (I.e.injective ?_) (g _ _ (by rw [hE, hE, b])) rfl rfl
    rw [map_nsmul]
    exact (congrArg (fun x : M.QT _ => x.1.1.toAdd) (hE _ q)).trans (a.trans
      (congrArg (fun x : M.QT _ => n ^ 2 • x.1.1.toAdd) (hE _ p)).symm)
end Move
end GlobalTheory.SeriesCompare
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
noncomputable section
namespace GlobalTheory.SeriesCompare

section Base
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {C : Type} [NormedField C] [Algebra (FractionRing V) C]

theorem admissible_base_of_complete_dvr (hV : GlobalTheory.LN.CDvr V) : AdmBase V (IsLocalRing.maximalIdeal V) := by
  obtain ⟨h₁, h₂, h₃⟩ := hV
  exact ⟨inferInstance, inferInstance, inferInstance, h₂⟩

theorem charZero_of (hV : GlobalTheory.LN.CDvr V) : CharZero C := by
  haveI := hV.2.2
  exact (RingHom.charZero_iff (ϕ := (algebraMap (FractionRing V) C).comp (algebraMap V _))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V _))).1 inferInstance

theorem exists_one_lt_norm (hV : GlobalTheory.LN.CDvr V) (hC : CExt V (IsLocalRing.maximalIdeal V) C) : ∃ x : C, 1 < ‖x‖ := by
  haveI := hV.1
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 (IsDiscreteValuationRing.not_a_field V)
  refine ⟨(algebraMap (FractionRing V) C (algebraMap V _ a))⁻¹, ?_⟩
  rw [norm_inv]
  refine (one_lt_inv₀ (norm_pos_iff.2 ?_)).2 (hC.2 a ha)
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 h0)

theorem isUnit_iff_norm (hC : CExt V (IsLocalRing.maximalIdeal V) C) (n : ℕ) : IsUnit (n : V) ↔ ‖(n : C)‖ = 1 := by
  constructor
  · intro hu
    obtain ⟨m, hm⟩ := hu.exists_right_inv
    have a₁ := hC.1 n
    have a₂ := hC.1 m
    have a₃ := congrArg (fun x => ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖) hm
    simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a₁ a₃
    refine le_antisymm a₁ ?_
    calc (1 : ℝ) = _ := a₃.symm
      _ ≤ ‖(n : C)‖ * 1 := by gcongr
      _ = _ := _root_.mul_one _
  · intro h
    by_contra hu
    have := hC.2 n hu
    rw [map_natCast, map_natCast, h] at this
    exact lt_irrefl _ this
end Base

section Gauge
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]

theorem qkExt_id {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem qPt_unique' {N : NumD C} (ν : NumOf D C N) {k : ℕ} {p : QkPt D C k} {q q' : N.QT k} (h : ν.QPt p q)
    (h' : ν.QPt p q') : q = q' :=
  Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (ν.eX.injective (h.1.trans h'.1.symm))) (ν.pt_unique h.2 h'.2))

variable (he : D.PsiEven) (hb : D.TauBimult) [IsAlgClosed C] {N : NumD C} (ν : NumOf D C N)
include he hb

theorem exists_val {k : ℕ} (p : QkPt D C k) : ∃ q, ν.QPt p q :=
  (((GtValues.points_correspond R D he hb C N ν).2.2.2.2 k).1 p).exists

theorem exists_pt {k : ℕ} (q : N.QT k) : ∃ p, ν.QPt p q :=
  ((GtValues.points_correspond R D he hb C N ν).2.2.2.2 k).2.1 q

theorem pt_unique {k : ℕ} {p p' : QkPt D C k} {q : N.QT k} (h : ν.QPt p q) (h' : ν.QPt p' q) : p = p' :=
  TorusExt.qk_ext (h.1.symm.trans h'.1) (((GtValues.points_correspond R D he hb C N ν).2.1 _).unique h.2 h'.2)

theorem exists_gaugeMap {M : NumD C} (ν₀ : NumOf D C M) (hth : ν₀.th = ν.th) :
    ∃ I : NumD.Hom (RingHom.id C) N M, I.lam = 1 ∧ (∀ k, Function.Bijective (qMap I k)) ∧
      ∀ k (p : QkPt D C k) q, ν.QPt p q ↔ ν₀.QPt p (qMap I k q) := by
  obtain ⟨I, hl, -, hI⟩ := GaugeHom.exists_hom R D C C (RingHom.id C) (RingHom.id_comp _) N M ν ν₀ hth
  have a : ∀ k (p : QkPt D C k) q q', ν.QPt p q → ν₀.QPt p q' → q' = qMap I k q := fun k p q q' h h' =>
    (qMap_iff I).1 (hI k p p q q' (qkExt_id p) h h')
  have b : ∀ k (p : QkPt D C k) q, ν.QPt p q → ν₀.QPt p (qMap I k q) := fun k p q h => by
    obtain ⟨q', h'⟩ := exists_val he hb ν₀ p
    exact a k p q q' h h' ▸ h'
  have c : ∀ k (p : QkPt D C k) q, ν₀.QPt p (qMap I k q) → ν.QPt p q := fun k p q h => by
    obtain ⟨p', h'⟩ := exists_pt he hb ν q
    exact pt_unique he hb ν₀ (b k p' q h') h ▸ h'
  refine ⟨I, hl, fun k => ⟨fun q q' h => ?_, fun q' => ?_⟩, fun k p q => ⟨b k p q, c k p q⟩⟩
  · obtain ⟨p, hp⟩ := exists_pt he hb ν q
    exact qPt_unique' ν hp (c k p q' (h ▸ b k p q hp))
  · obtain ⟨p, hp⟩ := exists_pt he hb ν₀ q'
    obtain ⟨q, hq⟩ := exists_val he hb ν p
    exact ⟨q, (a k p q q' hq hp).symm⟩
end Gauge

section Integral
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (D : DegData V (IsLocalRing.maximalIdeal V))
  {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing V) C]
  (hC : CExt V (IsLocalRing.maximalIdeal V) C) {N : NumD C} (ν : NumOf D.toPre C N)
include hV hC

theorem exists_integral : ∃ (M : NumD C) (ν₀ : NumOf D.toPre C M) (q : QuadraticMap ℤ M.X ℝ)
    (I : NumD.Hom (RingHom.id C) N M), ν₀.IntN ∧ M.Int q ∧ I.lam = 1 ∧ (∀ k, Function.Bijective (qMap I k)) ∧
      ∀ k (p : QkPt D.toPre C k) q, ν.QPt p q ↔ ν₀.QPt p (qMap I k q) := by
  let S : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl
  obtain ⟨J, hJ, hJ'⟩ := IntegralGauge.exists_integral_gauge V D.toPre C S fun r => (hS _).2 (hC.1 r)
  obtain ⟨M, ν₀, rfl, hth⟩ := GaugeValues.exists_numOf firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult C J hJ ν.th ν.th_gen
  have hI : ν₀.IntN := ⟨S, hS, hJ'⟩
  obtain ⟨q, hq⟩ := IntVal.main V _ (admissible_base_of_complete_dvr hV) D C hC M ν₀ hI
  obtain ⟨I, h⟩ := exists_gaugeMap D.psi_even D.tau_bimult ν ν₀ hth
  exact ⟨M, ν₀, q, I, hI, hq, h⟩


include ν in
theorem summable_of_data [CompleteSpace C] {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) :
    Summable (N.txT m p) ∧ ∀ j, j ≠ 0 → ∀ r : N.QT j, Summable (N.evT m p r.1.2) := by
  obtain ⟨M, ν₀, q, I, -, hq, hl, -⟩ := exists_integral hV D hC ν
  exact ⟨⟨_, (hasSum_qMap I hl hm p _).1 (summable_txT hq hm.pos.ne' _).hasSum⟩,
    fun j hj r => summable_evT_of_qMap I hm p r (summable_evT hq hm.pos.ne' hj _ _)⟩
end Integral

section Conclusions
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) {D D' : DegPre V} (he : D.PsiEven)
  (hb : D.TauBimult) (he' : D'.PsiEven) (hb' : D'.TauBimult)
include hV he hb he' hb'

theorem exists_pullDeg {C : Type} [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C] {N N' : NumD C}
    (ν : NumOf D C N) (ν' : NumOf D' C N') (J : NumD.Iso N N') (hJ : GeoIso ν ν' J.toIso) {k : ℕ} (hk : 3 ≤ k)
    (hσ : ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C k) (p' pσ' : QkPt D' C k) (q qσ : N.QT k) (qσ' : N'.QT k),
      QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ →
      ν'.QPt p' (qMap (TateInh.homOfIso J) k q) → ν'.QPt pσ' qσ' → N'.QEq (qMap (TateInh.homOfIso J) k qσ) qσ') :
    ∃ e : IsPullDeg (RingHom.id V) D D', ∀ (k : ℕ) (p : QkPt D C k) (p' : QkPt D' C k) (q : N.QT k),
      ν.QPt p q → ν'.QPt p' (qMap (TateInh.homOfIso J) k q) → Carries e p p' := by
  haveI := hV.1
  haveI := hV.2.2
  have hL := firstFiveLaws.1
  have hL2 := firstFiveLaws.2.1
  have hk0 : k ≠ 0 := by omega
  obtain ⟨φ, w, wv, g₁, g₂, g₃, g₄, g₅⟩ := hJ
  have pt : ∀ x, lift (𝟙 (TF (R := V) C)) (ν.eA x) ≫ φ.hom ≫ snd _ _ = ν'.eA (J.φ x) := fun x => by
    rw [← Category.assoc, g₃, lift_snd]
  have h1 : lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ D.P.A) ≫ φ.hom ≫ snd _ _ = 1 := by
    have := pt 1
    rwa [map_one, map_one, map_one] at this
  have inv : ∀ (σ : C ≃ₐ[FractionRing V] C) (s : TF (R := V) C ⟶ TF (R := V) C), s.left = spMap (σ : C →+* C) →
      s ▷ D.P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := fun σ s hs => by
    have hf : (σ : C →+* C).comp (algebraMap (FractionRing V) C) = algebraMap (FractionRing V) C :=
      RingHom.ext σ.commutes
    haveI : IsIso s.left := by
      rw [hs]
      exact inferInstanceAs (IsIso (Spec.map σ.toRingEquiv.toCommRingCatIso.hom))
    haveI : IsIso ((Over.forget _).map s) := this
    haveI : IsIso s := isIso_of_reflects_iso s (Over.forget _)
    refine GlobalTheory.T.polarisedIso_commutes_fieldAutomorphism_of_torsion hL _ D.P D'.P C _ φ g₁ h1 ⟨w, g₂⟩ k hk (Nat.cast_ne_zero.2 hk0) (asIso s) fun x hx => ?_
    obtain ⟨b, rfl⟩ := ν.eA.surjective x
    obtain ⟨g, rfl, hg⟩ := QStr.root_over N hk0 1 b (ν.eA.injective (by rw [map_pow, hx]; exact (map_one _).symm))
    let q : N.QT k := ⟨(1, g), hg.trans N.io_zero.symm⟩
    obtain ⟨p, hp⟩ := exists_pt he hb ν q
    obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (qMap (TateInh.homOfIso J) k q)
    obtain ⟨pσ, hpσ⟩ := (TorusExt.existsUnique_qkExt hb _ hf p).exists
    obtain ⟨pσ', hpσ'⟩ := (TorusExt.existsUnique_qkExt hb' _ hf p').exists
    obtain ⟨qσ, hqσ⟩ := exists_val he hb ν pσ
    obtain ⟨qσ', hqσ'⟩ := exists_val he' hb' ν' pσ'
    obtain ⟨z, hz, hz'⟩ := hσ σ p pσ p' pσ' q qσ qσ' hpσ hpσ' hp hqσ hp' hqσ'
    have y₁ : qσ.1.1.toAdd = q.1.1.toAdd := ν.eX.injective (hqσ.1.trans (hpσ.1.trans hp.1.symm))
    have y₂ : qσ'.1.1.toAdd = J.e q.1.1.toAdd := ν'.eX.injective (hqσ'.1.trans (hpσ'.1.trans hp'.1.symm))
    have z0 : z = 0 := by
      have : J.e q.1.1.toAdd = J.e q.1.1.toAdd + k • z := y₂.symm.trans (hz.trans (congrArg (fun t => J.e t + k • z) y₁))
      rw [left_eq_add, ← natCast_zsmul] at this
      exact (smul_eq_zero.1 this).resolve_left (Int.natCast_ne_zero.2 hk0)
    rw [z0, NumD.io_zero, _root_.mul_one] at hz'
    have rb : ∀ r : N.QT k, (qMap (TateInh.homOfIso J) k r).1.2.b = J.φ r.1.2.b := fun r =>
      ((qMap_iff (TateInh.homOfIso J)).2 rfl).2.1
    have b₁ : s ≫ ν.eA g.b = ν.eA qσ.1.2.b :=
      Over.OverMorphism.ext (by rw [hqσ.2.1, hpσ.2.1, ← hp.2.1, Over.comp_left, hs])
    have b₂ : s ≫ ν'.eA (J.φ g.b) = ν'.eA qσ'.1.2.b :=
      Over.OverMorphism.ext (by rw [hqσ'.2.1, hpσ'.2.1, ← hp'.2.1, Over.comp_left, hs, rb])
    rw [asIso_hom, b₁, pt, pt, b₂, hz', rb]
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_descent_automorphism_invariant_morphism (FractionRing V) C _ (jK V) D.P.A D'.P.A
    (haveI := D'.P.isAb.proper; inferInstance) (Over.homMk (jFK (R := V) C) rfl) rfl (φ.hom ≫ snd _ _) inv
  obtain ⟨Ψ, a₁, a₂, a₃⟩ := GlobalTheory.T.exists_iso_polarisedAbelianSchemes_dvr_of_fieldExtension hL hL2 V D.P D'.P C φ g₁ h1 ⟨w, g₂⟩ _ g hg
  obtain ⟨e, hc⟩ := GlobalTheory.T.exists_pullbackDegeneration_of_values_iso_dvr hL V D D' C N N' ν ν' J Ψ a₁ a₃ φ w g₁ a₂ g₂ g₃
    (fun x => (congrArg _ (g₄ 1).symm).trans ((g₅ x).trans (g₄ x)))
  exact ⟨e, fun k p p' q hq hq' => hc k p p' q _ hq hq' rfl ((qMap_iff (TateInh.homOfIso J)).2 rfl).2⟩

variable {C : Type} [NormedField C] [IsAlgClosed C] [Algebra (FractionRing V) C] {N N' : NumD C}
  (ν : NumOf D C N) (ν' : NumOf D' C N') {n : ℕ} {mt : Match N N' n} {w : TowerIso N N' n}

theorem inducedBy_of_onQ (hn : 2 ≤ n) (h : SameMatch mt w) {j : ℕ} (hj : 1 ≤ j) (hr : w.RationalAt ν ν' j)
    (H : ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso) :
    ∃ e : IsPullDeg (RingHom.id V) D D', w.InducedBy ν ν' e := by
  haveI : CharZero C := charZero_of hV
  obtain ⟨J, hQ, hJ⟩ := H
  have a : ∀ i (q : N.QT ((n ^ i) ^ 2)), N'.QEq (w.io i q) (qMap (TateInh.homOfIso J) _ q) := fun i q => by
    refine (h i _ _).1 ?_
    revert q
    rw [← pow_mul]
    exact fun q => hQ _ _ _ rfl ((qMap_iff (TateInh.homOfIso J)).2 rfl).2
  have E : Equivalence (N'.QEq (k := (n ^ j) ^ 2)) := by
    constructor
    · intro p
      exact ⟨0, by simp, by simp⟩
    ·
      rintro p p' ⟨z, hz, hz'⟩
      exact ⟨-z, by rw [hz, smul_neg, add_neg_cancel_right],
        by rw [hz', N'.io_neg, mul_inv_cancel_right]⟩
    ·
      rintro p p' p'' ⟨z, hz, hz'⟩ ⟨t, ht, ht'⟩
      exact ⟨z + t, by rw [ht, hz, smul_add, add_assoc],
        by rw [ht', hz', N'.io_add, _root_.mul_assoc]⟩
  obtain ⟨e, he⟩ := exists_pullDeg hV he hb he' hb' ν ν' J hJ (k := (n ^ j) ^ 2)
    (by
      have : 2 ≤ n ^ j := hn.trans (Nat.le_self_pow (by omega) n)
      nlinarith)
    fun σ p pσ p' pσ' q qσ qσ' a₁ a₂ a₃ a₄ a₅ a₆ =>
      E.trans (E.symm (a j qσ)) (hr σ p pσ p' pσ' q qσ _ qσ' a₁ a₂ a₃ a₄ a₅ a₆ (a j q))
  refine ⟨e, fun i q => ?_⟩
  obtain ⟨p, hp⟩ := exists_pt ‹D.PsiEven› hb ν q
  obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (qMap (TateInh.homOfIso J) _ q)
  exact ⟨p, p', _, hp, hp', he _ p p' q hp hp', a i q⟩


omit he hb he' hb' [IsAlgClosed C] in
theorem onQ_of_inducedBy (hn : n ≠ 0) (h : SameMatch mt w)
    (H : ∃ e : IsPullDeg (RingHom.id V) D D', w.InducedBy ν ν' e) :
    ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso := by
  haveI := hV.1
  obtain ⟨e, he⟩ := H
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.T.exists_geometric_values_iso_of_identification_dvr firstFiveLaws.1 V D D' e C N N' ν ν'
  refine ⟨J, fun j p p' h₁ h₂ => ?_, hJ⟩
  refine (r_incl mt (sq (n ^ j)) (pow_ne_zero _ hn) p p' (up (sq _) p) (up (sq _) p') rfl rfl rfl rfl).2 ((h j _ _).2 ?_)
  obtain ⟨r, r', q', a₁, a₂, a₃, a₄⟩ := he j (up (sq (n ^ j)) p)
  have b₁ := (qMap_iff (TateInh.homOfIso J)).1 (hc _ r r' _ q' a₁ a₂ a₃)
  have b₂ := (qMap_iff (TateInh.homOfIso J) (p := up (sq (n ^ j)) p) (p' := up (sq (n ^ j)) p')).1
    ⟨(congrArg (n ^ j • ·) h₁).trans (map_nsmul J.e _ _).symm, h₂⟩
  rw [b₂, ← b₁]
  exact a₄
end Conclusions

def RationalRel {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N N' : NumD C} {n : ℕ} (mt : Match N N' n) (ν : NumOf D C N) (ν' : NumOf D' C N')
    (j : ℕ) : Prop :=
  ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D C ((n ^ j) ^ 2)) (p' pσ' : QkPt D' C ((n ^ j) ^ 2))
    (q qσ : N.QT ((n ^ j) ^ 2)) (q' qσ' : N'.QT ((n ^ j) ^ 2)),
    QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → ν.QPt p q → ν.QPt pσ qσ → ν'.QPt p' q' → ν'.QPt pσ' qσ' →
    mt.r _ q q' → mt.r _ qσ qσ'

theorem SameMatch.rational_iff {V : Type} [CommRing V] [IsDomain V] {D D' : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N N' : NumD C} {n : ℕ} {mt : Match N N' n} {w : TowerIso N N' n} (h : SameMatch mt w)
    (ν : NumOf D C N) (ν' : NumOf D' C N') (j : ℕ) : RationalRel mt ν ν' j ↔ w.RationalAt ν ν' j := by
  simp only [RationalRel, TowerIso.RationalAt, h j]

def URecDvrSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (D D' : DegData V (IsLocalRing.maximalIdeal V))
      (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N N' : NumD C) (ν : NumOf D.toPre C N) (ν' : NumOf D'.toPre C N') (q : QuadraticMap ℤ N.X ℝ)
      (q' : QuadraticMap ℤ N'.X ℝ) (n : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Int q → N'.Int q' →
      N.Tors n D.toPre.P.g → N'.Tors n D'.toPre.P.g → ∀ mt : Match N N' n, (∃ j, 1 ≤ j ∧ RationalRel mt ν ν' j) →
      ∃ J : NumD.Iso N N', mt.OnQ J ∧ GeoIso ν ν' J.toIso

theorem uRecDvr_of_uRec (h : URecSt) : URecDvrSt :=
  fun V _ _ _ _ D D' C _ _ _ _ _ _ N N' ν ν' q q' n h₁ h₂ h₃ h₄ h₅ h₆ h₇ mt _ =>
    h V D.toPre D'.toPre D.psi_even D.tau_bimult D'.psi_even D'.tau_bimult C N N' ν ν' q q' n h₁ h₂ h₃ h₄ h₅ h₆ h₇ mt

theorem recognition_iff : RecognitionSt ↔ URecDvrSt := by
  constructor
  · rintro h V _ _ _ hV D D' C _ _ _ _ _ hC N N' ν ν' q q' n hn ho h1 hq hq' - - mt ⟨j, hj, hr⟩
    obtain ⟨w, hw⟩ := exists_tower hn.ne_zero mt
    exact onQ_of_inducedBy hV ν ν' hn.ne_zero hw (h V hV D D' n hn ho ((isUnit_iff_norm hC n).2 h1) C hC N N' ν ν' w mt.c₀
      (hw.proportional (fun j p => summable_txT hq (pow_ne_zero _ hn.ne_zero) p)
        fun j p => summable_txT hq' (pow_ne_zero _ hn.ne_zero) p) ⟨j, hj, (hw.rational_iff ν ν' j).1 hr⟩)
  · rintro h V _ _ _ hV D D' n hn ho hu C _ _ _ _ _ hC N N' ν ν' w c₀ hw ⟨j, hj, hr⟩
    letI : NontriviallyNormedField C := ⟨exists_one_lt_norm hV hC⟩
    haveI := hV.1
    have hL := firstFiveLaws.1
    have h1 := (isUnit_iff_norm hC n).1 hu
    have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    have hO : CExt V ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := IsLocalRing.maximalIdeal V) hr)⟩
    obtain ⟨M, ν₀, q, I, hI, hq, hl, hB, hP⟩ := exists_integral hV D hC ν
    obtain ⟨M', ν₀', q', I', hI', hq', hl', hB', hP'⟩ := exists_integral hV D' hC ν'
    have hT := ValuesTorsion.tors_of_integral hL firstFiveLaws.2.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) V _ D.psi_even D.tau_bimult C hO M ν₀
      hI n hn ho h1
    have hT' := ValuesTorsion.tors_of_integral hL firstFiveLaws.2.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) V _ D'.psi_even D'.tau_bimult C hO M'
      ν₀' hI' n hn ho h1
    obtain ⟨w₀, hw₀⟩ := exists_move I I' hB hB' w
    have hp₀ : w₀.Proportional c₀ := fun i p => by
      obtain ⟨p, rfl⟩ := (hB _).2 p
      obtain ⟨v, a, b⟩ := hw i p
      exact ⟨v, (hasSum_qMap I hl ho.pow p v).2 a, by rw [hw₀]; exact (hasSum_qMap I' hl' ho.pow _ _).2 b⟩
    have hc : ∀ i (p p' : M'.QT ((n ^ i) ^ 2)), M'.QEq p p' → M'.tx (n ^ i) p' = M'.tx (n ^ i) p := by
      rintro i p p' ⟨z, a, b⟩
      exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence C M' _ ho.pow p p' χ).1 z a b).trans
        ((Equiv.addRight (n ^ i • z)).tsum_eq fun χ => M'.txT (n ^ i) p χ)
    have h0 : c₀ ≠ 0 := by
      rintro rfl
      obtain ⟨t, -, -, ht⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C M' q' hq' n _ hn ho h1 hT' 1 le_rfl).2.2 1
      obtain ⟨p, hp⟩ := w₀.onto 1 (1 * t)
      obtain ⟨v, -, b⟩ := hp₀ 1 p
      exact ht ((hc 1 _ _ hp).trans (b.tsum_eq.trans (zero_mul v)))
    obtain ⟨mt, -, hm⟩ := exists_match (io_injective hq) (io_injective hq') hn.ne_zero
      (fun i => (QStr.qStructure C M n _ hnC hT i).2.1) hc w₀ h0 hp₀
    have hr₀ : w₀.RationalAt ν₀ ν₀' j := fun σ p pσ p' pσ' a aσ a' aσ' e₁ e₂ e₃ e₄ e₅ e₆ e₇ => by
      obtain ⟨a, rfl⟩ := (hB _).2 a
      obtain ⟨aσ, rfl⟩ := (hB _).2 aσ
      obtain ⟨a', rfl⟩ := (hB' _).2 a'
      obtain ⟨aσ', rfl⟩ := (hB' _).2 aσ'
      rw [hw₀, qEq_qMap I' (hB' _).1] at e₇ ⊢
      exact hr σ p pσ p' pσ' a aσ a' aσ' e₁ e₂ ((hP _ _ _).2 e₃) ((hP _ _ _).2 e₄) ((hP' _ _ _).2 e₅) ((hP' _ _ _).2 e₆) e₇
    obtain ⟨e, he⟩ := inducedBy_of_onQ hV D.psi_even D.tau_bimult D'.psi_even D'.tau_bimult ν₀ ν₀' hn.two_le hm hj hr₀
      (h V hV D D' C hC M M' ν₀ ν₀' q q' n hn ho h1 hq hq' hT hT' mt ⟨j, hj, (hm.rational_iff ν₀ ν₀' j).2 hr₀⟩)
    refine ⟨e, fun i a => ?_⟩
    obtain ⟨p, p', a', b₁, b₂, b₃, b₄⟩ := he i (qMap I _ a)
    obtain ⟨a', rfl⟩ := (hB' _).2 a'
    rw [hw₀, qEq_qMap I' (hB' _).1] at b₄
    exact ⟨p, p', a', (hP _ _ _).2 b₁, (hP' _ _ _).2 b₂, b₃, b₄⟩

end GlobalTheory.SeriesCompare
end
