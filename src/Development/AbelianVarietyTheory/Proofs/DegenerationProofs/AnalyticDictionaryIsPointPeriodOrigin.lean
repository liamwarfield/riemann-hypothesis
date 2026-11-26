module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleSections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_log_of_character {X : Type} [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℂˣ)
    (h : ∀ x y, φ (x + y) = φ x * φ y) : ∃ l : X →+ ℂ, ∀ x, (φ x : ℂ) = eTwoPi (l x) := by
  classical
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h0 : φ 0 = 1 := by
    have h00 := h 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (mul_one _).symm)
  let b := Module.Free.chooseBasis ℤ X
  let l : X →+ ℂ :=
    (b.constr ℤ fun i => Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)).toAddMonoidHom
  refine ⟨l, fun x => ?_⟩
  let f₁ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (φ x)
      map_zero' := by simp [h0]
      map_add' := fun x y => by simp [h] }
  let f₂ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (Units.mk0 (eTwoPi (l x)) (AnArc.e_ne_zero _))
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [AnArc.e_add] }
  have key : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show Additive.ofMul (φ (b i)) = Additive.ofMul (Units.mk0 (eTwoPi (l (b i))) (AnArc.e_ne_zero _))
    congr 1
    ext
    rw [Units.val_mk0]
    have hl : l (b i) = Complex.log (φ (b i)) / (2 * Real.pi * Complex.I) := by
      simp [l]
    rw [hl, eTwoPi, mul_div_cancel₀ _ hπ, Complex.exp_log (Units.ne_zero _)]
  have hx := congrArg (fun u : Additive ℂˣ => ((Additive.toMul u : ℂˣ) : ℂ)) (LinearMap.congr_fun key x)
  simpa [f₁, f₂] using hx

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O} (d : Dict N B)

theorem Dict.cube_val (x y z : Fin B.gB → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) =
      d.fr (x + y + z) * d.fr x * d.fr y * d.fr z := by
  have h := congrArg Units.val (d.ab.2.2.2.2.2.1 x y z)
  push_cast at h
  exact h

theorem Dict.existsUnique_isPt (v : B.V) : ∃! g, d.IsPt v g := by
  let E : B.X → ℂˣ := fun x => Units.mk0 (eTwoPi (v.1 x)) (AnArc.e_ne_zero _)
  let s : N.X → ℂˣ := fun χ =>
    E (d.eX.symm χ) * d.fr (B.ct (d.eX.symm χ)) * d.fr v.2 * (d.fr (B.ct (d.eX.symm χ) + v.2))⁻¹
  have hs : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') (d.ex v.2) = s χ * s χ' := by
    intro χ χ'
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    obtain ⟨x', rfl⟩ := d.eX.surjective χ'
    rw [← map_add d.eX, d.c_eq, d.c_eq]
    have h := d.cube_val (B.ct x) (B.ct x') v.2
    ext
    simp only [s, E, AddEquiv.symm_apply_apply, map_add (f := _), Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, AnArc.e_add]
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct x')) (d.ex v.2) : ℂ) =
        d.fr (B.ct x + B.ct x' + v.2) * d.fr (B.ct x) * d.fr (B.ct x') * d.fr v.2 /
          (d.fr (B.ct x + B.ct x') * d.fr (B.ct x + v.2) * d.fr (B.ct x' + v.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hθ]
    field_simp
  refine ⟨⟨d.ex v.2, s, hs⟩, ⟨rfl, fun x => ?_⟩, ?_⟩
  · simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [inv_mul_cancel_right₀ (Units.ne_zero _)]
  · rintro g ⟨hb, hg⟩
    refine NumD.Gt.ext hb (funext fun χ => ?_)
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    apply Units.ext
    have h := hg x
    simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)]
    exact h

theorem Dict.exists_isPt (g : N.Gt) : ∃ v, d.IsPt v g := by
  obtain ⟨w, hw⟩ := d.ab.2.1 g.b
  let φ : B.X → ℂˣ := fun x => g.s (d.eX x) * d.fr (B.ct x + w) * (d.fr (B.ct x) * d.fr w)⁻¹
  have hφ : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    have hm := g.mult (d.eX x) (d.eX y)
    rw [d.c_eq, d.c_eq, ← hw] at hm
    have hm' := congrArg Units.val hm
    push_cast at hm'
    have h := d.cube_val (B.ct x) (B.ct y) w
    ext
    simp only [φ, map_add (f := _), Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    have hS : (g.s (d.eX x + d.eX y) : ℂ) =
        g.s (d.eX x) * g.s (d.eX y) / N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact hm'
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) : ℂ) =
        d.fr (B.ct x + B.ct y + w) * d.fr (B.ct x) * d.fr (B.ct y) * d.fr w /
          (d.fr (B.ct x + B.ct y) * d.fr (B.ct x + w) * d.fr (B.ct y + w)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hS, hθ]
    field_simp
  obtain ⟨l, hl⟩ := exists_log_of_character φ hφ
  refine ⟨(l, w), hw.symm, fun x => ?_⟩
  show (g.s (d.eX x) : ℂ) * d.fr (B.ct x + w) = eTwoPi (l x) * d.fr (B.ct x) * d.fr w
  rw [← hl x]
  simp only [φ, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem Dict.IsPt.add {d : Dict N B} {v v' : B.V} {g g' : N.Gt} (h : d.IsPt v g) (h' : d.IsPt v' g') :
    d.IsPt (v + v') (g * g') := by
  obtain ⟨hb, hs⟩ := h
  obtain ⟨hb', hs'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.Gt.mul_b, hb, hb', Prod.snd_add, d.ab.1]
  · have e1 := hs x
    have e2 := hs' x
    have hc := d.cube_val (B.ct x) v.2 v'.2
    rw [NumD.Gt.mul_s, d.c_eq, hb, hb']
    simp only [Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.e_add, Units.val_div_eq_div_val,
      Units.val_mul, ← add_assoc]
    have h1 : (g.s (d.eX x) : ℂ) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2 / d.fr (B.ct x + v.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e1
    have h2 : (g'.s (d.eX x) : ℂ) = eTwoPi (v'.1 x) * d.fr (B.ct x) * d.fr v'.2 / d.fr (B.ct x + v'.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e2
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex v.2) (d.ex v'.2) : ℂ) =
        d.fr (B.ct x + v.2 + v'.2) * d.fr (B.ct x) * d.fr v.2 * d.fr v'.2 /
          (d.fr (B.ct x + v.2) * d.fr (B.ct x + v'.2) * d.fr (v.2 + v'.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination hc
    rw [h1, h2, hθ]
    field_simp

theorem Dict.analyticDictionary_isPoint_period_origin (la : B.La) : d.IsPt (B.P0 la) (N.io (d.eX la.y)) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.io_b, d.c_eq, AnArc.degeneratingTori_basePeriodMap_snd, d.ab.1, (d.ab.2.2.1 _).mpr la.l.2, mul_one]
  · rw [NumD.io_s, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_fst_apply, sub_eq_add_neg, AnArc.e_add, AnArc.e_add,
      AnArc.e_intCast, AnArc.e_neg_div, Complex.exp_neg, mul_one]
    have h1 := congrArg Units.val (N.ψ_add (d.eX la.y) (d.eX x))
    have h2 := congrArg Units.val (d.ψ_eq (la.y + x))
    have h3 := B.psi_add la.y x
    have h4 := congrArg Units.val (d.ψ_eq la.y)
    have h5 := congrArg Units.val (d.ψ_eq x)
    have h6 := d.ab.2.2.2.2.1 la.l (B.ct la.y + B.ct x)
    have h7 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
    have h8 := B.ah_add la.l (B.ct la.y) (B.ct x)
    push_cast at h1 h2 h4 h5
    rw [map_add d.eX, map_add B.ct] at h2
    rw [show B.ct la.y + B.ct x + (la.l : Fin B.gB → ℂ) = B.ct x + (B.ct la.y + la.l) by abel] at h6
    have key : ((N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
          Complex.exp (Real.pi * B.H (B.ct x) la.l) -
        eTwoPi (B.T la.y x) * d.fr (B.ct x) * d.fr (B.ct la.y + la.l)) *
        ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) = 0 := by
      linear_combination
        (-((d.fr (B.ct x + (B.ct la.y + la.l)) : ℂ) * Complex.exp (Real.pi * B.H (B.ct x) la.l) *
            B.ah la.l (B.ct la.y))) * h1
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * h8
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * h6 + h2 + h3
        - (B.psi la.y : ℂ) * eTwoPi (B.T la.y x) * h5
        - (N.ψ (d.eX x) : ℂ) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h4
        + (N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h7
    have hne : ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (B.ah_ne_zero _ _)
    have hD := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)
    have hQ : Complex.exp (Real.pi * B.H (B.ct x) la.l) ≠ 0 := Complex.exp_ne_zero _
    calc (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l))
        = (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
            Complex.exp (Real.pi * B.H (B.ct x) la.l) * (Complex.exp (Real.pi * B.H (B.ct x) la.l))⁻¹ := by
          rw [mul_inv_cancel_right₀ hQ]
      _ = _ := by rw [hD]; ring

theorem Dict.isPt_one_iff (v : B.V) : d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la := by
  constructor
  · rintro ⟨hb, hs⟩
    rw [NumD.Gt.one_b] at hb
    have hl : v.2 ∈ B.abelian₂ := (d.ab.2.2.1 v.2).mp hb.symm
    let l : B.abelian₂ := ⟨v.2, hl⟩
    have hp0 : (1 : ℂ) = B.ah l 0 * d.fr v.2 := by
      have h0 : (d.fr 0 : ℂ) = B.ah l 0 * d.fr (0 + v.2) := d.ab.2.2.2.2.1 l 0
      rwa [zero_add, d.ab.2.2.2.1, Units.val_one] at h0
    have hhalf : ∀ z : ℂ, eTwoPi (z / (2 * Complex.I)) = Complex.exp (Real.pi * z) := by
      intro z
      have := AnArc.e_neg_div (-z)
      rwa [neg_div, neg_neg, mul_neg, neg_neg] at this
    have hint : ∀ x, ∃ m : ℤ, (m : ℂ) = v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I) := by
      intro x
      have hsx := hs x
      rw [NumD.Gt.generator_inv_base, Units.val_one, one_mul] at hsx
      have hp1 : (d.fr (B.ct x) : ℂ) = B.ah l (B.ct x) * d.fr (B.ct x + v.2) := d.ab.2.2.2.2.1 l (B.ct x)
      have hq := B.ah_add l 0 (B.ct x)
      rw [zero_add] at hq
      have hF : (d.fr (B.ct x + v.2) : ℂ) *
          (1 - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2)) = 0 := by
        linear_combination hsx + eTwoPi (v.1 x) * d.fr v.2 * hp1 +
          eTwoPi (v.1 x) * d.fr v.2 * d.fr (B.ct x + v.2) * hq -
          eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2) * d.fr (B.ct x + v.2) * hp0
      have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hF).resolve_left (Units.ne_zero _))
      have he : eTwoPi (v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)) = 1 := by
        rw [AnArc.e_add, hhalf]
        exact h1.symm
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
      refine ⟨m, ?_⟩
      have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hπ
      rw [hm]
      ring
    let n : B.X →+ ℤ :=
      { toFun := fun x => (hint x).choose
        map_zero' := Int.cast_injective (α := ℂ) (by
          rw [(hint 0).choose_spec, Int.cast_zero]
          simp)
        map_add' := fun x y => Int.cast_injective (α := ℂ) (by
          rw [Int.cast_add, (hint (x + y)).choose_spec, (hint x).choose_spec, (hint y).choose_spec]
          simp only [map_add (f := _), AnArc.H_add_left]
          ring) }
    refine ⟨AnArc.La.mk 0 n l, AnArc.La.mk_y _ _ _, ?_⟩
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.La.mk_y, AnArc.La.mk_n, AnArc.La.mk_l, map_zero,
        AddMonoidHom.zero_apply, zero_add]
      show v.1 x = ((hint x).choose : ℂ) - B.H (B.ct x) v.2 / (2 * Complex.I)
      rw [(hint x).choose_spec]
      ring
    · rw [AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_l, map_zero, zero_add]
  · rintro ⟨la, hy, rfl⟩
    have h := d.analyticDictionary_isPoint_period_origin la
    rwa [hy, map_zero, NumD.io_zero] at h

theorem ptSt : PtSt := fun _ _ _ _ _ d =>
  ⟨d.existsUnique_isPt, d.exists_isPt, fun _ _ _ _ h h' => h.add h', d.isPt_one_iff, d.analyticDictionary_isPoint_period_origin⟩

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNFrame
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch.Wp

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

theorem ex_nsmul (d : Dict N B) (i : ℕ) (z : Fin B.gB → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (d.ab.2.2.1 0).2 (zero_mem _)
  | succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]

theorem cubN_frame (d : Dict N B) (k : ℕ) (x' x : Fin B.gB → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ k ih =>
    have h := d.ab.2.2.2.2.2.1 (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem tk_frame (d : Dict N B) {k : ℕ} (hk : 0 < k) {la la' : B.La} {p p' : N.QT k} (h : d.Rep k la p)
    (h' : d.Rep k la' p') :
    (N.tk p p' : ℂ) * (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) *
        ((d.fr ((k : ℂ)⁻¹ • B.P0 la').2 : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx
  set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'
  have e : k • x' = B.ct la'.y + la'.l := by
    rw [hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  have s := h.2.2 la'.y
  have f1 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)
  have f2 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y)
  rw [AnArc.ah_add, add_right_comm, ← e] at f1
  rw [← e] at f2
  rw [← hx, f1, f2, eTwoPi] at s
  rw [NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']
  have n1 := B.ah_ne_zero la'.l (B.ct la'.y)
  have n2 := (d.fr (k • x')).ne_zero
  have n3 := (d.fr x).ne_zero
  have n4 := (d.fr (k • x' + x)).ne_zero
  have n5 := Complex.exp_ne_zero (Real.pi * B.H x la'.l)
  rw [div_mul_eq_mul_div, eq_div_iff n5]
  apply mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))
  linear_combination (B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) *
    (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s

theorem wp_eq : WpSt := by
  intro O _ _ N B d k hk la la' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := tk_frame d hk h h'
  have b := tk_frame d hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  have E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ) := by
    rw [← B.Ef_eq_im]; simp
  have C := Complex.sub_conj (B.H la.l la'.l)
  rw [B.H_conj] at C
  have key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) *
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la').2 la.l) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd,
      AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]
    push_cast at C ⊢
    rw [E]
    have hI := Complex.I_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * C
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.Ex.Arch.Wp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFEqGenValMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibCube
open GlobalTheory.FrameValue GlobalTheory.TorusExt

theorem vF_eq_genVal_mul {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    (u : HolUnif A L' g) (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (fr : (Fin g → ℂ) → ℂˣ)
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {r : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' r z) :
    vF t (r ≫ h) J = genVal u hL' a r z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := (default : PrimeSpectrum ℂ)
  let J' : (Sp ℂ ⟶ A.left) → L'.ι := chartAt hL'
  have hJ' : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L'.U (J' ψ) := le_chartAt hL'
  have e := congrArg (fun q => (((stalkUnits p).symm q : ℂˣ) : ℂ))
    (DegPull.pmaps_val hψ H r p (J := J) (J' := J') (fun ψ => hJ ψ trivial) (fun ψ => hJ' ψ trivial))
  have e₁ : vF a r J' = genVal u hL' a r z * frameProd u ε z (fun k => J' (r ≫ φ' k)) :=
    valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' r)
  have e₂ : ∀ v, (((stalkUnits p).symm (gw w (u.ex v).left p (J ((u.ex v).left ≫ Φ)) (J' (u.ex v).left)) : ℂˣ) : ℂ) *
      u.fr (J' (u.ex v).left) v = fr v := fun v => by
    rw [hfr v _ (hJ' _)]
    refine congrArg (· * _) ((stalkConst p).injective ?_)
    have m : ⊤ ≤ (u.ex v).left ⁻¹ᵁ ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left)) :=
      fun y hy => ⟨mem_pull.2 (hJ ((u.ex v).left ≫ Φ) hy), hJ' _ hy⟩
    rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
    exact (gs_unit (u.ex v).left p ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left))
      (m trivial) _).symm.trans (gs_eq_stalkConst _ p m _)
  simp only [map_mul, map_prod, map_zpow, Units.val_mul] at e
  rw [GaugeValues.vF_eq hJ, GaugeValues.vF_eq hJ', e₁] at e
  rw [e, mul_left_comm]
  congr 1
  rw [frameProd, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, e₂]

theorem exists_cube_down {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    (c : CubicalStr G L) {L' : LB G'.left} (hL' : L'.IsLB) {w : LB.Iso L' (L.L.pull F)} (hw : w.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' (thφ G' (x3 G')) thε), a.IsGen ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε a c.t (cubeMapOf gp).F3 ∧
      LB.Gen.Corr L' _ _ (Y := (G2 G').left) _ _ (LB.pullGen L' (thφ G' (x3 G')) thε a (faceMap G' 0).left)
        (LB.oneGen L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB hL' (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine ⟨a, ha, H, corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
  have e := DegPull.pmaps_val hψ H (lift (1 : G2 G' ⟶ G') (lift (x2 G' 0) (x2 G' 1))).left y hJ hJ'
  have q : ∀ a b c : G2 G' ⟶ G', (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp _ a) (lift (pushHom gp _ b) (pushHom gp _ c))).left := fun a b c =>
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q, map_one] at e
  have p := prod_cub (1 : G2 G' ⟶ G') (x2 G' 0) (x2 G' 1) (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.one_mul, _root_.one_mul] at p
  have face : val c.t (lift (1 : Over.mk ((G2 G').hom ≫ f) ⟶ G)
      (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1)))).left y J = 1 := by
    have h := val_corr hJ (c.face 0) (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub c (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have e' := face.symm.trans (e.trans (congrArg (· * _) p))
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp]
  apply Additive.ofMul.injective
  have e'' := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e'' ⊢
  refine Eq.trans ?_ e''.symm
  abel

end GlobalTheory.Ex.Arch.FibCube

namespace GlobalTheory.Ex.Arch
open GlobalTheory.FrameValue GlobalTheory.CubeValues

theorem fibCubeSt : Laws → FibCubeSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ x y z
  obtain ⟨a, ha, H, hf⟩ := FibCube.exists_cube_down gp D.cub P'.isLB hw
  have e := FibCube.vF_eq_genVal_mul (L := D.P.L) (Φ := φ) (w := w) u P'.isLB (fun I : thK => (cubeMapOf gp).psum_comm I.down) ha H hJ fr
    (fun v i hi => by rw [← hex v]; exact hfr v i hi) (isLift_cube u ![x, y, z])
  replace e := e.trans ((congrArg (· * _) (genVal_cube_of_face P'.isLB hAH a ha hf _)).trans (_root_.one_mul _))
  have q : (pt3 u ![x, y, z]).left ≫ (cubeMapOf gp).F3 = (lift (ex x) (lift (ex y) (ex z))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, pt3, hex] <;> rfl
  have p := prod_thK fun I => fr (∑ a ∈ I, ![x, y, z] a)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val] at p
  rw [q] at e
  refine (congrArg (fun s : ℂ => s * fr (x + y) * fr (x + z) * fr (y + z) * fr 0)
    (e.trans (congrArg Units.val p))).trans ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionLiftClosedBaseChangeOfH1Vanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionLiftClosedBaseChangeOfH1Vanishes
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecLiftClosed

variable {X Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem gs_comb {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (W : X.Opens) (hz : r z ∈ W)
    (c : Fin n → R) (u : Fin n → Γ(X, W)) :
    gs r z W (∑ i, AbLaw.cst p W (c i) * u i) =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) * gs r z W (u i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hz _).symm.trans ((gs_mul r z _ hz _ _).trans ?_)
  exact congrArg (· * _) ((gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _))

theorem gs_const_comp (q : Z ⟶ Spec (CommRingCat.of R')) (h : R →+* R') (z : Z) (a : R) :
    gs (q ≫ Spec.map (CommRingCat.ofHom h)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (h a)) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

def combSec {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (c : Fin n → R) (τ : Fin n → LB.Sec M) :
    LB.Sec M where
  f := fun k => ∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_comb p (𝟙 X) y (M.U i) hy.1 _ _).trans (Eq.trans ?_ (congrArg (_ * ·)
      (gs_comb p (𝟙 X) y (M.U j) hy.2 _ _)).symm)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.SecPullIso.gs_sec_trans (τ a) (𝟙 X) y hy.1 hy.2, mul_left_comm]

theorem exists_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH A' _ g hg X' β f' hβ M' w hM' hw s'
  obtain ⟨n, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf hp M hM K g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH
  choose τ' hτ' using fun i => (GlobalTheory.SecPullIso.section_pull X X' β M M' w hM hM' hw (τ i)).1.exists
  obtain ⟨c, hc, -⟩ := hτ A' g X' β f' hβ M' w τ' hM' hw hτ' s'
  choose d hd using fun i => hg (c i)
  refine ⟨combSec f d τ, fun z k k' hk hk' => ?_⟩
  refine (gs_comb f β z (M.U k) hk _ _).trans ?_
  rw [hc k', gs_comb f' (𝟙 X') z (M'.U k') hk', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hβ.w, gs_const_comp, hd, hτ' i z k k' hk hk', Category.id_comp, mul_left_comm]

end GlobalTheory.SecLiftClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionLiftClosedBaseChangeOfH1VanishesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  first | exact @GlobalTheory.SecLiftClosed.exists_lift | exact GlobalTheory.SecLiftClosed.exists_lift | (intros; apply GlobalTheory.SecLiftClosed.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLifts

theorem exists_compatible_sections_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro R _ _ _ I hI Y β hβ hfl hpr N v hN K _ g₀ hg₀ X₀ π f₀ hπ N₀ w₀ hN₀ hw₀ h1 s₀
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre R I Y β hβ N v hN e
    have g := (isGen_iff _).1 hw
    have g' := (isGen_iff _).1 hw₀
    obtain ⟨w'', T⟩ := exists_comp (hN 0).1 w w₀ g g' (hN (e + 1)).1 hN₀
    have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h =>
      hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero _)))
    have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have h := hπ.paste_horiz hj
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes (R ⧸ I ^ (e + 1 + 1)) _ (Y (e + 1)).hom (hfl (e + 1)) (hpr (e + 1)) (N (e + 1))
      (hN (e + 1)).1 K _ (hg₀.comp (Ideal.Quotient.factor_surjective _)) X₀ (π ≫ j) f₀ h N₀ w'' hN₀
      ((isGen_iff _).2 (T.pgen_comp (hN 0).1 g g')) h1 _ _ (Ideal.Quotient.factor_surjective _) _ (β e)
      (Y e).hom (hβ e) (N e) (v e) (hN e).1 (hN e).2 s'
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩

end GlobalTheory.SecLifts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_sections_thickenings_localRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  first | exact @GlobalTheory.SecLifts.exists_compatible_sections_local | exact GlobalTheory.SecLifts.exists_compatible_sections_local | (intros; apply GlobalTheory.SecLifts.exists_compatible_sections_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DifferentiableQuot
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibPrim
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.FrameValue

theorem differentiable_quot {A : Over (Sp ℂ)} [GrpObj A] {X : Scheme.{0}} {L : LB X} {L' : LB A.left} (hL' : L'.IsLB)
    {φ : A.left ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) {g : ℕ} (u : HolUnif A L' g)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      fr z = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {ψ : K → (X ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen)
    {z : (Fin g → ℂ) → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun v => z v k)
    (hz : ∀ v k, ((u.ex v).left ≫ φ) ≫ ψ k = (u.ex (z v k)).left ≫ φ) :
    Differentiable ℂ fun v => vF t ((u.ex v).left ≫ φ) J / ∏ k, fr (z v k) ^ ε k := by
  intro v₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex v₀).left ≫ φ) ⁻¹ᵁ L.wchart ψ j :=
    ⟨_, (le_preimage_wchart _ L ψ _).2 fun _ => hJ _⟩
  obtain ⟨i, hi⟩ : ∃ i : K → L'.ι, ∀ k, ⊤ ≤ (u.ex (z v₀ k)).left ⁻¹ᵁ L'.U (i k) := ⟨_, fun _ => le_chartAt hL' _⟩
  have key : ∀ v, ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j → ∀ k,
      ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L.wchart (fun _ : PUnit => φ) (fun _ => j k) := fun v hv k =>
    (le_preimage_wchart _ L _ _).2 fun _ => hz v k ▸ (le_preimage_wchart _ L ψ _).1 hv k
  obtain ⟨ho, hh⟩ := u.hol (φ ⁻¹ᵁ L.wchart ψ j) ((φ.app _).hom (t.s j).val)
  have hn : {v | ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j} ∈ nhds v₀ := ho.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun v => valAt' ((u.ex v).left ≫ φ) (L.wchart ψ j) (t.s j).val) v₀ := by
    refine (hh.differentiableAt (ho.mem_nhds hj)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    exact ((valueRules _ (u.ex v).left).2.2.2.1 _ φ _ _).symm
  let G : K → (Fin g → ℂ) → ℂ := fun k x =>
    valAt' (u.ex x).left (L.wchart (fun _ : PUnit => φ) (fun _ => j k) ⊓ L'.U (i k)) (w.s (fun _ => j k, i k)).val *
      u.fr (i k) x
  have h₀ := fun k => (le_preimage_inf _ _ _).2 ⟨key v₀ hj k, hi k⟩
  have n₀ : ∀ k, G k (z v₀ k) ≠ 0 := fun k =>
    mul_ne_zero (val_unit_ne_zero _ valueRules (h₀ k) _) (u.fr_ne _ _ (hi k))
  have d₂ : DifferentiableAt ℂ (fun v => ∏ k, G k (z v k) ^ ε k) v₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun v => G k (z v k) ^ ε k) v₀ := fun k => by
      refine DifferentiableAt.zpow ?_ (Or.inl (n₀ k))
      refine DifferentiableAt.comp v₀ (g := G k) ?_ (hd k v₀)
      exact ((u.hol _ _).2.differentiableAt ((u.hol _ 0).1.mem_nhds (h₀ k))).fun_mul
        ((u.fr_hol (i k)).differentiableAt ((u.hol _ 0).1.mem_nhds (hi k)))
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n₀ k)))).congr_of_eventuallyEq ?_
  have hn' : ∀ᶠ v in nhds v₀, ∀ k, ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L'.U (i k) :=
    Filter.eventually_all.2 fun k => (hd k v₀).continuousAt.preimage_mem_nhds ((u.hol _ 0).1.mem_nhds (hi k))
  filter_upwards [hn, hn'] with v hv hv'
  have hJv : ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ fun k => J (((u.ex v).left ≫ φ) ≫ ψ k) :=
    (le_preimage_wchart _ L ψ _).2 fun _ => hJ _
  have e₁ := (val_gen _ valueRules t ht _ _ hJv hv).trans
    (congrArg (· * _) (val_linComb _ valueRules L ψ ε _ _ hJv hv))
  have e₂ : ∀ k, fr (z v k) = valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val * G k (z v k) := fun k => by
    rw [hfr _ _ (hv' k), hz v k, ← _root_.mul_assoc]
    refine congrArg (· * _) ((GlobalTheory.PowUnif.val_iso _ L L' (fun _ : PUnit => φ) w hw _ _ _ _
      ((le_preimage_wchart _ L _ _).2 fun _ => hJ _) (key v hv k) (hv' k) (hv' k)).trans ?_)
    rw [GlobalTheory.PowUnif.val_g_self hL' _ _ (hv' k), inv_one, _root_.mul_one, Fintype.prod_unique]
  have n : (∏ k, valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (val_unit_ne_zero _ valueRules
      ((le_preimage_inf _ _ _).2 ⟨hJ _, (le_preimage_wchart _ L ψ _).1 hv k⟩) _)
  simp only [e₂, mul_zpow, Finset.prod_mul_distrib]
  exact (congrArg (· / _) e₁).trans ((mul_div_mul_left _ _ n).trans (div_eq_mul_inv _ _))

theorem vF_eq_one {X Y Z : Scheme.{0}} {L : LB X} {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} {e : Z ⟶ Y}
    (h : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t e) (LB.oneGen L)) (y : Sp ℂ ⟶ Z) : vF t (y ≫ e) J = 1 := by
  have h₁ : ⊤ ≤ y ⁻¹ᵁ L.wchart (fun k => e ≫ ψ k) fun k => J (y ≫ e ≫ ψ k) :=
    (le_preimage_wchart _ L _ _).2 fun _ => hJ _
  have h₂ : ⊤ ≤ y ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim :=
    (le_preimage_wchart _ L _ _).2 fun k => k.elim
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  have := congrArg (fun q : Γ(Z, _)ˣ => valAt' y _ q.val) (h (fun k => J (y ≫ e ≫ ψ k)) PEmpty.elim
    (fun a b q => congrArg (fun q => J (y ≫ q)) q) (fun a => a.elim) (fun _ b => b.elim))
  have e₁ := (val_res y valueRules inf_le_left h₃ _).symm.trans (this.trans (val_res y valueRules inf_le_right h₃ _))
  obtain ⟨r, hr⟩ := (valueRules Z y).2.1 _ h₂
  exact ((val_res y valueRules _ h₁ _).trans (val_pullU y valueRules e _ _)).symm.trans
    (e₁.trans ((hr _).trans (map_one r)))

theorem fibPrim : FibPrimSt := by
  rintro R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, rfl, hφ, hw, hAH, -, -, -, hex, hfr⟩ f hf F hF hFf hH Ef hEf t ⟨ht, h₀⟩
  change u.IsAH Hm χ at hAH
  have hL := P'.isLB
  have add : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => Over.OverMorphism.ext (by
    rw [hex, u.ex_add, ← hφ.2 _ _ _ (pushPt hφ.1.w (u.ex z)) (pushPt hφ.1.w (u.ex z')) rfl rfl]
    exact mul_left_congr (Category.id_comp _) _ _ _ _ (hex z).symm (hex z').symm)
  have zero : ex 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have per : ∀ (l : u.Λ) z, (ex (z + l)).left = (ex z).left := fun l z => by
    rw [hex, hex, ex_add_period u z l l.2]
  have fac : ∀ (l : u.Λ) z, (fr z : ℂ) = ahFactor Hm χ l z * fr (z + l) := fun l z => by
    have hi := le_chartAt hL (u.ex z).left
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P'.L.U (chartAt hL (u.ex z).left) := by
      rw [ex_add_period u z l l.2]; exact hi
    rw [hfr _ _ hi, hfr _ _ hi', hAH.2.2.2 l _ z hi, per, ex_add_period u z l l.2, mul_left_comm]
    rfl
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → ℂ, ∀ v, V v = vF t (ex v).left J /
      (fr (v + F v) * ((fr v : ℂ) ^ 2)⁻¹ * (fr (F v) : ℂ)⁻¹ * fr 0 ^ 2) := ⟨_, fun _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have hd : Differentiable ℂ V := by
    have := differentiable_quot hL hw u hJ (fr := fun z => fr z) (fun z i hi => by rw [← hex]; exact hfr z i hi) ht
      (z := fun v => ![v + F v, v, F v, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop) (fun v k => by
        rw [← hex, ← hex]
        fin_cases k
        · exact congrArg (fun m => m.left) (show ex v ≫ (𝟙 _ * f) = ex (v + F v) by
            rw [MonObj.comp_mul, Category.comp_id, ← hFf, add])
        · exact Category.comp_id _
        · exact congrArg (fun m => m.left) (hFf v).symm
        · exact congrArg (fun m => m.left) ((MonObj.comp_one (ex v)).trans zero.symm))
    convert this using 2 with v
    rw [hV, hex]
    simp [Fin.prod_univ_four]
  have hper : ∀ (l : u.Λ) v, V (v + l) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ / χ l * V v := fun l v => by
    have a₁ := fac (l + ⟨F l, hF l l.2⟩) (v + F v)
    have a₂ := fac l v
    have a₃ := fac ⟨F l, hF l l.2⟩ (F v)
    have c := chi_add hL hAH l ⟨F l, hF l l.2⟩
    have s : Complex.exp (Real.pi * Complex.I * (hermForm Hm l (F l)).im) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ := by
      rw [← hEf l ⟨F l, hF l l.2⟩, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have x : Complex.exp (Real.pi * hermForm Hm (v + F v) (l + F l) + Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) =
        Complex.exp (Real.pi * hermForm Hm v l + Real.pi / 2 * hermForm Hm l l) ^ 2 *
        Complex.exp (Real.pi * hermForm Hm (F v) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      simp only [EigenNorm.hermForm_add_left, EigenNorm.hermForm_add_right]
      push_cast
      linear_combination (-Real.pi : ℂ) * hH v l - (Real.pi / 2 : ℂ) * hH l l
    rw [s] at c
    rw [hV, hV, per, a₁, a₂, a₃, map_add (f := _), add_add_add_comm v]
    simp only [ahFactor, c, Submodule.coe_add, x]
    have n := chi_ne_zero hAH l
    have n' := chi_ne_zero hAH ⟨F l, hF l l.2⟩
    have n'' : (-1 : ℂ) ^ Ef l ⟨F l, hF l l.2⟩ ≠ 0 := zpow_ne_zero _ (by simp)
    field_simp
  have hc := const_of_norm_periodic u hd (fun l v => by
    rw [hper, norm_mul, norm_div, hAH.2.2.1, norm_zpow, norm_neg, norm_one, one_zpow, div_one, _root_.one_mul])
  have h1 : V 0 = 1 := by
    have e : (ex 0).left = (TF (R := R) ℂ).hom ≫ eSec D.P.A := by rw [zero, Hom.one_def]; simp [eSec]
    rw [hV, e, vF_eq_one hJ h₀, map_zero, add_zero]
    have := (fr 0).ne_zero
    field_simp
  refine ⟨fun l => ?_, fun z => ?_⟩
  · have := hper l 0
    rw [hc _ 0, h1, _root_.mul_one] at this
    exact ((div_eq_one_iff_eq (chi_ne_zero hAH l)).1 this.symm).symm
  · have := (hV z).symm.trans ((hc z 0).trans h1)
    have a := (fr z).ne_zero
    have b := (fr (F z)).ne_zero
    have c := (fr (z + F z)).ne_zero
    have d := (fr 0).ne_zero
    field_simp at this
    exact this

theorem fibPrim_of_laws : Laws → FibPrimSt := fun _ => fibPrim

end GlobalTheory.Ex.Arch.FibPrim
end
end
