module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OrbitBaseIdempotentRank
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsPretransitiveActO
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem tdM : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := by
  haveI := (tdk : TotallyDisconnectedSpace k)
  exact (inferInstance : TotallyDisconnectedSpace (Fin N → Fin N → k))

theorem comm_span_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (y : Matrix (Fin N) (Fin N) k) :
    (∀ a ∈ S, a * y = y * a) ↔ ∀ i, b i * y = y * b i := by
  have hmem : ∀ a, a ∈ S ↔ a ∈ Submodule.span k (Set.range b) := fun a => by
    rw [← hb]; rfl
  constructor
  · exact fun h i => h _ ((hmem _).2 (Submodule.subset_span ⟨i, rfl⟩))
  · intro h a ha
    have key : ∀ a ∈ Submodule.span k (Set.range b), a * y = y * a := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
      | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
    exact key a ((hmem a).1 ha)

theorem cj_eq_self_iff (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g x = x ↔ x * g.val = g.val * x := by
  unfold cj
  constructor
  · intro h
    calc x * g.val = (↑g * x * ↑g⁻¹) * g.val := by rw [h]
      _ = g.val * x := by simp [mul_assoc]
  · intro h
    rw [← h, mul_assoc, Units.mul_inv, mul_one]

theorem mem_GzS_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) (g : GL (Fin N) k) :
    g ∈ GzS S ↔ ∀ i, cj g (b i) = b i := by
  exact (show g ∈ GzS S ↔ ∀ a ∈ S, a * g.val = g.val * a from Iff.rfl).trans
    ((comm_span_iff hb _).trans (forall_congr' fun i => (cj_eq_self_iff g (b i)).symm))

def Orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
  {w | ∃ g : GL (Fin N) k, ∀ i, w i = cj g (b i)}

theorem self_mem_orb {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : b ∈ Orb b :=
  ⟨1, fun i => (cj_one _).symm⟩

theorem cj_mem_orb {r : ℕ} {b w : Fin r → Matrix (Fin N) (Fin N) k} (hw : w ∈ Orb b) (g : GL (Fin N) k) :
    (fun i => cj g (w i)) ∈ Orb b := by
  obtain ⟨h, hh⟩ := hw
  exact ⟨g * h, fun i => by show cj g (w i) = _; rw [hh, cj_mul]⟩

abbrev cr_commRing {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S) : CommRing S :=
  { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (hS.1 a a.2 b b.2) }

theorem span_top_of {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    Submodule.span k (Set.range fun i => (⟨b i, by
      show b i ∈ S.toSubmodule; rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩⟩ : S)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Matrix (Fin N) (Fin N) k) ∈ Submodule.span k (Set.range b) := by
    rw [← hb]
    exact x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨c, ?_⟩
  apply Subtype.ext
  rw [← hc]
  simp

theorem isClosed_orb (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    IsClosed (Orb b) := by
  letI : CommRing S := cr_commRing hS
  haveI : IsReduced S := hS.2
  exact hO N r S hS.2 _ (span_top_of hb) S.val

def actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) : MulAction (GL (Fin N) k) (Orb b) where
  smul g w := ⟨fun i => cj g (w.1 i), cj_mem_orb w.2 g⟩
  one_smul w := Subtype.ext (funext fun i => cj_one _)
  mul_smul g h w := Subtype.ext (funext fun i => cj_mul g h _)

theorem continuousSMul_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @ContinuousSMul (GL (Fin N) k) (Orb b) (actO b).toSMul _ _ := by
  letI := actO b
  refine ⟨?_⟩
  show Continuous (fun p : GL (Fin N) k × Orb b => (⟨fun i => cj p.1 (p.2.1 i), cj_mem_orb p.2.2 p.1⟩ : Orb b))
  have hc : ∀ i : Fin r, Continuous (fun p : GL (Fin N) k × Orb b => cj p.1 (p.2.1 i)) := by
    intro i
    have h1 : Continuous (fun p : GL (Fin N) k × Orb b => p.2.1 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have h2 : Continuous (fun p : GL (Fin N) k × Orb b => (p.1, p.2.1 i)) := continuous_fst.prodMk h1
    exact (continuous_cj (n := N)).comp h2
  exact Continuous.subtype_mk (continuous_pi hc) _

theorem isPretransitive_actO {r : ℕ} (b : Fin r → Matrix (Fin N) (Fin N) k) :
    @MulAction.IsPretransitive (GL (Fin N) k) (Orb b) (actO b).toSMul := by
  letI := actO b
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨h, hh⟩ := y.2
  refine ⟨h * g⁻¹, Subtype.ext (funext fun i => ?_)⟩
  show cj (h * g⁻¹) (x.1 i) = y.1 i
  rw [hg i, hh i, ← cj_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_orb_homeo (hO : OrbClosed k) {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hS : CR S)
    {b : Fin r → Matrix (Fin N) (Fin N) k} (hb : S.toSubmodule = Submodule.span k (Set.range b)) :
    ∃ e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b, ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) =
      fun i => cj g (b i) := by
  letI := actO b
  haveI := continuousSMul_actO b
  haveI := isPretransitive_actO b
  haveI : LocallyCompactSpace (Orb b) := (isClosed_orb hO hS hb).locallyCompactSpace
  obtain ⟨e, he⟩ := exists_quotient_homeo (G := GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b)
  have hst : MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = GzS S := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_GzS_iff hb]
    constructor
    · intro h i
      exact congrFun (congrArg Subtype.val h) i
    · intro h
      exact Subtype.ext (funext h)
  have key : ∀ H : Subgroup (GL (Fin N) k),
      MulAction.stabilizer (GL (Fin N) k) (⟨b, self_mem_orb b⟩ : Orb b) = H →
      ∃ e : GL (Fin N) k ⧸ H ≃ₜ Orb b, ∀ g : GL (Fin N) k,
        ((e g : Orb b) : Fin r → Matrix (Fin N) (Fin N) k) = fun i => cj g (b i) := by
    rintro H rfl
    exact ⟨e, fun g => by rw [he g]; rfl⟩
  exact key _ hst

theorem rank_add_of_orth {e f : Matrix (Fin N) (Fin N) k} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) : (e + f).rank = e.rank + f.rank := by
  have hE : (e + f) * e = e := by rw [add_mul, he.eq, hfe, add_zero]
  have hF : (e + f) * f = f := by rw [add_mul, hef, hf.eq, zero_add]
  have hsup : LinearMap.range (e + f).mulVecLin =
      LinearMap.range e.mulVecLin ⊔ LinearMap.range f.mulVecLin := by
    apply le_antisymm
    · rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le _ _
    · refine sup_le ?_ ?_
      · conv_lhs => rw [← hE]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
      · conv_lhs => rw [← hF]
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _
  have hinf : LinearMap.range e.mulVecLin ⊓ LinearMap.range f.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [Submodule.mem_inf, LinearMap.mem_range, Matrix.mulVecLin_apply] at hx
    obtain ⟨⟨u, rfl⟩, ⟨w, hw⟩⟩ := hx
    rw [Submodule.mem_bot]
    have hu : e *ᵥ u = e *ᵥ (e *ᵥ u) := by rw [Matrix.mulVec_mulVec, he.eq]
    rw [hu, ← hw, Matrix.mulVec_mulVec, hef, Matrix.zero_mulVec]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e.mulVecLin) (LinearMap.range f.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  unfold Matrix.rank
  exact h

theorem rank_sum_orth {ι : Type*} [DecidableEq ι] (e : ι → Matrix (Fin N) (Fin N) k) (he : ∀ t, IsIdempotentElem (e t))
    (ho : ∀ t t', t ≠ t' → e t * e t' = 0) (T : Finset ι) :
    IsIdempotentElem (∑ t ∈ T, e t) ∧ (∑ t ∈ T, e t).rank = ∑ t ∈ T, (e t).rank := by
  refine Finset.induction_on T ?_ ?_
  · refine ⟨?_, ?_⟩ <;> simp [IsIdempotentElem, Matrix.rank_zero]
  · intro a s ha ih
    have h1 : e a * ∑ t ∈ s, e t = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun t ht => ho a t (fun h => ha (by rw [h]; exact ht))
    have h2 : (∑ t ∈ s, e t) * e a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun t ht => ho t a (fun h => ha (by rw [← h]; exact ht))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(he a).add ih.1 (by rw [h1, h2, add_zero]), by rw [rank_add_of_orth (he a) ih.1 h1 h2, ih.2]⟩

theorem cr_bot : CR (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha
    exact Algebra.commutes c b
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := hx
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 x.2
    have hn' : (x : Matrix (Fin N) (Fin N) k) ^ n = 0 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [← hc, ← map_pow] at hn'
    by_cases h0 : c = 0
    · apply Subtype.ext
      rw [← hc, h0, map_zero]
      rfl
    · have h1 : (1 : Matrix (Fin N) (Fin N) k) = 0 := by
        have hcn : c ^ n ≠ 0 := pow_ne_zero _ h0
        calc (1 : Matrix (Fin N) (Fin N) k) = algebraMap k _ ((c ^ n)⁻¹ * c ^ n) := by
              rw [inv_mul_cancel₀ hcn, map_one]
          _ = 0 := by rw [map_mul, hn', mul_zero]
      apply Subtype.ext
      show (x : Matrix (Fin N) (Fin N) k) = 0
      rw [← mul_one (x : Matrix (Fin N) (Fin N) k), h1, mul_zero]

def glEquivBot : GL (Fin N) k ≃ₜ* GzS (⊥ : Subalgebra k (Matrix (Fin N) (Fin N) k)) where
  toFun g := ⟨g, fun a ha => by obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha; exact Algebra.commutes c g.val⟩
  invFun g := g.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_id _
  continuous_invFun := continuous_subtype_val

theorem isUnimod_GL (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : PositivityTheory.PfBern.Frob.IsUnimod (GL (Fin N) k) :=
  isUnimod_of_equiv glEquivBot (hU N ⊥ cr_bot)

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece
  PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem cj_mulM (g : GL (Fin N) k) (a b : Matrix (Fin N) (Fin N) k) : cj g (a * b) = cj g a * cj g b := by
  have h1 : g⁻¹.val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cj]
  rw [show g.val * a * g⁻¹.val * (g.val * b * g⁻¹.val) = g.val * a * (g⁻¹.val * g.val) * b * g⁻¹.val by
    simp only [mul_assoc], h1, mul_one]
  simp only [mul_assoc]

theorem cj_inv_cj (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g⁻¹ (cj g x) = x := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_cj_inv (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g (cj g⁻¹ x) = x := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

theorem cj_sum {ι : Type*} (g : GL (Fin N) k) (T : Finset ι) (f : ι → Matrix (Fin N) (Fin N) k) :
    cj g (∑ i ∈ T, f i) = ∑ i ∈ T, cj g (f i) := by
  simp only [cj, Finset.mul_sum, Finset.sum_mul]

theorem cj_smul (g : GL (Fin N) k) (c : k) (x : Matrix (Fin N) (Fin N) k) : cj g (c • x) = c • cj g x := by
  simp only [cj, mul_smul_comm, smul_mul_assoc]

theorem cj_pow (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (n : ℕ) : cj g (x ^ n) = cj g x ^ n :=
  (Units.conj_pow g x n).symm

theorem rank_cj (g : GL (Fin N) k) (e : Matrix (Fin N) (Fin N) k) : (cj g e).rank = e.rank := rank_conj g e

theorem eq_zero_of_rank {A : Matrix (Fin N) (Fin N) k} (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

theorem ne_zero_iff_rank {A : Matrix (Fin N) (Fin N) k} : A ≠ 0 ↔ A.rank ≠ 0 :=
  ⟨fun h h0 => h (eq_zero_of_rank h0), fun h h0 => h (by rw [h0, Matrix.rank_zero])⟩

def lin {a0 : ℕ} (c : Fin a0 → k) (w : Fin a0 → Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  ∑ i, c i • w i

theorem lin_cj {a0 : ℕ} (c : Fin a0 → k) (w : Fin a0 → Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    lin c (fun i => cj g (w i)) = cj g (lin c w) := by
  simp only [lin, cj_sum, cj_smul]

theorem continuous_lin {a0 : ℕ} (c : Fin a0 → k) : Continuous (lin (N := N) c) := by
  unfold lin
  exact continuous_finsetSum _ fun i _ => by fun_prop

theorem pe_cj {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    pe (fun l => cj g (c l)) (cj g x) = cj g (pe c x) := by
  simp only [pe, cj_sum, cj_mulM, cj_pow]

theorem continuous_re {d r : ℕ} (γ : Fin d → Fin r → k) (s : Fin r → Matrix (Fin N) (Fin N) k) :
    Continuous (re γ s) := by
  unfold re
  exact continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun j _ => by fun_prop

variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)

theorem z_mem (i : Fin D.a0) : D.z i ∈ Z := by
  show D.z i ∈ Z.toSubmodule
  rw [D.hz]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem exists_coef {a : Matrix (Fin N) (Fin N) k} (ha : a ∈ Z) : ∃ c : Fin D.a0 → k, lin c D.z = a := by
  have : a ∈ Submodule.span k (Set.range D.z) := by rw [← D.hz]; exact ha
  exact (Submodule.mem_span_range_iff_exists_fun k).1 this

def al (j : Fin D.r) (l : Fin D.d) : Fin D.a0 → k := (exists_coef D (D.ha j l)).choose

def bl (l : Fin D.d) : Fin D.a0 → k := (exists_coef D (D.hb l)).choose

theorem lin_al (j : Fin D.r) (l : Fin D.d) : lin (al D j l) D.z = D.a j l := (exists_coef D (D.ha j l)).choose_spec

theorem lin_bl (l : Fin D.d) : lin (bl D l) D.z = D.b l := (exists_coef D (D.hb l)).choose_spec

def sw (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : Fin D.r → Matrix (Fin N) (Fin N) k :=
  fun j => pe (fun l => lin (al D j l) w) x

def ew (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  pe (fun l => lin (bl D l) w) x

def et (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (t : Fin D.m) :
    Matrix (Fin N) (Fin N) k :=
  ∑ j, D.κ t j • sw D w x j

theorem weight_map_at_base (x : Matrix (Fin N) (Fin N) k) : sw D D.z x = fun j => pe (D.a j) x := by
  funext j; simp only [sw, lin_al]

theorem eigenvalue_map_at_base (x : Matrix (Fin N) (Fin N) k) : ew D D.z x = pe D.b x := by
  simp only [ew, lin_bl]

theorem sw_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    sw D (fun i => cj g (w i)) (cj g x) = fun j => cj g (sw D w x j) := by
  funext j; simp only [sw, lin_cj, pe_cj]

theorem ew_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    ew D (fun i => cj g (w i)) (cj g x) = cj g (ew D w x) := by
  simp only [ew, lin_cj, pe_cj]

theorem et_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) (t : Fin D.m) :
    et D (fun i => cj g (w i)) (cj g x) t = cj g (et D w x t) := by
  simp only [et, sw_cj, cj_sum, cj_smul]

theorem continuous_sw (j : Fin D.r) :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => sw D p.1 p.2 j := by
  unfold sw pe
  exact continuous_finsetSum _ fun l _ => ((continuous_lin _).comp continuous_fst).mul ((continuous_pow _).comp continuous_snd)

theorem continuous_ew :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => ew D p.1 p.2 := by
  unfold ew pe
  exact continuous_finsetSum _ fun l _ => ((continuous_lin _).comp continuous_fst).mul ((continuous_pow _).comp continuous_snd)

theorem continuous_et (t : Fin D.m) :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => et D p.1 p.2 t := by
  unfold et
  exact continuous_finsetSum _ fun j _ => (continuous_sw D j).const_smul (D.κ t j)

def Ys (τ : Fin D.m → ℕ) : Set ((Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
  {p | ∃ g : GL (Fin N) k, (∀ i, p.1 i = cj g (D.z i)) ∧ cj g⁻¹ p.2.1 ∈ piece D τ}

theorem mem_Ys_cj {τ : Fin D.m → ℕ} {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ)
    (g : GL (Fin N) k) : ((fun i => cj g (p.1 i)), act g p.2) ∈ Ys D τ := by
  obtain ⟨h, hh, hx⟩ := hp
  refine ⟨g * h, fun i => by show cj g (p.1 i) = _; rw [hh, cj_mul], ?_⟩
  show cj (g * h)⁻¹ (cj g p.2.1) ∈ piece D τ
  rw [_root_.mul_inv_rev, cj_mul, cj_inv_cj]
  exact hx

def F0 : Set ((Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
  {p | p.1 ∈ Orb D.z ∧ (∀ i, p.1 i * p.2.1 = p.2.1 * p.1 i) ∧ aeval p.2.1 χ = 0}

theorem mem_orbit_base_iff {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ F0 D) :
    ∃ g : GL (Fin N) k, (∀ i, p.1 i = cj g (D.z i)) ∧ cj g⁻¹ p.2.1 ∈ Bz Z ∧ aeval (cj g⁻¹ p.2.1) χ = 0 := by
  obtain ⟨⟨g, hg⟩, hc, hχ⟩ := hp
  refine ⟨g, hg, (comm_span_iff D.hz _).2 fun i => ?_, ?_⟩
  · have e : D.z i = cj g⁻¹ (p.1 i) := by rw [hg, cj_inv_cj]
    rw [e, ← cj_mulM, ← cj_mulM, hc]
  · rw [cj, PTop.aeval_conj, hχ, mul_zero, zero_mul]

theorem orbit_base_idempotent_rank {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ F0 D) (t : Fin D.m) :
    IsIdempotentElem (et D p.1 p.2.1 t) ∧ (et D p.1 p.2.1 t).rank = typ D (cj (Classical.choose (mem_orbit_base_iff D hp))⁻¹ p.2.1) t := by
  obtain ⟨hg, hB, hχ⟩ := Classical.choose_spec (mem_orbit_base_iff D hp)
  set g := Classical.choose (mem_orbit_base_iff D hp)
  have e1 : p.1 = fun i => cj g (D.z i) := funext hg
  have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
  have e3 : et D p.1 p.2.1 t = cj g (∑ j, D.κ t j • pe (D.a j) (cj g⁻¹ p.2.1)) := by
    conv_lhs => rw [e1, e2]
    rw [et_cj, et, weight_map_at_base]
  rw [e3]
  refine ⟨?_, rank_conj g _⟩
  show cj g _ * cj g _ = cj g _
  rw [← cj_mulM, ((D.spec _ hB hχ).2.2.2.2.2.2.2.2.1 t).eq]

theorem Ys_eq (τ : Fin D.m → ℕ) (hP : ∀ g ∈ Gz Z, ∀ x ∈ piece D τ, g.val * x * g⁻¹.val ∈ piece D τ) :
    Ys D τ = F0 D ∩ ⋂ t, {p | p ∈ F0 D ∧ (et D p.1 p.2.1 t).rank = τ t} := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hx, hχ, hτ⟩
    have e1 : p.1 = fun i => cj g (D.z i) := funext hg
    have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
    have hF : p ∈ F0 D := by
      refine ⟨⟨g, hg⟩, fun i => ?_, ?_⟩
      · rw [hg, e2, ← cj_mulM, ← cj_mulM, hx _ (z_mem D i)]
      · rw [e2, cj, PTop.aeval_conj, hχ, mul_zero, zero_mul]
    refine ⟨hF, fun t => ⟨hF, ?_⟩⟩
    rw [e1, e2, et_cj, rank_cj, et, weight_map_at_base]
    exact congrFun hτ t
  · rintro ⟨hF, ht⟩
    obtain ⟨g, hg, hB, hχ⟩ := mem_orbit_base_iff D hF
    refine ⟨g, hg, hB, hχ, funext fun t => ?_⟩
    have e1 : p.1 = fun i => cj g (D.z i) := funext hg
    have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
    have := (ht t).2
    rw [e1, e2, et_cj, rank_cj, et, weight_map_at_base] at this
    exact this

theorem isClosed_orbit_base (hO : OrbClosed k) (hZ : CR Z) : IsClosed (F0 D) := by
  haveI : T2Space k := t2k
  have e : F0 D = (Prod.fst ⁻¹' Orb D.z) ∩ ((⋂ i, {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N |
      p.1 i * p.2.1 = p.2.1 * p.1 i}) ∩ {p | aeval p.2.1 χ = 0}) := by
    ext p; simp only [F0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [e]
  refine ((isClosed_orb hO hZ D.hz).preimage continuous_fst).inter (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun i => isClosed_eq (((continuous_apply i).comp continuous_fst).mul
      (continuous_fst.comp continuous_snd)) ((continuous_fst.comp continuous_snd).mul ((continuous_apply i).comp continuous_fst))
  · exact isClosed_eq ((continuous_aevalM χ).comp (continuous_fst.comp continuous_snd)) continuous_const

theorem isClosed_Ys (hO : OrbClosed k) (hZ : CR Z) (τ : Fin D.m → ℕ)
    (hP : ∀ g ∈ Gz Z, ∀ x ∈ piece D τ, g.val * x * g⁻¹.val ∈ piece D τ) : IsClosed (Ys D τ) := by
  rw [Ys_eq D τ hP]
  have hF := isClosed_orbit_base D hO hZ
  exact hF.inter (isClosed_iInter fun t => isClosed_rank hF ((continuous_et D t).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) (fun p hp => (orbit_base_idempotent_rank D hp t).1) _)

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

def lc {r : ℕ} (s : Fin r → Matrix (Fin N) (Fin N) k) (v : Fin r → k) : Matrix (Fin N) (Fin N) k := ∑ j, v j • s j

section Lc

variable {r : ℕ} (s : Fin r → Matrix (Fin N) (Fin N) k)

theorem lc_add (v w : Fin r → k) : lc s (v + w) = lc s v + lc s w := by
  simp only [lc, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem lc_sub (v w : Fin r → k) : lc s (v - w) = lc s v - lc s w := by
  simp only [lc, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem lc_smul (c : k) (v : Fin r → k) : lc s (c • v) = c • lc s v := by
  simp only [lc, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem lc_sum {ι : Type*} (T : Finset ι) (v : ι → Fin r → k) : lc s (∑ t ∈ T, v t) = ∑ t ∈ T, lc s (v t) := by
  simp only [lc, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem lc_single (j : Fin r) : lc s (Pi.single j 1) = s j := by
  simp [lc, Pi.single_apply]

theorem lc_mul (c : Fin r → Fin r → Fin r → k) (hmul : ∀ j j', s j * s j' = ∑ t, c j j' t • s t) (v w : Fin r → k) :
    lc s v * lc s w = lc s (fun t => ∑ j, ∑ j', v j * w j' * c j j' t) := by
  simp only [lc, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, hmul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Lc

variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)

theorem sx_span {x : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨hm, hu, -⟩ := D.spec x hx hχ
  set P := Submodule.span k (Set.range fun j => pe (D.a j) x) with hP
  have h1 : (1 : Matrix (Fin N) (Fin N) k) ∈ P := by
    rw [← hu]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hPP : P * P ≤ P := by
    rw [hP, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    change pe (D.a i) x * pe (D.a j) x ∈ P
    rw [hm i j]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hmul : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P := fun a b ha hb => hPP (Submodule.mul_mem_mul ha hb)
  apply le_antisymm
  · have hle : Algebra.adjoin k (Set.range fun j => pe (D.a j) x) ≤ P.toSubalgebra h1 hmul :=
      Algebra.adjoin_le Submodule.subset_span
    exact Subalgebra.toSubmodule.monotone hle
  · rw [Submodule.span_le]
    exact Algebra.subset_adjoin

private theorem lc_kappa_complete_orthogonal_primitive_idempotents {x : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
    (s : Fin D.r → Matrix (Fin N) (Fin N) k) (hs : s = fun j => pe (D.a j) x) :
    (∀ j j', s j * s j' = ∑ t, D.c j j' t • s t) ∧ lc s D.u = 1 ∧
      (∀ j j', s j * s j' = s j' * s j) ∧
      (∀ y ∈ Submodule.span k (Set.range s), IsNilpotent y → y = 0) ∧
      (∀ t, IsIdempotentElem (lc s (D.κ t))) ∧
      ∑ t, lc s (D.κ t) = 1 ∧
      (∀ t t', t ≠ t' → lc s (D.κ t) * lc s (D.κ t') = 0) ∧
      (∀ t, ∀ y ∈ Submodule.span k (Set.range s), IsIdempotentElem y →
        y * lc s (D.κ t) = y → y = 0 ∨ y = lc s (D.κ t)) ∧
      (∀ v, lc s v = 0 ↔ ∀ t, lc s (D.κ t) ≠ 0 → v ∈ D.K t) := by
  subst hs
  obtain ⟨h1, h2, h3, -, -, h6, -, -, h9, h10, h11, h12, -, h14⟩ := D.spec x hx hχ
  exact ⟨h1, h2, h3, h6, h9, h10, h11, h12, h14⟩

theorem exists_isAttachedHodgeS_conj_mapRep (hO : OrbHom k) (hZ : CR Z) {τ : Fin D.m → ℕ} {x₀ x : Matrix (Fin N) (Fin N) k}
    (h₀ : x₀ ∈ piece D τ) (h : x ∈ piece D τ) :
    ∃ g : GL (Fin N) k, ∀ j, pe (D.a j) x = cj g (pe (D.a j) x₀) := by
  classical
  obtain ⟨hx₀B, hx₀χ, hx₀τ⟩ := h₀
  obtain ⟨hxB, hxχ, hxτ⟩ := h
  set s0 : Fin D.r → Matrix (Fin N) (Fin N) k := fun j => pe (D.a j) x₀ with hs0
  set s : Fin D.r → Matrix (Fin N) (Fin N) k := fun j => pe (D.a j) x with hs
  obtain ⟨m0, u0, c0, n0, i0, hsum0, o0, prim0, k0⟩ := lc_kappa_complete_orthogonal_primitive_idempotents D hx₀B hx₀χ s0 hs0
  obtain ⟨m1, u1, -, -, i1, -, o1, -, k1⟩ := lc_kappa_complete_orthogonal_primitive_idempotents D hxB hxχ s hs
  have hr0 : ∀ t, (lc s0 (D.κ t)).rank = τ t := fun t => congrFun hx₀τ t
  have hr1 : ∀ t, (lc s (D.κ t)).rank = τ t := fun t => congrFun hxτ t
  have hne : ∀ t, lc s0 (D.κ t) ≠ 0 ↔ lc s (D.κ t) ≠ 0 := by
    intro t
    rw [ne_zero_iff_rank, ne_zero_iff_rank, hr0, hr1]
  have hker : ∀ v, lc s0 v = 0 ↔ lc s v = 0 := by
    intro v
    rw [k0, k1]
    exact forall_congr' fun t => imp_congr_left (hne t)
  have hspan0 := sx_span D hx₀B hx₀χ
  have memSpan : ∀ y, y ∈ Sx D x₀ ↔ y ∈ Submodule.span k (Set.range s0) := by
    intro y
    rw [← Subalgebra.mem_toSubmodule, hspan0]
  have memS : ∀ y, y ∈ Sx D x₀ ↔ ∃ v, lc s0 v = y := by
    intro y
    rw [memSpan, Submodule.mem_span_range_iff_exists_fun]
    rfl
  have hcomm : ∀ a ∈ Sx D x₀, ∀ b ∈ Sx D x₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨v, rfl⟩ := (memS a).1 ha
    obtain ⟨w, rfl⟩ := (memS b).1 hb
    simp only [lc, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      congrArg₂ (· • ·) (mul_comm _ _) (c0 _ _)
  have hred : IsReduced (Sx D x₀) := by
    refine ⟨fun a ha => Subtype.ext ?_⟩
    exact n0 a.1 ((memSpan a.1).1 a.2) (ha.map (Sx D x₀).val)
  letI : CommRing (Sx D x₀) := cr_commRing ⟨hcomm, hred⟩
  choose vOf hvOf using fun a : Sx D x₀ => (memS a.1).1 a.2
  have key : ∀ (a : Sx D x₀) v, lc s0 v = a.1 → lc s (vOf a) = lc s v := by
    intro a v hv
    have h0 : lc s0 (vOf a - v) = 0 := by rw [lc_sub, hvOf, hv, sub_self]
    rw [← sub_eq_zero, ← lc_sub]
    exact (hker _).1 h0
  let F : Sx D x₀ →ₗ[k] Matrix (Fin N) (Fin N) k :=
    { toFun := fun a => lc s (vOf a)
      map_add' := fun a b => by
        show lc s (vOf (a + b)) = lc s (vOf a) + lc s (vOf b)
        rw [key (a + b) (vOf a + vOf b) (by rw [lc_add, hvOf, hvOf]; rfl), lc_add]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [key (c • a) (c • vOf a) (by rw [lc_smul, hvOf]; rfl), lc_smul] }
  let ρ' : Sx D x₀ →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap F
    (by
      show lc s (vOf 1) = 1
      rw [key 1 D.u (by rw [u0]; rfl), u1])
    (fun a b => by
      show lc s (vOf (a * b)) = lc s (vOf a) * lc s (vOf b)
      rw [lc_mul s D.c m1, key (a * b) (fun t => ∑ j, ∑ j', vOf a j * vOf b j' * D.c j j' t)
        (by rw [← lc_mul s0 D.c m0 (vOf a) (vOf b), hvOf, hvOf]; rfl)])
  have hρ' : ∀ a, ρ' a = lc s (vOf a) := fun a => rfl
  have hEmem : ∀ t, lc s0 (D.κ t) ∈ Sx D x₀ := fun t => (memS _).2 ⟨_, rfl⟩
  have hrk : ∀ e : Sx D x₀, IsIdempotentElem e → ((Sx D x₀).val e).rank = (ρ' e).rank := by
    intro e he
    have he1 : IsIdempotentElem e.1 := congrArg Subtype.val he
    have hpart : ∀ t, e.1 * lc s0 (D.κ t) = 0 ∨ e.1 * lc s0 (D.κ t) = lc s0 (D.κ t) := by
      intro t
      have hc : Commute e.1 (lc s0 (D.κ t)) := hcomm _ e.2 _ (hEmem t)
      refine prim0 t _ ((memSpan _).1 (Subalgebra.mul_mem _ e.2 (hEmem t)))
        (IsIdempotentElem.mul_of_commute hc he1 (i0 t)) ?_
      rw [mul_assoc, (i0 t).eq]
    set T' := Finset.univ.filter (fun t => e.1 * lc s0 (D.κ t) ≠ 0) with hT'
    have hfe : e.1 = ∑ t ∈ T', lc s0 (D.κ t) := by
      rw [hT', Finset.sum_filter]
      conv_lhs => rw [← mul_one e.1, ← hsum0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs with h'
      · rcases hpart t with h | h
        · exact absurd h h'
        · exact h
      · exact not_not.1 h'
    have hrep : lc s0 (∑ t ∈ T', D.κ t) = e.1 := by
      rw [lc_sum]
      exact hfe.symm
    have r0 : (∑ t ∈ T', lc s0 (D.κ t)).rank = ∑ t ∈ T', (lc s0 (D.κ t)).rank :=
      (rank_sum_orth (fun t => lc s0 (D.κ t)) i0 o0 T').2
    have r1 : (∑ t ∈ T', lc s (D.κ t)).rank = ∑ t ∈ T', (lc s (D.κ t)).rank :=
      (rank_sum_orth (fun t => lc s (D.κ t)) i1 o1 T').2
    show e.1.rank = (lc s (vOf e)).rank
    rw [key e _ hrep, lc_sum, r1]
    conv_lhs => rw [hfe]
    rw [r0]
    simp only [hr0, hr1]
  obtain ⟨g, hg⟩ := hO N (Sx D x₀) hred (Sx D x₀).val ρ' hrk
  refine ⟨g, fun j => ?_⟩
  have hmem : s0 j ∈ Sx D x₀ := (memS _).2 ⟨Pi.single j 1, lc_single s0 j⟩
  have e1 := hg ⟨s0 j, hmem⟩
  rw [hρ', key _ (Pi.single j 1) (lc_single s0 j), lc_single] at e1
  exact e1

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
