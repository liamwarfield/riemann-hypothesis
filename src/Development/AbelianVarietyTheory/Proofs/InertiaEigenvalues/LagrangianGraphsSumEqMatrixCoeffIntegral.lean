module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaximalIsotropicDoubled
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.Doubling

variable {E : Type} [Field E] {r : ℕ}

def conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) : Submodule E (Fin r → E) where
  carrier := {w | (fun i => c (w i)) ∈ S}
  add_mem' := by
    intro a b ha hb
    have := S.add_mem ha hb
    simpa [Set.mem_setOf_eq, Pi.add_def] using this
  zero_mem' := by
    have h0 : (fun i => c ((0 : Fin r → E) i)) = 0 := by funext i; simp
    change (fun i => c ((0 : Fin r → E) i)) ∈ S
    rw [h0]
    exact S.zero_mem
  smul_mem' := by
    intro t a ha
    have := S.smul_mem (c t) ha
    simpa [Set.mem_setOf_eq, Pi.smul_def] using this

theorem mem_conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    w ∈ conjSub c S ↔ (fun i => c (w i)) ∈ S := ⟨fun h => h, fun h => h⟩

private theorem conj_mem_lemma (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    (fun i => c (w i)) ∈ conjSub c S ↔ w ∈ S := by
  rw [mem_conjSub]
  simp only [hc]

theorem finrank_conjSub (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (S : Submodule E (Fin r → E)) :
    Module.finrank E (conjSub c S) = Module.finrank E S := by
  let j : S ≃+ conjSub c S :=
    { toFun := fun x => ⟨fun i => c (x.1 i), (conj_mem_lemma c hc S x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => c (y.1 i), (mem_conjSub c S y.1).1 y.2⟩
      left_inv := fun x => Subtype.ext (funext fun i => hc (x.1 i))
      right_inv := fun y => Subtype.ext (funext fun i => hc (y.1 i))
      map_add' := fun x y => Subtype.ext (funext fun i => map_add c (x.1 i) (y.1 i)) }
  have hr : Module.rank E S = Module.rank E (conjSub c S) :=
    rank_eq_of_equiv_equiv (c : E → E) j c.bijective
      (fun t x => Subtype.ext (funext fun i => map_mul c t (x.1 i)))
  exact (congrArg Cardinal.toNat hr).symm

theorem row_apply (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (x v : Fin r → E) :
    (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) v () =
      (fun i => c (x i)) ⬝ᵥ J.mulVec v := by
  rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.of_apply]

theorem mem_orth (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (S : Submodule E (Fin r → E))
    (v : Fin r → E) :
    v ∈ (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)))
      ↔ ∀ x ∈ S, (fun i => c (x i)) ⬝ᵥ J.mulVec v = 0 := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [← row_apply c J x v]
  exact ⟨fun h => congrFun h (), fun h => funext fun u => by cases u; exact h⟩

theorem finrank_orth (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (J : Matrix (Fin r) (Fin r) E)
    (hJ : J.det ≠ 0) (S : Submodule E (Fin r → E)) :
    Module.finrank E
      (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
        Submodule E (Fin r → E)) + Module.finrank E S = r := by
  classical
  set T := conjSub c S
  have hTS : Module.finrank E T = Module.finrank E S := finrank_conjSub c hc S
  have hunit : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (isUnit_iff_ne_zero.2 hJ)
  set Ψ : (Fin r → E) →ₗ[E] Module.Dual E (Fin r → E) :=
    (dotProductEquiv E (Fin r)).toLinearMap ∘ₗ J.vecMulLinear
  have hΨ : Function.Injective Ψ :=
    (dotProductEquiv E (Fin r)).injective.comp (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  have hΨv : ∀ w v, Ψ w v = w ⬝ᵥ J.mulVec v := fun w v => by
    simp [Ψ, Matrix.dotProduct_mulVec]
  have hO : (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
      Submodule E (Fin r → E)) = (T.map Ψ).dualCoannihilator := by
    ext v
    rw [mem_orth, Submodule.mem_dualCoannihilator]
    constructor
    · rintro h φ ⟨w, hw, rfl⟩
      rw [hΨv]
      have hw' := (mem_conjSub c S w).1 hw
      have := h _ hw'
      simpa only [hc] using this
    · intro h x hx
      have hx' : (fun i => c (x i)) ∈ T := by
        rw [mem_conjSub]; simpa only [hc] using hx
      have := h _ ⟨_, hx', rfl⟩
      rwa [hΨv] at this
  have hW : Module.finrank E (T.map Ψ) = Module.finrank E T :=
    (Submodule.equivMapOfInjective Ψ hΨ T).finrank_eq.symm
  have key := Subspace.finrank_add_finrank_dualCoannihilator_eq (T.map Ψ)
  rw [Module.finrank_fin_fun, hW, hTS] at key
  rw [hO]
  omega

theorem finrank_map_fst (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.fst E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.fst E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inr E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).2) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).1 = 0 := hy
      have hy' : (LinearMap.inr E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).2 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext h1.symm rfl
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).2, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

theorem finrank_map_snd (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.snd E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.snd E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inl E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).1) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).2 = 0 := hy
      have hy' : (LinearMap.inl E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).1 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext rfl h1.symm
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).1, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

private theorem conj_single_lemma (c : E ≃+* E) (i : Fin r) :
    (fun k => c ((Pi.single i (1 : E) : Fin r → E) k)) = (Pi.single i (1 : E) : Fin r → E) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem isometry_matrix (c : E ≃+* E) (J g : Matrix (Fin r) (Fin r) E)
    (h : ∀ x x' : Fin r → E, (fun i => c (x i)) ⬝ᵥ J.mulVec x' =
      (fun i => c ((g.mulVec x) i)) ⬝ᵥ J.mulVec (g.mulVec x')) :
    (g.map c).transpose * J * g = J := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [conj_single_lemma c i] at h1
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at h1
  rw [h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
    Matrix.mulVec, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)

theorem maximal_isotropic_doubled (E : Type) [Field E] (c : E ≃+* E) (r : ℕ)
    (J : Matrix (Fin r) (Fin r) E) (hc : ∀ x, c (c x) = x) (hJ : J.det ≠ 0)
    (_hJh : J.transpose.map c = J) (Y : Submodule E ((Fin r → E) × (Fin r → E)))
    (hY : Module.finrank E Y = r)
    (hiso : ∀ y ∈ Y, ∀ y' ∈ Y, (fun i => c (y.1 i)) ⬝ᵥ J.mulVec y'.1 =
      (fun i => c (y.2 i)) ⬝ᵥ J.mulVec y'.2) :
    (Module.finrank E (Y.comap (LinearMap.inl E _ _)) =
        Module.finrank E (Y.comap (LinearMap.inr E _ _))) ∧
      Y.map (LinearMap.fst E _ _) = ⨅ x ∈ Y.comap (LinearMap.inl E _ _),
        LinearMap.ker ((Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j))) ∧
      (Y.comap (LinearMap.inl E _ _) = ⊥ ↔ ∃ g : GL (Fin r) E,
        ((g : Matrix (Fin r) (Fin r) E).map c).transpose * J * (g : Matrix (Fin r) (Fin r) E) = J ∧
          ∀ y, y ∈ Y ↔ y.2 = (g : Matrix (Fin r) (Fin r) E).mulVec y.1) := by
  classical
  set A := Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) with hA
  set B := Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) with hB
  have memA : ∀ a, a ∈ A ↔ ((a, 0) : (Fin r → E) × (Fin r → E)) ∈ Y := fun a => by
    rw [hA, Submodule.mem_comap, LinearMap.inl_apply]
  have memB : ∀ b, b ∈ B ↔ (((0 : Fin r → E), b) : (Fin r → E) × (Fin r → E)) ∈ Y := fun b => by
    rw [hB, Submodule.mem_comap, LinearMap.inr_apply]
  have hfst := finrank_map_fst Y
  have hsnd := finrank_map_snd Y
  rw [← hB, hY] at hfst
  rw [← hA, hY] at hsnd
  have hoA := finrank_orth c hc J hJ A
  have hoB := finrank_orth c hc J hJ B
  have le1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ A,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro a ha
    have := hiso _ ((memA a).1 ha) y hy
    simpa using this
  have le2 : Y.map (LinearMap.snd E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ B,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro b hb
    have := hiso _ ((memB b).1 hb) y hy
    simpa using this.symm
  have d1 := Submodule.finrank_mono le1
  have d2 := Submodule.finrank_mono le2
  have hAB : Module.finrank E A = Module.finrank E B := by omega
  refine ⟨hAB, Submodule.eq_of_le_of_finrank_eq le1 (by omega), ?_⟩
  constructor
  · intro hA0
    have hA0' : Module.finrank E A = 0 := by rw [hA0]; exact finrank_bot E (Fin r → E)
    have hB0 : B = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hP1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) = ⊤ :=
      Submodule.eq_of_le_of_finrank_eq le_top (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    let f : Y →ₗ[E] (Fin r → E) := (LinearMap.fst E (Fin r → E) (Fin r → E)).comp Y.subtype
    have hf : ∀ y : Y, f y = (y : (Fin r → E) × (Fin r → E)).1 := fun y => rfl
    have finj : Function.Injective f := by
      intro y y' hyy
      rw [hf, hf] at hyy
      have hd : (y : (Fin r → E) × (Fin r → E)) - y' ∈ Y := Y.sub_mem y.2 y'.2
      have h2 : ((y : (Fin r → E) × (Fin r → E)) - y').2 ∈ B := by
        rw [memB]
        convert hd using 1
        exact Prod.ext (by simp [hyy]) rfl
      rw [hB0, Submodule.mem_bot, Prod.snd_sub, sub_eq_zero] at h2
      exact Subtype.ext (Prod.ext hyy h2)
    have fsurj : Function.Surjective f := by
      intro v
      have hv : v ∈ Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) := hP1 ▸ Submodule.mem_top
      obtain ⟨y, hy, rfl⟩ := hv
      exact ⟨⟨y, hy⟩, rfl⟩
    let e := LinearEquiv.ofBijective f ⟨finj, fsurj⟩
    let T : (Fin r → E) →ₗ[E] (Fin r → E) :=
      (LinearMap.snd E (Fin r → E) (Fin r → E)).comp (Y.subtype.comp e.symm.toLinearMap)
    have hT : ∀ v, T v = ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).2 := fun v => rfl
    have he1 : ∀ v, ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).1 = v := fun v => by
      rw [← hf]
      exact e.apply_symm_apply v
    have hgraph : ∀ y : (Fin r → E) × (Fin r → E), y ∈ Y ↔ y.2 = T y.1 := by
      intro y
      constructor
      · intro hy
        have hyy : (⟨y, hy⟩ : Y) = e.symm y.1 := finj (by rw [hf, hf, he1])
        rw [hT, ← hyy]
      · intro h
        have hy : y = ((e.symm y.1 : Y) : (Fin r → E) × (Fin r → E)) :=
          Prod.ext (he1 _).symm (h.trans (hT _))
        rw [hy]
        exact (e.symm y.1).2
    set M := LinearMap.toMatrix' T with hMdef
    have hM : ∀ v, M.mulVec v = T v := fun v => LinearMap.toMatrix'_mulVec T v
    have hdet : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv
      have hv0 : (v, (0 : Fin r → E)) ∈ Y := by
        rw [hgraph, ← hM, hMv]
      have hvA : v ∈ A := (memA v).2 hv0
      rw [hA0, Submodule.mem_bot] at hvA
      exact hvA
    refine ⟨Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.mpr hdet), ?_, ?_⟩
    · show (M.map c).transpose * J * M = J
      apply isometry_matrix
      intro x x'
      have hx := (hgraph (x, T x)).2 rfl
      have hx' := (hgraph (x', T x')).2 rfl
      have := hiso _ hx _ hx'
      rw [hM, hM]
      exact this
    · intro y
      show y ∈ Y ↔ y.2 = M.mulVec y.1
      rw [hM]
      exact hgraph y
  · rintro ⟨g, -, hg⟩
    rw [eq_bot_iff]
    intro a ha
    rw [memA, hg] at ha
    have hinv : ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((g : Matrix (Fin r) (Fin r) E).mulVec a) = a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← ha, Matrix.mulVec_zero] at hinv
    rw [Submodule.mem_bot, ← hinv]

end GlobalTheory.Doubling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Graphs

variable {D : D7}

def graphSub (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearMap.range (LinearMap.prod LinearMap.id (Matrix.mulVecLin c))

theorem mem_graphSub {W : HSp D} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    {y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)} : y ∈ graphSub W c ↔ y.2 = c *ᵥ y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨y.1, Prod.ext rfl (by simp [h])⟩

theorem cT_eq (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) c = cᴴ := by
  funext i j
  rfl

theorem star_dot (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

def graphLag (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : Lag W :=
  ⟨graphSub W g, by
    rw [graphSub, LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
        W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    rw [cT_eq] at h
    show star x ⬝ᵥ W.gram *ᵥ y = star ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x) ⬝ᵥ
      W.gram *ᵥ ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ y)
    rw [star_dot, h]⟩

theorem graphLag_bot (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    (graphLag W g hg).1.comap (LinearMap.inl D.host.E _ _) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h : (0 : Fin W.rank → D.host.E) = (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x :=
    mem_graphSub.1 (Submodule.mem_comap.1 hx)
  have h2 := congrArg (((g⁻¹ : GL (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using h2.symm

theorem herm' (W : HSp D) : W.gramᵀ.map (starRingAut : D.host.E ≃+* D.host.E) = W.gram := by
  have h := GlobalTheory.AutFunCounterexample.gram_herm W
  funext i j
  exact congrFun (congrFun h i) j

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ g : GL (Fin W.rank) D.host.E,
    g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧ Formalism.UG.bc (incA D) g = matHom W (γ : GA D W) := by
  have h : matHom W (γ : GA D W) ∈ HFin (AF D.host.F) D.sp.cm.sig W.gram := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg, e⟩

def ratG (W : HSp D) (γ : GQ W) : GL (Fin W.rank) D.host.E := (exists_rat W γ).choose

theorem ratG_mem (W : HSp D) (γ : GQ W) :
    ratG W γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := (exists_rat W γ).choose_spec.1

theorem mt_ratG (W : HSp D) (γ : GQ W) :
    Formalism.L2.Theta.mt W (γ : GA D W) = (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) := by
  rw [Formalism.L2.Theta.mt, ← (exists_rat W γ).choose_spec.2]
  rfl

theorem bc_injective (W : HSp D) {g g' : GL (Fin W.rank) D.host.E}
    (h : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) =
      (g' : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) : g = g' := by
  exact Units.ext (Matrix.ext fun i j => incA_injective D (congrFun (congrFun h i) j))

theorem graphSub_injective (W : HSp D) {c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : graphSub W c = graphSub W c') : c = c' := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hx : (x, c *ᵥ x) ∈ graphSub W c' := h ▸ mem_graphSub.2 rfl
  exact mem_graphSub.1 hx

theorem isLagFrame_graph (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    IsLagFrame W (graphLag W g hg) (1, (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)) := by
  have h := congrArg (Submodule.map (LinearMap.prod (LinearMap.id : (Fin W.rank → D.host.E) →ₗ[D.host.E] _)
    (Matrix.mulVecLin (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E))))
    (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  refine Eq.trans ?_ h
  congr 2
  funext j
  ext a <;> simp [Matrix.one_apply, Pi.single_apply]

theorem hr_mem (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
  show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
      ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      W.gram.map (inclR (F := D.host.F) (AF D.host.F)) *
      (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) =
      W.gram.map (inclR (F := D.host.F) (AF D.host.F))
  rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, h]

def ofRat (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : GQ W :=
  ⟨(⟨Formalism.UG.bc (incA D) g, hr_mem W g hg⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram),
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

end GlobalTheory.RawLift.Graphs

namespace GlobalTheory.RawLift.Graphs

open GlobalTheory.RawLift.Graphs

theorem graphs : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  intro D W
  let f : GQ W → {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} :=
    fun γ => ⟨graphLag W (ratG W γ) (ratG_mem W γ), graphLag_bot W _ _⟩
  have hinj : Function.Injective f := by
    intro γ γ' h
    have h1 : graphSub W (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = graphSub W (ratG W γ') :=
      congrArg (fun Y => Y.1.1) h
    have h2 := graphSub_injective W h1
    have h3 : Formalism.L2.Theta.mt W (γ : GA D W) = Formalism.L2.Theta.mt W (γ' : GA D W) := by
      rw [mt_ratG, mt_ratG, h2]
    exact Subtype.ext (GlobalTheory.AutFunCounterexample.GA_ext W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨g, hgU, hgY⟩ := ((GlobalTheory.Doubling.maximal_isotropic_doubled D.host.E starRingAut W.rank W.gram
      (fun x => star_star x) (GlobalTheory.AutFunCounterexample.gram_det_ne W) (herm' W) Y.1 Y.2.1 Y.2.2).2.2).1 hY
    have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := hgU
    refine ⟨ofRat W g hg, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ratG W (ofRat W g hg) = g := bc_injective W ((mt_ratG W _).symm.trans rfl)
    show graphSub W (ratG W (ofRat W g hg)) = Y.1
    rw [e1]
    ext y
    rw [mem_graphSub]
    exact (hgY y).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ⟨_, mt_ratG W γ, isLagFrame_graph W _ (ratG_mem W γ)⟩⟩

end GlobalTheory.RawLift.Graphs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  first | exact @GlobalTheory.RawLift.Graphs.graphs | exact GlobalTheory.RawLift.Graphs.graphs | (intros; apply GlobalTheory.RawLift.Graphs.graphs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomain
open MeasureTheory

namespace GlobalTheory

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    {Γ : Subgroup G} [Countable Γ] {𝓖 : Set G}

theorem fundamentalDomain_lintegral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G) :
    ∫⁻ y in 𝓖, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂ν
      = ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν := by
  rw [lintegral_tsum (fun γ => by fun_prop)]
  set F : G → ENNReal := fun g => ‖P (x⁻¹ * g)‖ₑ * ‖a x‖ₑ * ‖b g‖ₑ with hF
  have key : ∀ γ : Γ, ∀ y, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = ‖P (x⁻¹ * ((γ : G)⁻¹ * y))‖ₑ * ‖a x‖ₑ * ‖b ((γ : G)⁻¹ * y)‖ₑ
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.lintegral_eq_tsum' F, ← lintegral_mul_left_eq_self _ x]
  simp [hF]

theorem fundamentalDomain_integral_unfold_left (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {a b P : G → ℂ}
    (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) (hbm : Measurable b) (hPm : Measurable P) (x : G)
    (hfin : ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ≠ ⊤) :
    ∑' γ : Γ, ∫ y in 𝓖, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) ∂ν
      = ∫ g, star (a x) * b (x * g) * P g ∂ν := by
  set F : G → ℂ := fun g => star (a x) * b g * P (x⁻¹ * g) with hF
  have hFi : Integrable F ν := by
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_mul_left_eq_self _ x]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    refine lintegral_congr (fun g => ?_)
    have hs : ‖star (a x)‖ₑ = ‖a x‖ₑ := by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
    simp only [hF, enorm_mul, hs, inv_mul_cancel_left]
    ring
  have key : ∀ γ : Γ, ∀ y, star (a x) * b y * P (x⁻¹ * (γ : G)⁻¹ * y) = F (γ⁻¹ • y) := by
    intro γ y
    have h1 : γ⁻¹ • y = (γ : G)⁻¹ * y := by simp [Subgroup.smul_def]
    rw [hF, h1]
    show _ = star (a x) * b ((γ : G)⁻¹ * y) * P (x⁻¹ * ((γ : G)⁻¹ * y))
    rw [hb _ (Γ.inv_mem γ.2)]; simp only [mul_assoc]
  simp_rw [key]
  rw [← h𝓖.integral_eq_tsum' F hFi, ← integral_mul_left_eq_self F x]
  simp [hF]

theorem unfold_tsum_fundamentalDomain (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (a b P : G → ℂ)
    (ha : Continuous a) (hbc : Continuous b) (hb : ∀ γ ∈ Γ, ∀ g, b (γ * g) = b g)
    (hP : StronglyMeasurable P)
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  have ham : Measurable a := ha.measurable
  have hbm : Measurable b := hbc.measurable
  have hPm : Measurable P := hP.measurable
  have hs : ∀ z : ℂ, ‖star z‖ₑ = ‖z‖ₑ := fun z => by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  set μ := ν.restrict 𝓖 with hμ

  have hT : ∫⁻ x, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν ∂μ ≠ ⊤ := by
    rw [← lintegral_congr (fun x => fundamentalDomain_lintegral_unfold_left h𝓖 hb hbm hPm (a := a) x)]
    exact hfin
  set k : G → G → ℂ := fun x g => star (a x) * b (x * g) * P g with hk
  have hkm : Measurable (Function.uncurry k) := by
    simp only [hk, Function.uncurry_def]; fun_prop
  have hki : Integrable (Function.uncurry k) (μ.prod ν) := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ (by fun_prop)]
    refine lt_of_le_of_lt (le_of_eq ?_) hT.lt_top
    refine lintegral_congr (fun x => lintegral_congr (fun g => ?_))
    simp only [hk, Function.uncurry_apply_pair, enorm_mul, hs]
    ring
  refine ⟨?_, ?_⟩
  · have h1 := hki.swap.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun g => ?_))
    simp only [hk, Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [integral_mul_const, mul_comm]

  · set f : Γ → G × G → ℂ := fun γ z => star (a z.1) * b z.2 * P (z.1⁻¹ * (γ : G)⁻¹ * z.2) with hf
    have hfm : ∀ γ, Measurable (f γ) := fun γ => by simp only [hf]; fun_prop
    have hfe : ∀ γ x y, ‖f γ (x, y)‖ₑ = ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ := by
      intro γ x y; simp only [hf, enorm_mul, hs]; ring
    have hsum : ∑' γ : Γ, ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (fun γ => ((hfm γ).enorm.lintegral_prod_right').aemeasurable)]
      have hx : ∀ x, ∑' γ : Γ, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ
          = ∫⁻ y, ∑' γ : Γ, ‖P (x⁻¹ * (γ : G)⁻¹ * y)‖ₑ * ‖a x‖ₑ * ‖b y‖ₑ ∂μ := fun x => by
        rw [← lintegral_tsum (f := fun γ y => ‖f γ (x, y)‖ₑ)
          (fun γ => ((hfm γ).comp measurable_prodMk_left).enorm.aemeasurable)]
        simp only [hfe]
      rw [lintegral_congr hx]
      exact hfin
    have hfi : ∀ γ, Integrable (f γ) (μ.prod μ) := fun γ =>
      ⟨(hfm γ).aestronglyMeasurable, by
        unfold HasFiniteIntegral
        rw [lintegral_prod _ (hfm γ).enorm.aemeasurable]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ => ∫⁻ x, ∫⁻ y, ‖f γ (x, y)‖ₑ ∂μ ∂μ) γ)
          hsum.lt_top⟩
    have lhs : ∀ γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν)
        = ∫ x, ∫ y, f γ (x, y) ∂μ ∂μ := by
      intro γ; rw [← Measure.prod_restrict, ← integral_prod _ (hfi γ)]
    rw [tsum_congr lhs, ← integral_tsum (fun γ => (hfi γ).integral_prod_left.aestronglyMeasurable)
      (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun γ =>
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _))]
    have hae : ∀ᵐ x ∂μ, ∫⁻ g, ‖P g‖ₑ * ‖a x‖ₑ * ‖b (x * g)‖ₑ ∂ν < ⊤ :=
      ae_lt_top (show Measurable (fun z : G × G => ‖P z.2‖ₑ * ‖a z.1‖ₑ * ‖b (z.1 * z.2)‖ₑ) by
        fun_prop).lintegral_prod_right' hT
    have step : (∫ x, ∑' γ : Γ, ∫ y, f γ (x, y) ∂μ ∂μ) = ∫ x, ∫ g, k x g ∂ν ∂μ :=
      integral_congr_ae (hae.mono fun x hx => fundamentalDomain_integral_unfold_left h𝓖 hb hbm hPm x hx.ne)
    rw [step, integral_integral_swap hki]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hk]
    rw [integral_mul_const, mul_comm]
end
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomainStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_tsum_integral_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → ∀ (a b P : G → ℂ), Continuous a → Continuous b →
    (∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) → StronglyMeasurable P →
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ →
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  first | exact @GlobalTheory.unfold_tsum_fundamentalDomain | exact GlobalTheory.unfold_tsum_fundamentalDomain | (intros; apply GlobalTheory.unfold_tsum_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem graph_term_of_termMove {D : D7} (hTM : TermMove D) {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) {Y : Lag W} (hY : IsLagFrame W Y (1, c)) (g₁ g₂ : GA D W) :
    lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂) = thetaIP μ 𝓕 (om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂) f₁ := by
  have hmul : ∀ p q (f : WO V W → ℂ), om p (om q f) = om (p * q) f := fun p q f => by rw [map_mul]; rfl
  have p₁ := hS.weil.om_pres (1, g₁) f₁ h₁
  have p₂ := hS.weil.om_pres (1, g₂) f₂ h₂
  obtain ⟨hfr, hg⟩ := hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ p₁ p₂
  have e1 : om (1, g₁⁻¹) (om (1, γ⁻¹) (om (1, g₂) f₂)) = om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂ := by
    rw [hmul, hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, mul_assoc]
  have e2 : om (1, g₁⁻¹) (om (1, g₁) f₁) = f₁ := by
    rw [hmul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  rw [← hfr Y (1, c) hY, (hg γ hγ c hc).2,
    ← GlobalTheory.T.theta_pairing_invariant D ψ V W χV χW om μ 𝓕 hS.weil hS.covol (1, g₁⁻¹) _ _ (hS.weil.om_pres (1, γ⁻¹) _ p₂) p₁, e1, e2]


open scoped GlobalTheory.GaugeEx in
theorem rallis_graphs : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  intro D hEA hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI := hS.haarW
  obtain ⟨e, he⟩ := GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary D W
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : Countable (GQ W) := e.injective.countable
  choose c hc hcf using he
  let P : GA D W → ℂ := fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁
  have hT : ∀ (γ : GQ W) (p : GA D W × GA D W),
      lagTerm μ 𝓕 (fr (e γ).1) (om (1, p.1) f₁) (om (1, p.2) f₂) = P (p.1⁻¹ * (γ : GA D W)⁻¹ * p.2) :=
    fun γ p => graph_term_of_termMove hTM hS hf₁ hf₂ γ.2 (hc γ) (hcf γ) p.1 p.2
  have hPm : StronglyMeasurable P := by
    have h := GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ hf₁ hf₂ (1, 1)
    have hcont : Continuous fun g : GA D W => ((1 : GA D W), g) := continuous_const.prodMk continuous_id
    convert h.comp_measurable hcont.measurable using 1
    funext g
    simp only [Function.comp_apply]
    rw [lagTerm_one_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : GQ W, ‖P (g₁⁻¹ * (γ : GA D W)⁻¹ * g₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hEA ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂) ?_
    refine lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_
    have hinj : Function.Injective fun γ : GQ W => (e γ).1 := Subtype.val_injective.comp e.injective
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun Y => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ))
    refine tsum_congr fun γ => ?_
    rw [← hT γ (g₁, g₂)]
  obtain ⟨hI, hE⟩ := GlobalTheory.T.unfold_tsum_integral_fundamentalDomain νW (GQ W) 𝓖 hS.fdW φ₁ φ₂ P ha₁.cont ha₂.cont ha₂.left hPm hfin
  refine ⟨hI, ?_⟩
  refine ((e.tsum_eq (fun Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} =>
    ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW))).symm.trans ?_).trans hE
  refine tsum_congr fun γ => ?_
  congr 1
  funext p
  rw [hT γ p]

end GlobalTheory.RawLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  first | exact @GlobalTheory.RawLift.rallis_graphs | exact GlobalTheory.RawLift.rallis_graphs | (intros; apply GlobalTheory.RawLift.rallis_graphs <;> assumption)
end
