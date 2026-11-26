module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.DiagDC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym.Sig

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem sc_eq (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = dg (fun _ : Fin n => z) := by
  apply Units.ext
  ext i j
  simp [dg, val_diagT, GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]

private theorem sc_comm (z : kˣ) (g : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) z * g = g * GeneralLinearGroup.scalar (Fin n) z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_eq, dg, val_diagT]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem sc_mem_iff (V : Lev k) (hn : 0 < n) (z : kˣ) :
    GeneralLinearGroup.scalar (Fin n) z ∈ V.J n ↔ z ∈ V.H := by
  constructor
  · intro h
    obtain ⟨u, hu, e⟩ := ((memJ k V n _).1 h).2.2 ⟨0, hn⟩
    have : u = z := by
      apply Units.ext
      rw [e, sc_eq, dg, val_diagT]
      simp
    exact this ▸ hu
  · intro h
    rw [sc_eq]
    exact le_sup_left (b := (glIwa k n).Nm V.c) (le_sup_right (a := (glIwa k n).N) ⟨fun _ => z, fun _ _ => h, rfl⟩)

private theorem dom_of (d : Fin n → kˣ) (hd : SDom d) : Dom d := fun i j h =>
  h.eq_or_lt.elim (fun e => by rw [e]) (fun l => (hd i j l).le)

private theorem H_of_mem (V : Lev k) (hn : 0 < n) {d : Fin n → kˣ} (hd : SDom d) {g : GL (Fin n) k}
    (hg : g ∈ V.DC d) {z : kˣ} (h : GeneralLinearGroup.scalar (Fin n) z * g ∈ V.DC d) : z ∈ V.H := by
  obtain ⟨j, hj, _, ⟨t, ht, rfl⟩, e⟩ := contract k V n (MonoidHom.id _) (pres_id V n) d hd g hg
  obtain ⟨a, ha, b, hb, e2⟩ := h
  have e3 : dg ((fun _ => z) * t * d) = (j⁻¹ * a) * dg d * (b * j) := by
    have e4 : dg ((fun _ => z) * t * d) = GeneralLinearGroup.scalar (Fin n) z * (diagT k (Fin n) t * dg d) := by
      rw [sc_eq, dg, dg, dg, map_mul, map_mul, mul_assoc]
    rw [e4, ← e, MonoidHom.id_apply]
    calc
      GeneralLinearGroup.scalar (Fin n) z * (j⁻¹ * g * j)
          = j⁻¹ * (GeneralLinearGroup.scalar (Fin n) z * g) * j := by
        rw [← mul_assoc, ← mul_assoc, sc_comm z j⁻¹]; simp only [mul_assoc]
      _ = _ := by rw [e2]; group
  have h1 : dg ((fun _ => z) * t * d) ∈ V.DC d := ⟨_, mul_mem (inv_mem hj) ha, _, mul_mem hb hj, e3⟩
  have h2 := (diagDC k V n d _ (dom_of d hd)).1 h1 ⟨0, hn⟩
  have h3 : z * t ⟨0, hn⟩ * d ⟨0, hn⟩ / d ⟨0, hn⟩ ∈ V.H := h2
  have h4 := div_mem h3 (ht ⟨0, hn⟩ trivial)
  simpa using h4

private theorem mem_ZJ (V : Lev k) (u : GL (Fin n) k) :
    u ∈ V.ZJ n ↔ ∃ z : kˣ, ∃ j ∈ V.J n, u = GeneralLinearGroup.scalar (Fin n) z * j := by
  haveI : (GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k).range.Normal := ⟨by
    rintro _ ⟨z, rfl⟩ g
    exact ⟨z, by rw [← sc_comm z g]; simp⟩⟩
  rw [← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
    exact ⟨z, j, hj, rfl⟩
  · rintro ⟨z, j, hj, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩

private theorem fZ_eq (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (hn : 0 < n)
    {d : Fin n → kˣ} (hd : SDom d) {z : kˣ} {g : GL (Fin n) k}
    (h : (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g ∈ V.DC d) :
    V.fZ ω d g = (((ω z)⁻¹ : ℂˣ) : ℂ) := by
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g ∈ V.DC d := ⟨z, h⟩
  rw [Lev.fZ, dite_eq_left hex]
  have hc := hex.choose_spec
  generalize hex.choose = c at hc ⊢
  have h1 : z / c ∈ V.H := H_of_mem V hn hd h (g := (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g) (by
    convert hc using 1
    simp only [map_div, div_eq_mul_inv, map_mul, map_inv]
    rw [sc_comm z, ← mul_assoc, mul_assoc _ _ g]
    group)
  have h2 := hω _ h1
  rw [map_div, div_eq_one] at h2
  rw [h2]

private theorem dc_tr (V : Lev k) {d : Fin n → kˣ} {c : kˣ} {g u u' : GL (Fin n) k}
    (hu : u ∈ V.J n) (hu' : u' ∈ V.J n) (h : (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d) :
    (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (u * g * u') ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, e⟩ := h
  refine ⟨u * a, mul_mem hu ha, b * u', mul_mem hb hu', ?_⟩
  have : (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (u * g * u') =
      u * ((GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g) * u' := by
    rw [← map_inv, ← mul_assoc, ← mul_assoc, sc_comm c⁻¹ u]; simp only [mul_assoc]
  rw [this, e]; group

end

theorem UpperTheory.V.Z.Sym.Sig.eqZ :
    UpperTheory.V.Z.Sym.Sig.EqZ := by
  intro k _ _ _ _ V ω hω n hn
  have wd : ∀ (z z' : kˣ) (j j' : GL (Fin n) k), j ∈ V.J n → j' ∈ V.J n →
      GeneralLinearGroup.scalar (Fin n) z * j = GeneralLinearGroup.scalar (Fin n) z' * j' → ω z = ω z' := by
    intro z z' j j' hj hj' e
    have h1 : GeneralLinearGroup.scalar (Fin n) (z'⁻¹ * z) = j' * j⁻¹ := by
      rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    have h2 : z'⁻¹ * z ∈ V.H := (sc_mem_iff V hn _).1 (h1 ▸ mul_mem hj' (inv_mem hj))
    have h3 := hω _ h2
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3.symm
  have hZ : ∀ u : V.ZJ n, ∃ z : kˣ, ∃ j ∈ V.J n, (u : GL (Fin n) k) = GeneralLinearGroup.scalar (Fin n) z * j :=
    fun u => (mem_ZJ V u.1).1 u.2
  choose Z Jf hJ eZ using hZ
  refine ⟨⟨MonoidHom.mk' (fun u => ω (Z u)) ?_, ?_⟩, mem_ZJ V, ?_⟩
  · intro u v
    rw [← map_mul]
    refine wd _ _ _ _ (hJ (u * v)) (mul_mem (hJ u) (hJ v)) ?_
    rw [← eZ (u * v), Subgroup.coe_mul, eZ u, eZ v, map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (Jf u), ← sc_comm, mul_assoc]
  · intro z j u hj e
    exact wd _ _ _ _ (hJ u) hj ((eZ u).symm.trans e)
  · intro d hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z g hg
      exact fZ_eq V ω hω hn hd (by rwa [inv_mul_cancel_left])
    · intro z g
      by_cases h : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (z := z * c) (by
          convert hc using 1
          rw [map_mul]
          group), map_mul, mul_inv, Units.val_mul]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = 0 :=
          dif_neg (fun ⟨c, hc⟩ => h ⟨z⁻¹ * c, by
            convert hc using 1
            rw [map_mul, map_inv]
            group⟩)
        rw [h0, h1, mul_zero]
    · intro u hu u' hu' g
      by_cases h : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (dc_tr V hu hu' hc)]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (u * g * u') = 0 := dif_neg (fun ⟨c, hc⟩ => h ⟨c, by
          have h2 := dc_tr V (inv_mem hu) (inv_mem hu') hc
          have e : u⁻¹ * (u * g * u') * u'⁻¹ = g := by group
          rwa [e] at h2⟩)
        rw [h0, h1]
    · have hfin := ((finFacts k V).2.2.2.2.2 n).1 (dg d)
      refine (Set.Finite.image (fun q : GL (Fin n) k ⧸ V.J n =>
        ((q.out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n)) hfin).subset ?_
      intro y hy
      have hex : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * y.out ∈ V.DC d := by
        by_contra h
        exact hy (dif_neg h)
      obtain ⟨c, a, ha, b, hb, e⟩ := hex
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)
      refine ⟨((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n), ⟨⟨a, ha⟩, rfl⟩, ?_⟩
      show ((((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n).out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n) = y
      have e1 : y.out = (a * dg d) * (GeneralLinearGroup.scalar (Fin n) c * b) := by
        calc
          y.out = GeneralLinearGroup.scalar (Fin n) c *
              ((GeneralLinearGroup.scalar (Fin n) c)⁻¹ * y.out) := by group
          _ = GeneralLinearGroup.scalar (Fin n) c * (a * dg d * b) := by rw [e]
          _ = _ := by rw [← mul_assoc, sc_comm c (a * dg d), mul_assoc]
      rw [hj, ← QuotientGroup.out_eq' y, QuotientGroup.eq, e1]
      refine (mem_ZJ V _).2 ⟨c, (j : GL (Fin n) k)⁻¹ * b, mul_mem (inv_mem j.2) hb, ?_⟩
      calc (a * dg d * (j : GL (Fin n) k))⁻¹ * (a * dg d * (GeneralLinearGroup.scalar (Fin n) c * b))
          = (j : GL (Fin n) k)⁻¹ * GeneralLinearGroup.scalar (Fin n) c * b := by group
        _ = _ := by rw [← sc_comm, mul_assoc]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.HkEqUOp
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym.Sig

section Gen

variable {G : Type} [Group G]

private theorem sum_reps {I : Subgroup G} (F : LeviFact I) (a : G) (hI : HeckePair I) (hp : F.Pos a)
    (hn : F.NormJ a) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I a v : M) = ∑ u ∈ s, ρ (u * a) v := by
  classical
  obtain ⟨-, h2, -⟩ := hkApply A G M ρ I I a (hI a)
  have hsm : ∀ g : I, g • (a : G ⧸ I) = ((g * a : G) : G ⧸ I) := fun g => rfl
  have hg' : ∀ g ∈ I, ∃ u ∈ F.Uf ⊓ I, ((g * a : G) : G ⧸ I) = ((u * a : G) : G ⧸ I) := by
    intro g hg
    obtain ⟨u, hu, m, hm, l, hl, rfl⟩ := F.fact g hg
    refine ⟨u, hu, ?_⟩
    rw [QuotientGroup.eq]
    have e : (u * m * l * a)⁻¹ * (u * a) = (a⁻¹ * l * a)⁻¹ * (a⁻¹ * m * a)⁻¹ := by group
    rw [e]
    exact I.mul_mem (I.inv_mem (hp.2.2 l hl)) (I.inv_mem (hn m hm).2)
  show (hk2 ρ I I a v : M) = _
  rw [h2 (s.image (· * a)) ?_ ?_ v, Finset.sum_image]
  · intro x _ y _ hxy
    exact mul_right_cancel hxy
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨u, (hs u hu).2⟩, hsm _⟩
  · intro q hq
    obtain ⟨⟨g, hg⟩, rfl⟩ := hq
    obtain ⟨u', hu', he⟩ := hg' g hg
    obtain ⟨u, ⟨hus, hui⟩, huniq⟩ := hs' u' hu'
    have hq : ((u * a : G) : G ⧸ I) = ((u' * a : G) : G ⧸ I) := by
      rw [QuotientGroup.eq]
      have e : (u * a)⁻¹ * (u' * a) = a⁻¹ * (u⁻¹ * u') * a := by group
      rw [e]
      exact hui
    refine ⟨u * a, ⟨Finset.mem_image_of_mem _ hus, ?_⟩, ?_⟩
    · show ((u * a : G) : G ⧸ I) = ((g * a : G) : G ⧸ I)
      rw [he, hq]
    · rintro y ⟨hy, hyq⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      change ((w * a : G) : G ⧸ I) = ((g * a : G) : G ⧸ I) at hyq
      have hw' : w = u := by
        apply huniq w
        refine ⟨hw, ?_⟩
        rw [he] at hyq
        have e : a⁻¹ * (w⁻¹ * u') * a = (w * a)⁻¹ * (u' * a) := by group
        rw [e, ← QuotientGroup.eq]
        exact hyq
      simp [hw']

private theorem hk_eq_uOp (D : Iwa G) {I : Subgroup G} (F : LeviFact I) (a : G) (hI : HeckePair I)
    (hp : F.Pos a) (hn : F.NormJ a) (hU : F.Uf ⊓ I = D.N)
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I a v : M) = D.uOp ρ a v := by
  classical
  have hNI : ∀ y ∈ D.N, y ∈ F.Uf ⊓ I := fun y hy => hU ▸ hy
  have hND : ∀ y ∈ F.Uf ⊓ I, y ∈ D.N := fun y hy => by rwa [hU] at hy
  have hc : ∀ y : G, y ∈ D.Nconj a ↔ a⁻¹ * y * a ∈ D.N := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      have e : a⁻¹ * ((MulAut.conj a).toMonoidHom m) * a = m := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [e]
      exact hm
    · intro h
      refine ⟨a⁻¹ * y * a, h, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
  have heq : ∀ u x : D.N, ((u : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) = (x : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N)) ↔
      a⁻¹ * ((u : G)⁻¹ * x) * a ∈ I := by
    intro u x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hc]
    push_cast
    constructor
    · intro h
      exact (hNI _ h).2
    · intro h
      have hy : (u : G)⁻¹ * x ∈ F.Uf := (hNI _ (D.N.mul_mem (D.N.inv_mem u.2) x.2)).1
      have hm : a⁻¹ * ((u : G)⁻¹ * x) * a ∈ F.Uf ⊓ I :=
        ⟨by simpa using F.M_U a⁻¹ (F.Mf.inv_mem hp.1) _ hy, h⟩
      exact hND _ hm
  have hfin : Finite (↥D.N ⧸ (D.Nconj a).subgroupOf D.N) := by
    have := (hI a).to_subtype
    refine Finite.of_injective (β := MulAction.orbit I (a : G ⧸ I))
      (fun q => ⟨(((Quotient.out q : D.N) : G) * a : G), ⟨⟨_, (hNI _ (Quotient.out q).2).2⟩, rfl⟩⟩) ?_
    intro q q' hqq
    have h1 : (((Quotient.out q : D.N) : G) * a : G ⧸ I) = (((Quotient.out q' : D.N) : G) * a : G ⧸ I) :=
      congrArg Subtype.val hqq
    rw [QuotientGroup.eq] at h1
    have h2 : a⁻¹ * (((Quotient.out q : D.N) : G)⁻¹ * (Quotient.out q' : D.N)) * a ∈ I := by
      have e : a⁻¹ * (((Quotient.out q : D.N) : G)⁻¹ * (Quotient.out q' : D.N)) * a =
          (((Quotient.out q : D.N) : G) * a)⁻¹ * (((Quotient.out q' : D.N) : G) * a) := by group
      rw [e]
      exact h1
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (heq _ _).mpr h2
  haveI := Fintype.ofFinite (↥D.N ⧸ (D.Nconj a).subgroupOf D.N)
  have hinj : Function.Injective (fun q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N => ((Quotient.out q : D.N) : G)) := by
    intro q q' h
    have h' : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', h']
  rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply,
    sum_reps F a hI hp hn
      (Finset.univ.image fun q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N => ((Quotient.out q : D.N) : G)) ?_ ?_ ρ v]
  · exact Finset.sum_image (f := fun u => ρ (u * a) v) (fun q _ q' _ h => hinj h)
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hu
    exact hNI _ (Quotient.out q).2
  · intro x hx0
    have hx := hND x hx0
    set q : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N := ((⟨x, hx⟩ : D.N) : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) with hqdef
    refine ⟨((Quotient.out q : D.N) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩, ?_⟩
    · have := (heq (Quotient.out q) ⟨x, hx⟩).mp (by rw [QuotientGroup.out_eq'])
      simpa using this
    · rintro y ⟨hy, hyI⟩
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy
      have h3 : (((Quotient.out q' : D.N)) : ↥D.N ⧸ (D.Nconj a).subgroupOf D.N) = q :=
        (heq (Quotient.out q') ⟨x, hx⟩).mpr hyI
      rw [QuotientGroup.out_eq'] at h3
      rw [h3]

end Gen

section Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def lf (V : Lev k) (n : ℕ) : LeviFact (V.J n) where
  Uf := unipB k (Fin n)
  Mf := (diagT k (Fin n)).range
  Lf := (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k)
  M_U := by
    rintro _ ⟨t, rfl⟩ u hu
    exact GlAx.conj_up t hu
  M_L := by
    rintro _ ⟨t, rfl⟩ l hl
    exact GlAx.conj_low t hl
  uniq := by
    rintro u hu _ ⟨t, rfl⟩ l hl h
    exact GlAx.uniq t hu hl h
  fact g hg := by
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 g hg
    exact ⟨a, ⟨ha.1, V.N_le ha⟩, diagT k (Fin n) s, ⟨⟨s, rfl⟩, V.dg_mem fun i => hs i trivial⟩, b,
      ⟨hb.1, V.Nm_le hb⟩, rfl⟩

private theorem low_mem (V : Lev k) {l : GL (Fin n) k}
    (h : l ∈ (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k)) (h' : l ∈ V.J n) : l ∈ (glIwa k n).Nm V.c := by
  obtain ⟨a, ha, _, ⟨s, _, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 _ h'
  have hy : b * (a * diagT k (Fin n) s * b)⁻¹ ∈ (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k) :=
    Subgroup.mul_mem _ hb.1 (Subgroup.inv_mem _ h)
  have key : a * diagT k (Fin n) s * (b * (a * diagT k (Fin n) s * b)⁻¹) = 1 := by group
  obtain ⟨rfl, hs1⟩ := GlAx.uniq s ha.1 hy key
  rw [hs1]
  simpa using hb

private theorem dom_anti {d : Fin n → kˣ} (hd : Dom d) : Antitone fun i => ord k (d i) := by
  intro i j hij
  have h := hd i j hij
  rw [val_ord, val_ord] at h
  have hs : StrictAnti fun m : ℤ => uniformizer k ^ m :=
    zpow_right_strictAnti₀ GlAx.unif_pos uniformizer_lt_one
  exact hs.le_iff_ge.mp h

private theorem pos (V : Lev k) {d : Fin n → kˣ} (hd : Dom d) : (lf V n).Pos (dg d) := by
  have ha : Antitone fun i => ord k (d i) := dom_anti hd
  refine ⟨⟨d, rfl⟩, ?_, ?_⟩
  · rintro u ⟨hu, hJ⟩
    have hN : u ∈ (glData k n).N := ⟨hu, V.J_le_KO hJ⟩
    exact V.N_le (GlAx.conj_N (t := d) (fun i => val_ord (d i)) ha hN)
  · rintro l ⟨hl, hJ⟩
    have hm : l ∈ (glData k n).Nm V.c := low_mem V hl hJ
    have hv : ∀ i, valuation k ↑((d⁻¹) i) = uniformizer k ^ (-ord k (d i)) := by
      intro i
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, val_ord, _root_.zpow_neg]
    have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + -ord k (d j) ≤ V.c + -ord k (d i) := by
      intro i j hji
      have := ha hji.le
      simp only at this
      omega
    have h2 := GlAx.conj_Nm hv hc hm
    have he : diagT k (Fin n) d⁻¹ * l * (diagT k (Fin n) d⁻¹)⁻¹ = (dg d)⁻¹ * l * dg d := by
      simp [dg, map_inv]
    rw [he] at h2
    exact V.Nm_le h2

private theorem normJ (V : Lev k) (d : Fin n → kˣ) : (lf V n).NormJ (dg d) := by
  rintro _ ⟨⟨t, rfl⟩, hj⟩
  have hc : dg d * diagT k (Fin n) t = diagT k (Fin n) t * dg d := by
    show diagT k (Fin n) d * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) d
    rw [← map_mul, ← map_mul, mul_comm]
  constructor
  · rw [hc, mul_inv_cancel_right]
    exact hj
  · rw [mul_assoc, ← hc, inv_mul_cancel_left]
    exact hj

end Lin

theorem UpperTheory.V.Z.Sym.Sig.hkMul :
    UpperTheory.V.Z.Sym.Sig.HkMul := by
  intro k _ _ _ _ V n M _ _ ρ
  have hJ : HeckePair (V.J n) := ((finFacts k V).2.2.2.2.2 n).1
  constructor
  · intro d d' hd hd'
    have h := (leviMul ℂ _ M ρ (V.J n) (lf V n) (dg d) (dg d') hJ (pos V hd) (pos V hd')
      (Or.inl (normJ V d))).2
    rw [h]
    congr 1
    exact (map_mul (diagT k (Fin n)) d d').symm
  · intro d hd v
    have hU : (lf V n).Uf ⊓ V.J n = (glIwa k n).N := by
      apply le_antisymm
      · rintro x ⟨hx, hxJ⟩
        exact ⟨hx, V.J_le_KO hxJ⟩
      · intro x hx
        exact ⟨(glIwa k n).N_le hx, V.N_le hx⟩
    exact hk_eq_uOp (glIwa k n) (lf V n) (dg d) hJ (pos V hd) (normJ V d) hU ρ v

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicator
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dc_mul (V : Lev k) {d : Fin 3 → kˣ} {u v g : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (h : g ∈ V.DC d) : u * g * v ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨u * a, (V.J 3).mul_mem hu ha, b * v, (V.J 3).mul_mem hb hv, by group⟩

private theorem dc_iff (V : Lev k) {d : Fin 3 → kˣ} {u v : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (g : GL (Fin 3) k) : u * g * v ∈ V.DC d ↔ g ∈ V.DC d := by
  constructor
  · intro h
    have h2 := dc_mul V ((V.J 3).inv_mem hu) ((V.J 3).inv_mem hv) h
    simpa [mul_assoc] using h2
  · exact dc_mul V hu hv

private theorem gl3_spherical_bi_invariant (V : Lev k) (d : Fin 3 → kˣ) {u u' : GL (Fin 3) k} (hu : u ∈ V.J 3) (hu' : u' ∈ V.J 3)
    (g : GL (Fin 3) k) : V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g := by
  have hF := thFacts k V
  have key : u * g * th k 3 u' * (Phi k)⁻¹ = u * (g * (Phi k)⁻¹) * th' k u' := by
    have h7 := hF.2.2.2.2.2.2 u'
    have : th k 3 u' = (Phi k)⁻¹ * th' k u' * Phi k := by
      rw [mul_assoc, h7]
      group
    rw [this]
    group
  simp only [Lev.unitaryDoubleCosetIndicator]
  rw [key, dc_iff V hu (hF.2.1 u' hu')]

private theorem gl3_spherical_finite_support (V : Lev k) (d : Fin 3 → kˣ) :
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.unitaryDoubleCosetIndicator d y.out ≠ 0}.Finite := by
  have hF := thFacts k V
  have hJ := (finFacts k V).2.2.2.2.2 3
  have horb : (MulAction.orbit (V.J 3) ((dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)).Finite := hJ.1 (dg d)
  let F : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) → GL (Fin 3) k ⧸ V.J 3 :=
    fun y => ((Quotient.out y * (Phi k)⁻¹ : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)
  refine Set.Finite.of_finite_image (f := F) (horb.subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_setOf_eq, Lev.unitaryDoubleCosetIndicator] at hy
    have hy' : Quotient.out y * (Phi k)⁻¹ ∈ V.DC d := by
      by_contra hc
      rw [if_neg hc] at hy
      exact hy rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = F y
    simp only [F]
    rw [hab, QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · intro y1 _ y2 _ h
    simp only [F] at h
    rw [QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' y1, ← QuotientGroup.out_eq' y2, QuotientGroup.eq]
    set w := Phi k * ((Quotient.out y1)⁻¹ * Quotient.out y2) * (Phi k)⁻¹ with hw
    refine ⟨th' k w, hF.2.1 w ?_, ?_⟩
    · convert h using 1
      rw [hw]
      group
    · have h7 := hF.2.2.2.2.2.2 (th' k w)
      rw [Pres.invol hF.1 w] at h7
      have : th k 3 (th' k w) = (Phi k)⁻¹ * (w * Phi k) := by
        rw [h7]
        group
      rw [this, hw]
      group

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.eqG :
    UpperTheory.V.Z.Sym.Sig.EqG := by
  intro k _ _ _ _ V ω Rs Ry x z d
  refine ⟨fun u hu u' hu' g => ⟨gl3_spherical_bi_invariant V d hu hu' g, ?_⟩, gl3_spherical_finite_support V d, ?_⟩
  · simp only [Lev.fG, gl3_spherical_bi_invariant V _ hu hu' g]
  · refine (Set.Finite.biUnion Rs.finite_toSet fun e _ =>
      Set.Finite.biUnion Ry.finite_toSet fun y _ => gl3_spherical_finite_support V ![x * e, y, z]).subset ?_
    intro q hq
    have hq' : ∑ e ∈ Rs, ∑ y ∈ Ry, (ω e : ℂ) * V.unitaryDoubleCosetIndicator ![x * e, y, z] q.out ≠ 0 := hq
    obtain ⟨e, he, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
    obtain ⟨y, hy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_biUnion he (Set.mem_biUnion hy (right_ne_zero_of_mul h))

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkS
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.okS : UpperTheory.V.Z.Sym.Sig.OkS := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht
  intro S
  classical
  obtain ⟨-, -, -, -, hdt, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨-, -, -, -, -, hJ⟩ := finFacts k V
  have key : ∀ y : ↥(DX Δ), S.fS t y ≠ 0 ↔ eD hs y ∈ V.DC ![t, t⁻¹] := by
    intro y
    show Glob.one (eD hs y ∈ V.DC ![t, t⁻¹]) ≠ 0 ↔ _
    unfold Glob.one
    split_ifs with h <;> simp [h]
  have dcL : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, a * g ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹] := by
    intro a ha g
    constructor
    · rintro ⟨a', ha', b, hb, e⟩
      refine ⟨a⁻¹ * a', mul_mem (inv_mem ha) ha', b, hb, ?_⟩
      calc g = a⁻¹ * (a * g) := by group
        _ = a⁻¹ * a' * dg ![t, t⁻¹] * b := by rw [e]; group
    · rintro ⟨a', ha', b, hb, e⟩
      exact ⟨a * a', mul_mem ha ha', b, hb, by rw [e]; group⟩
  have dcR : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, g * a ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹] := by
    intro a ha g
    constructor
    · rintro ⟨a', ha', b, hb, e⟩
      refine ⟨a', ha', b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
      calc g = (g * a) * a⁻¹ := by group
        _ = a' * dg ![t, t⁻¹] * (b * a⁻¹) := by rw [e]; group
    · rintro ⟨a', ha', b, hb, e⟩
      exact ⟨a', ha', b * a, mul_mem hb ha, by rw [e]; group⟩
  have fSdef : ∀ y : ↥(DX Δ), S.fS t y = Glob.one (eD hs y ∈ V.DC ![t, t⁻¹]) := fun y => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    rw [fSdef, fSdef, fSdef, map_mul, map_mul, dcL _ hu', dcR _ hu']
    exact ⟨rfl, rfl⟩
  · have horb := (hJ 2).1 (dg ![t, t⁻¹])
    refine Set.Finite.of_finite_image
      (f := fun x : ↥(SU Δ) ⧸ S.J2.subgroupOf (SU Δ) =>
        ((eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2))
      (horb.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, e⟩ := (key _).1 hx
      refine ⟨⟨a, ha⟩, ?_⟩
      dsimp only
      rw [e]
      show (a : GL (Fin 2) k) • ((dg ![t, t⁻¹] : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2) = _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hb
    · intro x _ y _ hxy
      have h1 : (eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)))⁻¹ * eD hs ((Quotient.out y : ↥(SU Δ)) : ↥(DX Δ)) ∈ V.J 2 :=
        QuotientGroup.eq.1 hxy
      rw [← map_inv, ← map_mul] at h1
      have h3 : (Quotient.out x)⁻¹ * Quotient.out y ∈ S.J2.subgroupOf (SU Δ) := h1
      rw [← Quotient.out_eq x, ← Quotient.out_eq y]
      exact QuotientGroup.eq.2 h3
  · rintro γ τ ⟨hdet, htr⟩ hne
    have hmem := (key γ).1 hne
    have hv1 : valuation k (t : k) < 1 := by
      have ht' : valuation k (t : k) < valuation k ((unif k : kˣ) : k) ^ 2 := ht
      refine ht'.trans_le ?_
      rw [GlAx.unif_spec]
      exact pow_le_one₀ zero_le' (ValuativeRel.uniformizer_lt_one (R := k)).le
    have hprod : valuation k ((t⁻¹ : kˣ) : k) * valuation k (t : k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hlt : valuation k (t : k) < valuation k ((t⁻¹ : kˣ) : k) := by
      refine lt_of_not_ge fun hle => ?_
      exact (mul_lt_of_le_one_of_lt (hle.trans hv1.le) hv1).ne hprod
    have hd : SDom ![t, t⁻¹] := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd hij (by decide)
      · exact hlt
      · exact absurd hij (by decide)
      · exact absurd hij (by decide)
    obtain ⟨j, -, w, hw, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) ![t, t⁻¹] hd _ hmem
    obtain ⟨d, hdmem, rfl⟩ := hw
    have hd0 : d 0 ∈ V.H := hdmem 0 (Set.mem_univ _)
    rw [MonoidHom.id_apply] at e
    have hc : ((j⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (j : Matrix (Fin 2) (Fin 2) k) =
        diagonal fun i => (((d * ![t, t⁻¹]) i : kˣ) : k) := by
      rw [← Units.val_mul, ← Units.val_mul, e]
      unfold dg
      rw [← map_mul, val_diagT]
    have hD := Matrix.det_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    have hT := Matrix.trace_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [hc] at hD hT
    have inj := (algebraMap k (Lsq k Δ)).injective
    have hdet1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 :=
      inj (by rw [← (hdt γ).1, hdet, map_one])
    have htr1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = τ :=
      inj (by rw [← (hdt γ).2, htr])
    rw [hdet1, Matrix.det_diagonal, Fin.prod_univ_two] at hD
    rw [htr1, Matrix.trace_diagonal, Fin.sum_univ_two] at hT
    simp only [Pi.mul_apply, Units.val_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hD hT
    have hinv : (t * d 0)⁻¹ = d 1 * t⁻¹ := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      simp only [Units.val_mul, Units.val_one]
      linear_combination hD
    refine ⟨d 0, hd0, ?_⟩
    rw [hinv, Units.val_mul, Units.val_mul, ← hT]
    ring

end
end
