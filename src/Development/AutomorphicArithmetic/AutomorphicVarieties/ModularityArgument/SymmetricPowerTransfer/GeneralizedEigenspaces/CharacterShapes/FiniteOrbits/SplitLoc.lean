module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.KO

private theorem coset_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (U W : Subgroup G) (hUW : U ≤ W) (ω : W →* ℂˣ) (f : G → ℂ) (a : G) (c : ℂ) (hc : c ≠ 0)
    (hf : ∀ (u : W) y, f (y * u) = ((ω u)⁻¹ : ℂˣ) * f y)
    (φ : G → V) (hφ : ∀ g (u : W), φ (g * u) = (ω u : ℂ) • φ g)
    (hval : ∀ y ∈ DC U a, f y = c)
    (hsupp : ∀ y, f y ≠ 0 → ∃ u ∈ W, y * u ∈ DC U a)
    (huniq : ∀ y ∈ DC U a, ∀ u ∈ W, y * u ∈ DC U a → u ∈ U) (h : G) :
    ∑ᶠ x : G ⧸ W, f x.out • φ (h * x.out) = c • ∑ᶠ (y : G ⧸ U) (_ : y.out ∈ DC U a), φ (h * y.out) := by
  have hinv : ∀ (y : G) (u : W), f (y * u) • φ (h * (y * u)) = f y • φ (h * y) := by
    intro y u
    rw [hf, ← mul_assoc, hφ, smul_smul, Units.val_inv_eq_inv_val]
    congr 1
    have := Units.ne_zero (ω u)
    field_simp
  have hne : ∀ (y : G) (u : W), f y ≠ 0 → f (y * u) ≠ 0 := fun y u hy => by
    rw [hf]
    exact mul_ne_zero (Units.ne_zero _) hy
  have hDC : ∀ y ∈ DC U a, ∀ w ∈ U, y * w ∈ DC U a := by
    rintro _ ⟨p, hp, q, hq, rfl⟩ w hw
    exact ⟨p, hp, q * w, mul_mem hq hw, by simp [mul_assoc]⟩
  have hout : ∀ y : G ⧸ U, y.out ∈ DC U a → f ((y.out : G ⧸ W)).out ≠ 0 := fun y hy => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul W y.out
    rw [hu]
    exact hne _ _ (by rw [hval _ hy]; exact hc)
  have hb : Set.BijOn (fun y : G ⧸ U => (y.out : G ⧸ W)) {y | y.out ∈ DC U a} {x | f x.out ≠ 0} := by
    refine ⟨fun y hy => hout y hy, fun y hy y' hy' e => ?_, fun x hx => ?_⟩
    · have e' : y.out⁻¹ * y'.out ∈ W := QuotientGroup.eq.1 e
      have := huniq _ hy _ e' (by simpa using hy')
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.2 this
    · obtain ⟨u, hu, hxu⟩ := hsupp _ hx
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul U (x.out * u)
      refine ⟨((x.out * u : G) : G ⧸ U), ?_, ?_⟩
      · change Quotient.out _ ∈ DC U a
        rw [hw]
        exact hDC _ hxu _ w.2
      · change ((Quotient.out ((x.out * u : G) : G ⧸ U) : G) : G ⧸ W) = x
        rw [hw, ← QuotientGroup.out_eq' x, QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem (mul_mem hu (hUW w.2))
  have h1 : ∑ᶠ x : G ⧸ W, f x.out • φ (h * x.out) = ∑ᶠ x ∈ {x : G ⧸ W | f x.out ≠ 0}, f x.out • φ (h * x.out) := by
    refine finsum_congr fun x => ?_
    rw [finsum_eq_if]
    split_ifs with hx
    · rfl
    · have : f x.out = 0 := by simpa using hx
      rw [this, zero_smul]
  have h2 : c • ∑ᶠ (y : G ⧸ U) (_ : y.out ∈ DC U a), φ (h * y.out) =
      ∑ᶠ y ∈ {y : G ⧸ U | y.out ∈ DC U a}, c • φ (h * y.out) := by
    rw [smul_finsum]
    refine finsum_congr fun y => ?_
    rw [smul_finsum]
    rfl
  rw [h1, h2]
  symm
  refine finsum_mem_eq_of_bijOn _ hb fun y hy => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul W y.out
  change c • φ (h * y.out) = f (Quotient.out ((y.out : G) : G ⧸ W)) • φ (h * Quotient.out ((y.out : G) : G ⧸ W))
  rw [hu, hinv, hval _ hy]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scalar_eq (n : ℕ) (z : kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) z : GL (Fin n) k) = dg (fun _ => z) := by
  apply Units.ext
  rw [val_diagT]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.scalar_apply]

private theorem gl_uniq (V : Lev k) (d : Fin 2 → kˣ) (hd : Dom d) {Y u : GL (Fin 2) k} (hY : Y ∈ V.DC d) (hYu : Y * u ∈ V.DC d)
    (z : kˣ) (j : GL (Fin 2) k) (hj : j ∈ V.J 2) (hu : u = Matrix.GeneralLinearGroup.scalar (Fin 2) z * j) : u ∈ V.J 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hY
  obtain ⟨p, hp, q, hq, e⟩ := hYu
  have hcomm : ∀ g : GL (Fin 2) k, g * dg (fun _ => z) = dg (fun _ => z) * g := fun g => by
    rw [← scalar_eq]
    apply Units.ext
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq.symm
  have h1 : dg (d * fun _ => z) ∈ V.DC d := by
    refine ⟨a⁻¹ * p, mul_mem (inv_mem ha) hp, q * j⁻¹ * b⁻¹, mul_mem (mul_mem hq (inv_mem hj)) (inv_mem hb), ?_⟩
    have : dg (d * fun _ => z) = a⁻¹ * (a * dg d * b * u) * j⁻¹ * b⁻¹ := by
      rw [hu, scalar_eq]
      simp only [dg, map_mul]
      have := hcomm b
      simp only [dg] at this
      rw [show a⁻¹ * (a * diagT k (Fin 2) d * b * ((diagT k (Fin 2) fun _ => z) * j)) * j⁻¹ * b⁻¹ = diagT k (Fin 2) d * (b * (diagT k (Fin 2) fun _ => z)) * b⁻¹ by group, this]
      group
    rw [this, e]
    group
  have h2 := (diagDC k V 2 d _ hd).1 h1 0
  have h3 : z ∈ V.H := by simpa using h2
  rw [hu, scalar_eq]
  refine mul_mem ?_ hj
  exact le_sup_left (b := (glIwa k 2).Nm V.c) (le_sup_right (a := (glIwa k 2).N) ⟨fun _ => z, fun i _ => h3, rfl⟩)

end Loc

section Loc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_lt (t : kˣ) (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact uniformizer_ne_zero hx.symm
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : valuation k (unif k : k) = uniformizer k := Classical.epsilon_spec hex
  have h1 : valuation k (unif k : k) ≤ 1 := by
    rw [hu]; exact uniformizer_lt_one.le
  exact lt_of_lt_of_le ht (pow_le_one' h1 2)

private theorem sdom {t : kˣ} (ht : valuation k (t : k) < 1) : SDom (![t, 1] : Fin 2 → kˣ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem dom_of {t : kˣ} (ht : valuation k (t : k) < 1) : Dom (![t, 1] : Fin 2 → kˣ) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (sdom ht i j h).le

private theorem kirillov_function_value_eq (V : Lev k) (χ : kˣ →* ℂˣ) (hχ : ∀ u ∈ V.H, χ u = 1) {t : kˣ} (ht : valuation k (t : k) < 1)
    {Y : GL (Fin 2) k} (hY : Y ∈ V.DC ![t, 1]) : V.twistedCentralTestFunction χ t Y = (((χ t)⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨-, -, hz⟩ := eqZ k V χ hχ 2 (by norm_num)
  have h := (hz _ (sdom ht)).1 1 Y hY
  rw [map_one, one_mul, map_one, inv_one, Units.val_one] at h
  rw [Lev.twistedCentralTestFunction, h, mul_one]

private theorem kirillov_function_support (V : Lev k) (χ : kˣ →* ℂˣ) {t : kˣ} {Y : GL (Fin 2) k} (hY : V.twistedCentralTestFunction χ t Y ≠ 0) :
    ∃ z : kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * Y ∈ V.DC ![t, 1] := by
  by_contra h
  apply hY
  rw [Lev.twistedCentralTestFunction, Lev.fZ, dif_neg h, mul_zero]

end Loc2

section Glb

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private theorem scal_one' {K : Type} [Field K] {Δ : K} : IsScal (1 : Kˣ) (1 : DX Δ) := by
  simp [IsScal, mt]

private theorem scal_comm' {K : Type} [Field K] {Δ : K} {z : Kˣ} {s : DX Δ} (h : IsScal z s) (y : DX Δ) : s * y = y * s := by
  apply Subtype.ext
  apply Units.ext
  change mt s * mt y = mt y * mt s
  rw [h]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

private theorem dat_S (v : Pl F) (h : v ∈ A.Sg) : A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) := dif_pos h

private theorem level_two_at_sigma (v : Pl F) (h : v ∈ A.Sg) : A.dat.J2v v = ((A.V v).J 2).comap (eD (A.hs v h)) := by
  have h' : v ∈ A.dat.Sg := h
  rw [Dat.J2v, if_pos h', dat_S A v h]
  rfl

private theorem level_two_outside_sigma (v : Pl F) (h : v ∉ A.Sg) : A.dat.J2v v = KD _ (Ov v) := if_neg h

private theorem fK_sig (t : Dat.Par F) (v : Pl F) (h : v ∈ A.Sg) (x : DX (cv v Δ)) :
    A.dat.fKv t v x = (A.V v).twistedCentralTestFunction (A.χ v) (t v) (eD (A.hs v h) x) := by
  have h' : v ∈ A.dat.Sg := h
  rw [Dat.fKv, if_pos h', dat_S A v h]
  rfl

private theorem fK_off (t : Dat.Par F) (v : Pl F) (h : v ∉ A.Sg) (x : DX (cv v Δ)) :
    A.dat.fKv t v x = fZD (Ov v) (A.χ v) x := if_neg h

variable {A}

private theorem bij_sig (hA : A.Ok) (v : Pl F) (h : v ∈ A.Sg) : Function.Bijective (eD (A.hs v h)) := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨h1, h2, h3, -⟩ := hl v h
  exact (eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v h) h3).1

private theorem dc_sig (hA : A.Ok) {g : DA Δ} {d : ParN F 2} (hg : A.IsElD g d) (v : Pl F) (h : v ∈ A.Sg) (y : DX (cv v Δ)) :
    y ∈ DC (A.dat.J2v v) (g.1 v) ↔ eD (A.hs v h) y ∈ (A.V v).DC (d v) := by
  rw [level_two_at_sigma A v h]
  constructor
  · rintro ⟨u, hu, u', hu', rfl⟩
    exact ⟨_, hu, _, hu', by rw [map_mul, map_mul, hg.1 v h]⟩
  · rintro ⟨a, ha, b, hb, e⟩
    obtain ⟨u, rfl⟩ := (bij_sig hA v h).2 a
    obtain ⟨u', rfl⟩ := (bij_sig hA v h).2 b
    exact ⟨u, ha, u', hb, (bij_sig hA v h).1 (by rw [e, map_mul, map_mul, hg.1 v h])⟩

private theorem dc_box (hA : A.Ok) {g : DA Δ} {d : ParN F 2} (hg : A.IsElD g d) (y : DA Δ) :
    y ∈ DC A.dat.U2 g ↔ (∀ v (h : v ∈ A.Sg), eD (A.hs v h) (y.1 v) ∈ (A.V v).DC (d v)) ∧ ∀ v ∉ A.Sg, y.1 v ∈ KD _ (Ov v) := by
  have h := (uFBox (Pl F) (DA Δ) (fun v => DX (cv v Δ)) (fun v => KD (cv v Δ) (Ov v)) A.dat.J2v (rpg _ _) A.Sg
    (fun v hv => level_two_outside_sigma A v hv) g (fun v hv => by
      change g.1 v ∈ _
      rw [hg.2 v hv]
      exact one_mem _)).1 y
  refine h.trans ⟨fun ⟨a, b⟩ => ⟨fun v hv => (dc_sig hA hg v hv _).1 (a v hv), fun v hv => ?_⟩,
    fun ⟨a, b⟩ => ⟨fun v hv => (dc_sig hA hg v hv _).2 (a v hv), fun v hv => ?_⟩⟩
  · have := b v hv
    rwa [level_two_outside_sigma A v hv] at this
  · rw [level_two_outside_sigma A v hv]
    exact b v hv

private theorem fk_one (hA : A.Ok) (t : Dat.Par F) (v : Pl F) (hv : v ∉ A.Sg) (x : DX (cv v Δ)) (hx : x ∈ KD _ (Ov v)) :
    A.dat.fKv t v x = 1 := by
  have := (Loc.fzdLaw (Ov v) (Kv v) (cv v Δ) (hA.off v hv) (A.χ v) (hA.chi v).1).2 1 1 x scal_one' hx
  rw [one_mul, map_one, inv_one, Units.val_one] at this
  rw [fK_off A t v hv, this]

private theorem fk_val (hA : A.Ok) {t : Dat.Par F} (ht : A.Cone t) {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : y ∈ DC A.dat.U2 g) : A.dat.FK t y = ∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨a, b⟩ := (dc_box hA hg y).1 hy
  rw [Dat.FK, finprod_eq_prod_of_mulSupport_subset (s := A.Sg)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨-, -, -, h4, -⟩ := hl v hv
    rw [fK_sig A t v hv]
    exact kirillov_function_value_eq _ _ (fun u hu => h4 u ((A.V v).H_le hu)) (val_lt _ (ht v hv)) (a v hv)
  · intro v hv
    by_contra h
    exact hv (fk_one hA t v h _ (b v h))

private theorem fk_supp (hA : A.Ok) {t : Dat.Par F} {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : A.dat.FK t y ≠ 0) : ∃ u ∈ A.dat.UZ, y * u ∈ DC A.dat.U2 g := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  have hco : ∀ᶠ v in Filter.cofinite, v ∉ A.Sg := Filter.eventually_cofinite.2 (by simpa using A.Sg.finite_toSet)
  have hyK : ∀ᶠ v in Filter.cofinite, y.1 v ∈ KD (cv v Δ) (Ov v) := (rpg _ _).ae y
  have hfin : (Function.mulSupport fun v => A.dat.fKv t v (y.1 v)).Finite := by
    refine (Filter.eventually_cofinite.1 (hco.and hyK)).subset fun v hv h => hv ?_
    exact fk_one hA t v h.1 _ h.2
  have hne : ∀ v, A.dat.fKv t v (y.1 v) ≠ 0 := fun v h => hy (finprod_eq_zero _ v h hfin)
  have hloc : ∀ v, ∃ (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s ∧
      (∀ h : v ∈ A.Sg, eD (A.hs v h) (s⁻¹ * y.1 v) ∈ (A.V v).DC ![t v, 1]) ∧ (v ∉ A.Sg → s⁻¹ * y.1 v ∈ KD _ (Ov v)) := by
    intro v
    by_cases hv : v ∈ A.Sg
    · have h0 := hne v
      rw [fK_sig A t v hv] at h0
      obtain ⟨z, hz⟩ := kirillov_function_support _ _ h0
      obtain ⟨h1, h2, h3, -⟩ := hl v hv
      obtain ⟨hb, -, -, hscal, -⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
      obtain ⟨s, hs⟩ := hb.2 (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
      exact ⟨z, s, (hscal z s).2 hs, fun _ => by rwa [map_mul, map_inv, hs], fun h => (h hv).elim⟩
    · have h0 := hne v
      rw [fK_off A t v hv] at h0
      have : ∃ (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s ∧ s⁻¹ * y.1 v ∈ KD _ (Ov v) := by
        by_contra hh
        exact h0 (dif_neg hh)
      obtain ⟨z, s, hs, hk⟩ := this
      exact ⟨z, s, hs, fun h => (hv h).elim, fun _ => hk⟩
  choose z s hs hS hO using hloc
  have hmem : ∀ᶠ v in Filter.cofinite, (s v)⁻¹ ∈ KD (cv v Δ) (Ov v) :=
    (hco.and hyK).mono fun v h => by simpa using mul_mem (hO v h.1) (inv_mem h.2)
  refine ⟨⟨fun v => (s v)⁻¹, hmem⟩, Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_left (inv_mem ⟨z v, Units.ext (hs v).symm⟩)), ?_⟩
  have hc : ∀ v, (y * ⟨fun v => (s v)⁻¹, hmem⟩ : DA Δ).1 v = (s v)⁻¹ * y.1 v := fun v => by
    change y.1 v * (s v)⁻¹ = _
    have := scal_comm' (hs v) (y.1 v)
    rw [eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, this, mul_inv_cancel_right]
  refine (dc_box hA hg _).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [hc]
    exact hS v hv
  · rw [hc]
    exact hO v hv

private theorem fk_uniq (hA : A.Ok) {t : Dat.Par F} (ht : A.Cone t) {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : y ∈ DC A.dat.U2 g) (u : DA Δ) (hu : u ∈ A.dat.UZ) (hyu : y * u ∈ DC A.dat.U2 g) : u ∈ A.dat.U2 := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨a, a'⟩ := (dc_box hA hg y).1 hy
  obtain ⟨b, b'⟩ := (dc_box hA hg _).1 hyu
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
  have huv : u.1 v ∈ ZD _ ⊔ A.dat.J2v v := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu v)
  change u.1 v ∈ A.dat.J2v v
  by_cases hv : v ∈ A.Sg
  · rw [level_two_at_sigma A v hv] at huv ⊢
    obtain ⟨h1, h2, h3, h4, -⟩ := hl v hv
    obtain ⟨-, -, -, -, -, hZJ⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
    rw [← hZJ] at huv
    obtain ⟨-, hm, -⟩ := eqZ _ (A.V v) (A.χ v) (fun u hu => h4 u ((A.V v).H_le hu)) 2 (by norm_num)
    obtain ⟨z, j, hj, e⟩ := (hm _).1 huv
    have hb := b v hv
    have hbb : eD (A.hs v hv) (y.1 v) * eD (A.hs v hv) (u.1 v) ∈ (A.V v).DC ![t v, 1] := by
      rw [← map_mul]
      exact hb
    exact gl_uniq _ _ (dom_of (val_lt _ (ht v hv))) (a v hv) hbb z j hj e
  · rw [level_two_outside_sigma A v hv]
    exact (mul_mem_cancel_left (a' v hv)).1 (b' v hv)

end Glb

end UpperTheory.V.Z.Sym.So.KO

open UpperTheory.V.Z.Sym.So.KO in
theorem UpperTheory.V.Z.Sym.So.kOps :
    UpperTheory.V.Z.Sym.So.KOps := by
  intro F _ _ Δ A hA V _ _ ch B hB
  obtain ⟨hOk, hCone, hl, -, -⟩ := datOk F Δ A hA
  have hle : A.dat.U2 ≤ B.U := fun u hu => by
    rw [hB.U]
    exact Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_iInf.1 hu v))
  have hinv : ∀ φ ∈ B.Forms, ∀ u ∈ A.dat.U2, ∀ g, φ (g * u) = φ g := by
    intro φ hφ u hu g
    have h1 := hφ.2 g ⟨u, hle hu⟩
    have h2 := hB.ω ⟨u, hle hu⟩ (fun _ => 1) (fun _ => 1) fun v =>
      ⟨scal_one', by
        have h0 : u.1 v ∈ A.dat.J2v v := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu v)
        simpa using h0⟩
    simp only [map_one, Units.val_one, finprod_one] at h2
    rw [h2, one_smul] at h1
    exact h1
  refine ⟨fun t g ht hg φ => ?_, hinv, fun φ hφ z s hs g => ?_⟩
  · have ht' : A.dat.Cone t := (hCone t).2 ht
    have htest := finK_test F Δ A.dat hOk V ch B hB t ht'
    rw [Tf.rSpec _ _ _ B (Base.Tw.one B) _ htest φ]
    funext h
    have hdc := (dcBasic (DA Δ) V A.dat.U2 g (dMul F Δ A hA g _ hg).1 φ.1 (hinv φ.1 φ.2)).2.1 h
    rw [Pi.smul_apply, hdc]
    refine coset_sum A.dat.U2 B.U hle B.ω (A.dat.FK t) g _ (Finset.prod_ne_zero_iff.2 fun v _ => Units.ne_zero _)
      (fun u y => htest.right u y) φ.1 (fun g u => φ.2.2 g u) (fk_val hA ht hg) (fun y hy => ?_) (fun y hy u hu hyu => ?_) h
    · obtain ⟨u, hu, e⟩ := fk_supp hA hg y hy
      exact ⟨u, hB.U ▸ hu, e⟩
    · exact fk_uniq hA ht hg y hy u (hB.U ▸ hu) hyu
  · classical
    let z' : Dat.Par F := fun v => if v ∈ A.Sg then z v else 1
    have hsc : ∀ v, IsScal (z' v) (s.1 v) := fun v => by
      by_cases hv : v ∈ A.Sg
      · obtain ⟨h1, h2, h3, -⟩ := hl v hv
        obtain ⟨-, -, -, hscal, -⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
        have hz : z' v = z v := if_pos hv
        rw [hz, hscal, hs.1 v hv, scalar_eq]
        congr 1
        funext i
        fin_cases i <;> rfl
      · have hz : z' v = 1 := if_neg hv
        rw [hz, hs.2 v hv]
        exact scal_one'
    have hsU : s ∈ B.U := by
      rw [hB.U]
      exact Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨z' v, Units.ext (hsc v).symm⟩)
    have h1 := hφ.2 g ⟨s, hsU⟩
    have h2 := hB.ω ⟨s, hsU⟩ z' (fun v => s.1 v) fun v => ⟨hsc v, by simp⟩
    have h3 : (∏ᶠ v, (A.dat.χ v (z' v) : ℂ)) = ∏ v ∈ A.Sg, (A.χ v (z v) : ℂ) := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := A.Sg)]
      · refine Finset.prod_congr rfl fun v hv => ?_
        have hz : z' v = z v := if_pos hv
        rw [hz]
        rfl
      · intro v hv
        by_contra h
        have hz : z' v = 1 := if_neg h
        exact hv (by
          change ((A.dat.χ v (z' v) : ℂˣ) : ℂ) = 1
          rw [hz]
          simp)
    rw [h2, h3] at h1
    exact h1

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SplitLoc
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem split_loc (O : Type) [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k}
    (hs : s * s = Δ) (hs0 : s ≠ 0) (x : DX Δ) (hx : x ∈ KD Δ O) :
    ∃ t ∈ SU Δ, eD hs (t⁻¹ * x) ∈ (Lev.iw k).J 2 := by
  obtain ⟨hbij, hKO, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hxK : eD hs x ∈ KO k (Fin 2) := by
    have hx' : x ∈ Subgroup.comap (eD hs) (KO k (Fin 2)) := by
      rw [hKO]
      exact hx
    exact hx'
  let d : Fin 2 → kˣ := ![Matrix.GeneralLinearGroup.det (eD hs x), 1]
  have hd : Matrix.GeneralLinearGroup.det (dg d) = Matrix.GeneralLinearGroup.det (eD hs x) := by
    apply Units.ext
    simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two, d]
  obtain ⟨t, ht⟩ := hbij.2 (eD hs x * (dg d)⁻¹)
  refine ⟨t, ?_, ?_⟩
  · rw [SU, MonoidHom.mem_ker]
    apply Units.ext
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [show (↑(↑t : GL (Fin 2) (Lsq k Δ)) : Matrix (Fin 2) (Fin 2) (Lsq k Δ)) = Glob.mt t from rfl, (hdet t).1, ht,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hd, mul_inv_cancel, Units.val_one, map_one]
  · rw [map_mul, map_inv, ht, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    apply Lev.dg_mem
    intro i
    fin_cases i
    · show valuation k (↑(Matrix.GeneralLinearGroup.det (eD hs x)) : k) = 1
      exact GlobalTheory.StepData.valuation_det_of_mem_KO hxK
    · exact one_mem _

end

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') (x : DX Δ) :
    eD h x = eD h' x := by
  subst e
  rfl

theorem UpperTheory.V.Z.Sym.So.kNon :
    UpperTheory.V.Z.Sym.So.KNon := by
  intro F _ _ Δ A hA A₀ hA₀ hE V _ _ ch C hC Y hY hoff φ hφ hφ0
  classical
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨-, -, -, -, hU2₀⟩ := datOk F Δ A₀ hA₀
  have hinv := (kOps F Δ A hA V ch C hC).2.1 φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hY.2 g
  have hu₀ := (hU2₀ u).1 hu
  have hspl : ∀ v (h : v ∈ A.Sg ∧ v ∉ A₀.Sg), ∃ r ∈ SU ((cv v) Δ),
      eD (A.hs v h.1) (r⁻¹ * u.1 v) ∈ (Lev.iw (Kv v)).J 2 := fun v h =>
    split_loc (Ov v) (hloc v h.1).1 (hloc v h.1).2.1 (A.hs v h.1) (hloc v h.1).2.2.1 (u.1 v) (hu₀.2 v h.2)
  let tf : (v : Pl F) → ↥(DX ((cv v) Δ)) := fun v =>
    if h : v ∈ A.Sg ∧ v ∉ A₀.Sg then (hspl v h).choose else 1
  have htf : tf ∈ RP (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, tf v ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.eventually_cofinite.mpr (A.Sg.finite_toSet.subset ?_)
    intro v hv
    by_contra h
    apply hv
    have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h' => h h'.1
    simp only [tf, dif_neg hn]
    exact one_mem _
  let t : DA Δ := ⟨tf, htf⟩
  have hcomm : t * y = y * t := by
    apply Subtype.ext
    funext v
    show tf v * y.1 v = y.1 v * tf v
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · rw [hoff y hy v h.1]
      simp
    · simp only [tf, dif_neg h]
      simp
  have htS : t ∈ SA Δ := by
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show tf v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · simp only [tf, dif_pos h]
      exact (hspl v h).choose_spec.1
    · simp only [tf, dif_neg h]
      exact one_mem _
  have hj : t⁻¹ * u ∈ A.dat.U2 := by
    refine (hU2 _).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show eD (A.hs v hv) ((tf v)⁻¹ * u.1 v) ∈ (A.V v).J 2
      by_cases h0 : v ∈ A₀.Sg
      · have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => h.2 h0
        simp only [tf, dif_neg hn, inv_one, one_mul]
        rw [eD_congr (A.hs v hv) (A₀.hs v h0) (hE.s v h0), hE.V v h0]
        exact hu₀.1 v h0
      · have hp : v ∈ A.Sg ∧ v ∉ A₀.Sg := ⟨hv, h0⟩
        simp only [tf, dif_pos hp]
        rw [hE.iw v hv h0]
        exact (hspl v hp).choose_spec.2
    · show (tf v)⁻¹ * u.1 v ∈ KD ((cv v) Δ) (Ov v)
      have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => hv h.1
      simp only [tf, dif_neg hn, inv_one, one_mul]
      exact hu₀.2 v (fun h0 => hv (hE.sub h0))
  refine ⟨y, hy, ⟨s * t, mul_mem hs htS⟩, ?_⟩
  intro h0
  apply hg
  have hsy : s * y * u = s * t * y * (t⁻¹ * u) := by
    calc s * y * u = s * (y * t) * (t⁻¹ * u) := by group
      _ = s * (t * y) * (t⁻¹ * u) := by rw [← hcomm]
      _ = s * t * y * (t⁻¹ * u) := by group
  rw [show C.ι γ * s * y * u = C.ι γ * (s * y * u) by group, hφ.1 γ (s * y * u), hsy, hinv _ hj]
  rw [show φ (s * t * y) = 0 from h0, map_zero]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SaNormal
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem dc_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal) (a : S) (y : G)
    (hy : y * (a : G) = a * y) (hfin : AlgebraTools.FinOrb U U (a : G))
    (hc : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (g : S) :
    dcF ((U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S) a (fun h : S => φ (h * y)) g = dcF U (a : G) φ (g * y) := by
  classical
  have hmem : ∀ u : G, u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom ↔ y⁻¹ * u * y ∈ U := by
    intro u
    simp [MulAut.conj_apply]
  have hea : (MulAut.conj y⁻¹).toMonoidHom (a : G) = a := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hy, inv_mul_cancel_left]
  have hbij : Function.Bijective (MulAut.conj y⁻¹).toMonoidHom := (MulAut.conj y⁻¹).bijective
  have hM := dcMap G G V (MulAut.conj y⁻¹).toMonoidHom hbij U (a : G) (a : G)
  rw [hea] at hM
  obtain ⟨-, hfinIff, -, hmap⟩ := hM
  have hfin' := hfinIff.2 hfin
  have hφy : ∀ u ∈ U, ∀ x : G, φ (y * (x * u)) = φ (y * x) := by
    intro u hu x
    rw [← mul_assoc]
    exact hφ u hu _
  have htr : ∀ z : G, dcF U (a : G) (fun x => φ (y * x)) z = dcF U (a : G) φ (y * z) := by
    intro z
    rw [(dcBasic G V U a hfin (fun x => φ (y * x)) hφy).2.1, (dcBasic G V U a hfin φ hφ).2.1]
    simp only [mul_assoc]
  have hA : ∀ x : G, dcF (U.comap (MulAut.conj y⁻¹).toMonoidHom) (a : G) (fun h => φ (h * y)) x
      = dcF U (a : G) φ (x * y) := by
    intro x
    have h1 := congrFun (hmap hfin (fun x => φ (y * x)) hφy) x
    have h2 : ((fun x => φ (y * x)) ∘ (MulAut.conj y⁻¹).toMonoidHom) = fun h => φ (h * y) := by
      funext h
      simp [MulAut.conj_apply, mul_assoc]
    rw [h2] at h1
    rw [h1]
    simp only [Function.comp_apply]
    rw [htr]
    simp [MulAut.conj_apply, mul_assoc]
  have hay : (a : G) * y⁻¹ = y⁻¹ * a := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]
  have hc' : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∃ c ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom,
      c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S := by
    intro u hu
    obtain ⟨c, hcU, hca, h1, h2⟩ := hc _ ((hmem u).1 hu)
    refine ⟨y * c * y⁻¹, (hmem _).2 (by simpa [mul_assoc] using hcU), ?_, ?_, ?_⟩
    · calc y * c * y⁻¹ * (a : G) = y * c * (a * y⁻¹) := by rw [hay, mul_assoc]
        _ = y * (c * a) * y⁻¹ := by simp only [mul_assoc]
        _ = y * a * c * y⁻¹ := by rw [hca]; simp only [mul_assoc]
        _ = (a : G) * (y * c * y⁻¹) := by rw [hy]; simp only [mul_assoc]
    · have := hS.conj_mem _ h1 y
      simpa [mul_assoc] using this
    · have := hS.conj_mem _ h2 y
      simpa [mul_assoc] using this
  have hψG : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∀ x : G, φ (x * u * y) = φ (x * y) := by
    intro u hu x
    have := hφ _ ((hmem u).1 hu) (x * y)
    simpa [mul_assoc] using this
  obtain ⟨hfS, hDC, -, R, hR1, hR2, hR3⟩ := dcSub G V S _ a hfin' hc' hS
  have hψS : ∀ u ∈ (U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S, ∀ x : S,
      φ (((x * u : S) : G) * y) = φ ((x : G) * y) := by
    intro u hu x
    rw [Subgroup.mem_subgroupOf] at hu
    simpa using hψG _ hu x
  rw [(dcBasic S V _ a hfS (fun h : S => φ (h * y)) hψS).2.2.2.2 R hR1 hR2 g, ← hA]
  rw [(dcBasic G V _ (a : G) hfin' (fun h => φ (h * y)) hψG).2.2.2.2 (R.map (Function.Embedding.subtype _)) ?_ ?_ g]
  · rw [Finset.sum_map]
    simp
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hz
    exact (hDC r).1 (hR1 r hr)
  · intro z hz
    obtain ⟨r, ⟨hr, hrz⟩, huniq⟩ := hR3 z hz
    refine ⟨(r : G), ⟨Finset.mem_map_of_mem _ hr, hrz⟩, ?_⟩
    rintro w ⟨hw, hwz⟩
    obtain ⟨r', hr', rfl⟩ := Finset.mem_map.1 hw
    exact congrArg Subtype.val (huniq r' ⟨hr', hwz⟩)

private theorem sa_normal {F : Type} [Field F] [NumberField F] (Δ : F) : (SA Δ).Normal := by
  unfold SA
  refine Subgroup.normal_iInf_normal fun v => ?_
  have hN : (SU ((cv v) Δ)).Normal := by
    unfold SU
    exact MonoidHom.normal_ker _
  exact hN.comap _

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kRes :
    UpperTheory.V.Z.Sym.So.KRes := by
  intro F _ _ Δ A hA V _ _ ch C hC y hy φ hφ a ha
  have hK := kOps F Δ A hA V ch C hC
  have hφU : ∀ u ∈ A.dat.U2, ∀ g : DA Δ, φ (g * u) = φ g := hK.2.1 φ hφ
  constructor
  · intro γ g g' hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [hg, mul_assoc]
    exact hφ.1 (γ : DX Δ) _
  · intro u hu g
    unfold SD.lvS at hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hu
    have := hφU _ hu ((g : DA Δ) * y)
    simpa [mul_assoc] using this
  · intro t g hdom hel
    have hyc : y * (g : DA Δ) = (g : DA Δ) * y := by
      apply Subtype.ext
      funext v
      by_cases hv : v ∈ A.Sg
      · have h1 := hy v hv
        simp [h1]
      · have h1 := hel.2 v hv
        simp [h1]
    have hfin := (dMul F Δ A hA (g : DA Δ) (SD.dS t) hel).1
    have hc : ∀ u ∈ A.dat.U2, ∃ c ∈ A.dat.U2, c * (g : DA Δ) = g * c ∧ u * c⁻¹ ∈ SA Δ ∧ c⁻¹ * u ∈ SA Δ := by
      intro u hu
      obtain ⟨c, hcU, h1, h2, h3⟩ := torPart F Δ A hA u hu
      exact ⟨c, hcU, h3 _ _ hel, h1, h2⟩
    funext h
    rw [Pi.smul_apply]
    unfold SD.lvS
    rw [dc_conj (SA Δ) A.dat.U2 (sa_normal Δ) g y hyc hfin hc φ hφU h, ha t g hdom hel]
    rfl

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DiagonalParameterDominant
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Scalar

variable {k : Type} [Field k]

private theorem dg_comm (z : kˣ) (x : GL (Fin 2) k) : dg ![z, z] * x = x * dg ![z, z] := by
  have h : (fun i => ((![z, z] i : kˣ) : k)) = fun _ => (z : k) := by
    funext i
    fin_cases i <;> rfl
  apply Units.ext
  simp only [Units.val_mul, val_diagT, h]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end Scalar

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private abbrev d1 (t : Dat.Par F) : ParN F 2 := fun v => ![t v, 1]

private theorem diagonal_parameter_mul (t t' : Dat.Par F) : d1 (t * t') = d1 t * d1 t' := by
  funext v i
  fin_cases i <;> simp [d1]

private theorem diagonal_parameter_dominant {t : Dat.Par F} (h : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1) : A.DomS (d1 t) := by
  intro v hv i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · simpa using h v hv
  · exact absurd hij (by decide)
  · exact le_rfl

private theorem cone_le {t : Dat.Par F} (h : A.Cone t) : ∀ v ∈ A.Sg, valuation (Kv v) (t v : Kv v) ≤ 1 := by
  intro v hv
  refine (h v hv).le.trans (pow_le_one₀ zero_le' ?_)
  rw [GlAx.unif_spec]
  exact uniformizer_lt_one.le

private theorem cone_mul {x y : Dat.Par F} (hx : ∀ v ∈ A.Sg, valuation (Kv v) (x v : Kv v) ≤ 1) (hy : A.Cone y) :
    A.Cone (x * y) := by
  intro v hv
  have h : valuation (Kv v) ((x * y) v : Kv v) = valuation (Kv v) (x v : Kv v) * valuation (Kv v) (y v : Kv v) := by
    rw [Pi.mul_apply, Units.val_mul, map_mul]
  rw [h]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hx v hv)) (hy v hv)

private def cc (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ)

private def pp (a : Chs F) (t : Dat.Par F) : ℂ := ∏ v ∈ A.Sg, ((a v (t v) : ℂˣ) : ℂ)

private theorem cc_mul (t t' : Dat.Par F) : cc A (t * t') = cc A t * cc A t' := by
  simp only [cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, mul_inv, Units.val_mul]

private theorem pp_mul (a : Chs F) (t t' : Dat.Par F) : pp A a (t * t') = pp A a t * pp A a t' := by
  simp only [pp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.mul_apply, map_mul, Units.val_mul]

private theorem cc_ne (t : Dat.Par F) : cc A t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_ne (a : Chs F) (t : Dat.Par F) : pp A a t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

private theorem pp_sq (a : Chs F) (t : Dat.Par F) : pp A (a ^ 2) t = pp A a (t * t) := by
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.pow_apply, MonoidHom.pow_apply, Pi.mul_apply, map_mul, pow_two]

private theorem exS_eq (hA : A.Ok) (a : Chs F) (t : Dat.Par F) : A.exS a t = pp A a t * cc A t := by
  simp only [SD.exS, pp, cc, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hχ : A.χ v = absPow (Kv v) 1 := ((datOk F Δ A hA).2.2.1 v hv).2.2.2.2
  have h := (expoEq (Kv v) (a v)).2.1 (t v)
  rw [SD.dS, h, hχ, absPow_neg, MonoidHom.inv_apply]

private theorem conj_mem (hA : A.Ok) {s u : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (hu : u ∈ A.dat.U2) : s⁻¹ * u * s ∈ A.dat.U2 := by
  have hU := (datOk F Δ A hA).2.2.2.2
  rw [hU] at hu ⊢
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    have e' : eD (A.hs v h) (s.1 v) = dg ![z v, z v] := hs.1 v h
    rw [e, map_mul, map_mul, map_inv, e', mul_assoc, ← dg_comm, inv_mul_cancel_left]
    exact hu.1 v h
  · have e : (s⁻¹ * u * s).1 v = (s.1 v)⁻¹ * u.1 v * s.1 v := rfl
    rw [e, hs.2 v h]
    simpa using hu.2 v h

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem dc_smul {G : Type} [Group G] (U : Subgroup G) (a : G) (c : ℂ) (φ : G → V) :
    dcF U a (c • φ) = c • dcF U a φ :=
  map_smul (dc (rightReg ℂ G V) U U a) c φ

private theorem mulOp (hA : A.Ok) {g g' : DA Δ} {d d' : ParN F 2} (hg : A.IsElD g d) (hg' : A.IsElD g' d')
    (hd : A.DomS d) (hd' : A.DomS d') (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) :
    dcF A.dat.U2 (g * g') φ = dcF A.dat.U2 g (dcF A.dat.U2 g' φ) := by
  have hm := (elEx F Δ A hA).2.2.2.1 g g' d d' hg hg'
  exact (uFMul _ V _ g g' (dMul F Δ A hA g d hg).1 (dMul F Δ A hA g' d' hg').1 (dMul F Δ A hA _ _ hm).1
    ((dMul F Δ A hA g d hg).2 g' d' hg' hd hd') φ hφ).symm

private theorem dcScal (hA : A.Ok) {s : DA Δ} {z : Dat.Par F} (hs : A.IsElD s fun v => ![z v, z v])
    (φ : DA Δ → V) (hφ : ∀ u ∈ A.dat.U2, ∀ x, φ (x * u) = φ x) (x : DA Δ) :
    dcF A.dat.U2 s φ x = φ (x * s) := by
  have h1 : ∀ y ∈ ({s} : Finset (DA Δ)), y ∈ DC A.dat.U2 s := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  have h2 : ∀ y ∈ DC A.dat.U2 s, ∃! r, r ∈ ({s} : Finset (DA Δ)) ∧ r⁻¹ * y ∈ A.dat.U2 := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    refine ⟨s, ⟨Finset.mem_singleton_self _, ?_⟩, fun r hr => Finset.mem_singleton.1 hr.1⟩
    have e : s⁻¹ * (u * s * u') = (s⁻¹ * u * s) * u' := by group
    rw [e]
    exact mul_mem (conj_mem A hA hs hu) hu'
  have h := (dcBasic _ V A.dat.U2 s (dMul F Δ A hA s _ hs).1 φ hφ).2.2.2.2 {s} h1 h2 x
  simpa using h

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kSpec :
    UpperTheory.V.Z.Sym.So.KSpec := by
  intro F _ _ Δ A hA V _ _ ch B hB
  obtain ⟨hop, hinv, hsc⟩ := kOps F Δ A hA V ch B hB
  have hexD := (elEx F Δ A hA).2.1
  have hmulD := (elEx F Δ A hA).2.2.2.1
  refine ⟨?_, ?_⟩
  · intro t t' ht ht'
    refine LinearMap.ext fun φ => Subtype.ext ?_
    obtain ⟨g, hg, -⟩ := hexD (d1 t)
    obtain ⟨g', hg', -⟩ := hexD (d1 t')
    have hgg : A.IsElD (g * g') (d1 (t * t')) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg hg'
    have e1 := hop (t * t') (g * g') (cone_mul A (cone_le A ht) ht') hgg φ
    have e2 := hop t g ht hg ((Base.Tw.one B).R (A.dat.FK t') φ)
    have e3 := hop t' g' ht' hg' φ
    rw [Module.End.mul_apply, e1, e2, e3, dc_smul, smul_smul,
      mulOp A hA hg hg' (diagonal_parameter_dominant A (cone_le A ht)) (diagonal_parameter_dominant A (cone_le A ht')) φ.1 (hinv φ.1 φ.2)]
    have := cc_mul A t t'
    simp only [cc] at this
    rw [this]
  · intro a φ hE t g hd hg
    have hφ := hinv φ.1 φ.2
    have hT : ∀ τ h, A.Cone τ → A.IsElD h (d1 τ) → dcF A.dat.U2 h φ.1 = pp A a τ • φ.1 := by
      intro τ h hτ hh
      have h1 := congrArg Subtype.val (hE τ hτ)
      rw [hop τ h hτ hh φ, Submodule.coe_smul, exS_eq A hA, mul_comm, ← smul_smul] at h1
      exact smul_right_injective _ (cc_ne A τ) h1
    have ht2 : ∀ v ∈ A.Sg, valuation (Kv v) ((t * t) v : Kv v) ≤ 1 := by
      intro v hv
      have h0 : valuation (Kv v) (t v : Kv v) ≤ valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) := by
        simpa [SD.dS] using hd v hv 0 1 (by decide)
      have h1 := mul_le_mul' h0 (le_refl (valuation (Kv v) (t v : Kv v)))
      have e : valuation (Kv v) (((t v)⁻¹ : (Kv v)ˣ) : Kv v) * valuation (Kv v) (t v : Kv v) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [e, ← map_mul] at h1
      rw [Pi.mul_apply, Units.val_mul]
      exact h1
    let t0 : Dat.Par F := fun v => unif (Kv v) ^ 3
    have h0 : A.Cone t0 := by
      intro v hv
      show valuation (Kv v) ((unif (Kv v) ^ 3 : (Kv v)ˣ) : Kv v) < _
      rw [Units.val_pow_eq_pow_val, map_pow, GlAx.unif_spec]
      exact pow_lt_pow_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one (by norm_num)
    obtain ⟨g0, hg0, -⟩ := hexD (d1 t0)
    obtain ⟨g1, hg1, -⟩ := hexD (d1 (t * t))
    have hgg : A.IsElD (g1 * g0) (d1 (t * t * t0)) := by
      rw [diagonal_parameter_mul]
      exact hmulD _ _ _ _ hg1 hg0
    have hg1φ : dcF A.dat.U2 g1 φ.1 = pp A a (t * t) • φ.1 := by
      have e := hT _ _ (cone_mul A ht2 h0) hgg
      rw [mulOp A hA hg1 hg0 (diagonal_parameter_dominant A ht2) (diagonal_parameter_dominant A (cone_le A h0)) φ.1 hφ, hT _ _ h0 hg0, dc_smul, pp_mul,
        mul_comm, ← smul_smul] at e
      exact smul_right_injective _ (pp_ne A a t0) e
    obtain ⟨s, hs, -⟩ := hexD fun v => ![t⁻¹ v, t⁻¹ v]
    have hm : A.IsElD (g1 * s) (SD.dS t) := by
      have e : SD.dS t = d1 (t * t) * fun v => ![t⁻¹ v, t⁻¹ v] := by
        funext v i
        fin_cases i <;> simp [SD.dS]
      rw [e]
      exact hmulD _ _ _ _ hg1 hs
    have hgs : g = g1 * s := (hexD (SD.dS t)).unique hg hm
    have hdom : A.DomS fun v => ![t⁻¹ v, t⁻¹ v] := by
      intro v _ i j _
      fin_cases i <;> fin_cases j <;> exact le_rfl
    have hsφ : dcF A.dat.U2 s φ.1 = cc A t • φ.1 := by
      funext x
      rw [dcScal A hA hs φ.1 hφ x, hsc φ.1 φ.2 _ s hs x, Pi.smul_apply]
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Pi.inv_apply, map_inv]
    rw [hgs, mulOp A hA hg1 hs (diagonal_parameter_dominant A ht2) hdom φ.1 hφ, hsφ, dc_smul, hg1φ, smul_smul, exS_eq A hA, pp_sq,
      mul_comm]

end
end
