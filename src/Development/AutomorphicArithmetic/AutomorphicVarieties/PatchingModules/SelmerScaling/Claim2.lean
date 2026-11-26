module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefULift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUPush
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RelSub
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {X : Type} [CommRing X] {a g : ℕ} {c : Fin a → Fin g → X}

private theorem rel_C (r : X) : DD.Rel c (DD.C r) (DD.C r) :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_zero : DD.Rel c 0 0 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_one : DD.Rel c 1 1 :=
  ⟨rfl, rfl, fun k => by simp, fun j => by simp⟩

private theorem rel_add {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u + u') (v + v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], by simp [a2, b2], fun k => ?_, fun j => ?_⟩
  · simp [a3, b3, mul_add, Finset.sum_add_distrib]
  · simp [a4, b4, mul_add, Finset.sum_add_distrib]

private theorem rel_neg {u : DD X a} {v : DD X g} (h : DD.Rel c u v) : DD.Rel c (-u) (-v) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨by simp [a1], by simp [a2], fun k => ?_, fun j => ?_⟩
  · simp [a3]
  · simp [a4]

private theorem rel_pair {p q : Fin a → X} {s t : Fin g → X} (h : ∀ k, p k = ∑ j, c k j * s j)
    (h' : ∀ j, t j = ∑ k, c k j * q k) : ∑ k, p k * q k = ∑ j, s j * t j := by
  simp only [h, h', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem rel_mul {u u' : DD X a} {v v' : DD X g} (h : DD.Rel c u v) (h' : DD.Rel c u' v') :
    DD.Rel c (u * u') (v * v') := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨by simp [a1, b1], ?_, fun k => ?_, fun j => ?_⟩
  · have e1 := rel_pair a3 b4
    have e2 := rel_pair b3 a4
    have e3 : ∑ k, u.ep' k * u'.ep k = ∑ j, v.ep' j * v'.ep j := by
      simpa only [mul_comm] using e2
    simp only [DD.mul_eta, Finset.sum_add_distrib, e1, e3, a1, a2, b1, b2]
  · simp only [DD.mul_ep, a3, b3, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [DD.mul_ep', a4, b4, a1, b1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

private theorem rel_sum {ι : Type} (s : Finset ι) (f : ι → DD X a) (f' : ι → DD X g)
    (h : ∀ i, DD.Rel c (f i) (f' i)) : DD.Rel c (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact rel_add (h i) ih

end

theorem UpperTheory.V.Pa.relSub :
    ∀ (X : Type) [CommRing X] (a g : ℕ) (c : Fin a → Fin g → X), (∀ r : X, DD.Rel c (DD.C r) (DD.C r)) ∧ (∀ u v u' v', DD.Rel c u v → DD.Rel c u' v' → DD.Rel c (u + u') (v + v') ∧ DD.Rel c (u - u') (v - v') ∧ DD.Rel c (u * u') (v * v')) ∧ (∀ u v v', DD.Rel c u v → DD.Rel c u v' → v.ep = v'.ep → v = v') ∧ ∀ (n : ℕ) (l : List (Matrix (Fin n) (Fin n) (DD X a) × Matrix (Fin n) (Fin n) (DD X g))), (∀ p ∈ l, ∀ i j, DD.Rel c (p.1 i j) (p.2 i j)) → ∀ i j, DD.Rel c ((l.map Prod.fst).prod i j) ((l.map Prod.snd).prod i j) := by
  intro X _ a g c
  refine ⟨rel_C, fun u v u' v' h h' => ⟨rel_add h h', ?_, rel_mul h h'⟩, ?_, ?_⟩
  · rw [sub_eq_add_neg, sub_eq_add_neg]
    exact rel_add h (rel_neg h')
  · rintro u v v' ⟨a1, a2, -, a4⟩ ⟨b1, b2, -, b4⟩ e
    exact DD.ext (a1.symm.trans b1) e (funext fun j => (a4 j).trans (b4 j).symm) (a2.symm.trans b2)
  · intro n l
    induction l with
    | nil =>
      intro _ i j
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact rel_one
      · exact rel_zero
    | cons p l ih =>
      intro h i j
      simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
      exact rel_sum _ _ _ fun k => rel_mul (h p (List.mem_cons_self ..) i k)
        (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) k j)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Gen
variable {X : Type} [CommRing X] {e g n : ℕ}

private def TT (X : Type) [CommRing X] (g : ℕ) : DD X g →+* DD X g where
  toFun u := ⟨u.a, u.ep, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def PP (c : Fin e → Fin g → X) (u : DD X e) (w : DD X g) : DD X g :=
  ⟨u.a, w.ep, fun j => ∑ k, c k j * u.ep' k, u.eta⟩

private def RM (c : Fin e → Fin g → X) (U : Matrix (Fin n) (Fin n) (DD X e)) (V : Matrix (Fin n) (Fin n) (DD X g)) : Prop :=
  ∀ i j, DD.Rel c (U i j) (V i j)

variable {c : Fin e → Fin g → X}

private theorem RM_uniq {U : Matrix (Fin n) (Fin n) (DD X e)} {V V' : Matrix (Fin n) (Fin n) (DD X g)}
    (h : RM c U V) (h' : RM c U V') (hT : (TT X g).mapMatrix V = (TT X g).mapMatrix V') : V = V' := by
  ext1 i j
  exact (relSub X e g c).2.2.1 _ _ _ (h i j) (h' i j) (congrArg (fun M => (M i j).ep) hT)

private theorem RM_mul {U U' : Matrix (Fin n) (Fin n) (DD X e)} {V V' : Matrix (Fin n) (Fin n) (DD X g)}
    (h : RM c U V) (h' : RM c U' V') : RM c (U * U') (V * V') := by
  have := (relSub X e g c).2.2.2 n [(U, V), (U', V')] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [h, h'])
  simpa [RM] using this

private theorem RM_zero : RM c (0 : Matrix (Fin n) (Fin n) (DD X e)) 0 := by
  intro i j
  have := (relSub X e g c).1 0
  simpa using this

private theorem RM_smul {u : DD X e} {v : DD X g} (h : DD.Rel c u v) :
    RM c (u • (1 : Matrix (Fin n) (Fin n) (DD X e))) (v • 1) := by
  intro i j
  by_cases hij : i = j
  · subst hij; simpa using h
  · simpa [hij] using RM_zero (c := c) i j

private theorem RM_one : RM c (1 : Matrix (Fin n) (Fin n) (DD X e)) 1 := by
  have := RM_smul (n := n) ((relSub X e g c).1 1)
  simpa using this

private theorem RM_prod {U : Fin n → Matrix (Fin n) (Fin n) (DD X e)} {V : Fin n → Matrix (Fin n) (Fin n) (DD X g)}
    (h : ∀ k, RM c (U k) (V k)) : RM c (List.ofFn U).prod (List.ofFn V).prod := by
  have := (relSub X e g c).2.2.2 n (List.ofFn fun k => (U k, V k)) (by
    intro p hp
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact h k)
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this

private theorem conj_prod {R : Type} [CommRing R] (w wi : Matrix (Fin n) (Fin n) R) (hw : w * wi = 1) (hw' : wi * w = 1)
    (M : Fin n → Matrix (Fin n) (Fin n) R)
    (d : Fin n → R) (h1 : ∀ k i j, j < i → (wi * M k * w) i j = 0) (h2 : ∀ k, (wi * M k * w) k k = d k) :
    (List.ofFn fun k => M k - d k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  have h0 := tri_prod_zero (fun k => wi * M k * w - d k • 1)
    (fun k i j hij => by
      rw [Matrix.sub_apply, h1 k i j hij, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', smul_zero, sub_zero])
    (fun k => by rw [Matrix.sub_apply, h2 k, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self])
  have e1 : ∀ Z, wi * (w * Z) = Z := fun Z => by rw [← mul_assoc, hw', one_mul]
  have e2 : ∀ Z, w * (wi * Z) = Z := fun Z => by rw [← mul_assoc, hw, one_mul]
  let φ : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun Z => w * Z * wi
      map_one' := by rw [mul_one, hw]
      map_mul' := fun Y Z => by simp only [mul_assoc, e1] }
  have h3 := congrArg φ h0
  rw [map_list_prod, List.map_ofFn] at h3
  have h4 : φ 0 = 0 := by simp [φ]
  rw [h4] at h3
  rw [← h3]
  congr 2
  funext k
  change _ = w * (_ - _) * wi
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hw]
  simp only [mul_assoc, e2, hw, mul_one]

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (DD.aug X g) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (AddMonoidHom.mk' (fun u : DD X g => u.ep j) fun _ _ => rfl) f s

private theorem eps_mul (Z : Fin g → Matrix (Fin n) (Fin n) X) (M : Matrix (Fin n) (Fin n) X) :
    (∀ i j, (((1 + DD.epM Z) * M.map DD.C : Matrix (Fin n) (Fin n) (DD X g)) i j).a = M i j) ∧
      ∀ k i j, (((1 + DD.epM Z) * M.map DD.C : Matrix (Fin n) (Fin n) (DD X g)) i j).ep k = (Z k * M) i j := by
  rw [add_mul, one_mul]
  refine ⟨fun i j => ?_, fun k i j => ?_⟩
  · simp [Matrix.mul_apply, sum_a, DD.epM]
  · simp [Matrix.mul_apply, sum_ep, DD.epM]

private noncomputable def pushU {H : Type} [Group H] (c : Fin e → Fin g → X) (ψ : H →* (DD X e)ˣ)
    (hψ : ∀ t, (ψ t : DD X e).ep = 0) : H →* (DD X g)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun t => PP c (ψ t) 0
      map_one' := by
        rw [map_one]; ext <;> simp [PP]
      map_mul' := fun s t => by
        rw [map_mul]
        ext <;> simp [PP, hψ, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm] }

private theorem pushU_val {H : Type} [Group H] (c : Fin e → Fin g → X) (ψ : H →* (DD X e)ˣ)
    (hψ : ∀ t, (ψ t : DD X e).ep = 0) (t : H) : (pushU c ψ hψ t : DD X g) = PP c (ψ t) 0 := rfl

end Gen

theorem UpperTheory.V.Pa.defUPush :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (e : ℕ) (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) (c : Fin e → Fin k.g → x.Fr), DefU h x u ψ → (∀ a, epC h x u a = ∑ j, c a j • kapF h k j) → ∃ (u' : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g)) (ψ' : ∀ v, Fin n → L.Gv v →* (DD x.Fr k.g)ˣ), DefU h x u' ψ' ∧ (∀ j, epC h x u' j = kapF h k j) ∧ ∀ j, epC' h x u' j = ∑ a, c a j • epC' h x u a := by
  intro l _ L G G0 h n x k e u ψ c hu hc
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := rho1Tri l L G G0 h n x k x.Fr
  obtain ⟨-, -, p3, p4, p5, p6⟩ := homBasic l L G G0 h
  obtain ⟨b1, -, b3⟩ := bndRho l L G G0 h n x k
  obtain ⟨o1, o2, o3, -⟩ := bndOps x.K G.G₀
  have hρmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := fun g g' => by
    simp [NP.ρX, mat, Matrix.map_mul]
  have hρ1 : x.ρX x.Fr 1 = 1 := by simp [NP.ρX, mat]
  have hinv : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := fun γ => by
    rw [← hρmul, ← map_mul, inv_mul_cancel, map_one, hρ1]
  have hinv' : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ) * x.ρX x.Fr (h.p₀ γ⁻¹) = 1 := fun γ => by
    rw [← hρmul, ← map_mul, mul_inv_cancel, map_one, hρ1]
  have ha : ∀ γ : G.G₀, (∀ i j, (k.ρ1 x.Fr (h.p₀ γ) i j).a = x.ρX x.Fr (h.p₀ γ) i j) ∧
      ∀ m i j, (k.ρ1 x.Fr (h.p₀ γ) i j).ep m = (kapF h k m γ * x.ρX x.Fr (h.p₀ γ)) i j := fun γ =>
    eps_mul (fun m => kapF h k m γ) (x.ρX x.Fr (h.p₀ γ))
  have hE : ∀ γ a i j, (u γ i j).ep a = ∑ m, c a m * (k.ρ1 x.Fr (h.p₀ γ) i j).ep m := by
    intro γ a i j
    have h1 : (u γ).map (fun z => z.ep a) = (∑ m, c a m • kapF h k m γ) * x.ρX x.Fr (h.p₀ γ) := by
      have h2 := congrFun (hc a) γ
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply] at h2
      rw [← h2, epC, mul_assoc, hinv, mul_one]
    have h3 := congrFun (congrFun h1 i) j
    rw [Finset.sum_mul, Matrix.sum_apply, Matrix.map_apply] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(ha γ).2, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
  have hψ0 : ∀ v i t, (ψ v i t : DD x.Fr e).ep = 0 := fun v i t => (hu.ψ_even v i t).2.1 rfl
  obtain ⟨u', hu'⟩ : ∃ u' : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g),
      ∀ γ i j, u' γ i j = PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j) :=
    ⟨fun γ => Matrix.of fun i j => PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j), fun _ _ _ => rfl⟩
  have hR : ∀ γ, RM c (u γ) (u' γ) := fun γ i j => by
    rw [hu']
    exact ⟨rfl, rfl, fun a => hE γ a i j, fun _ => rfl⟩
  have hT : ∀ γ, (TT x.Fr k.g).mapMatrix (u' γ) = (TT x.Fr k.g).mapMatrix (k.ρ1 x.Fr (h.p₀ γ)) := fun γ => by
    ext1 i j
    change TT _ _ (u' γ i j) = TT _ _ (k.ρ1 x.Fr (h.p₀ γ) i j)
    rw [hu']
    refine DD.ext ?_ rfl rfl rfl
    exact (congrFun (congrFun (hu.red γ) i) j).trans ((ha γ).1 i j).symm
  have hRψ : ∀ v i t, DD.Rel c (ψ v i t : DD x.Fr e) (pushU c (ψ v i) (hψ0 v i) t : DD x.Fr k.g) := fun v i t => by
    rw [pushU_val]
    exact ⟨rfl, rfl, fun a => by simp [PP, hψ0], fun _ => rfl⟩
  refine ⟨u', fun v i => pushU c (ψ v i) (hψ0 v i), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine RM_uniq (hR 1) (hu.one ▸ RM_one) ?_
    rw [hT, map_one h.p₀, r2]
  · intro γ γ'
    refine RM_uniq (hR _) (hu.mul γ γ' ▸ RM_mul (hR γ) (hR γ')) ?_
    rw [map_mul, hT, hT, hT, map_mul h.p₀, r1, map_mul]
  · intro γ
    rw [← hu.red γ]
    ext i j
    simp only [Matrix.map_apply, hu']
    rfl
  · intro γ i j
    rw [hu']
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · obtain ⟨-, -, -, a4⟩ := (hu.even γ i j).1 hij
      obtain ⟨-, a2, -, -⟩ := (r5 (h.p₀ γ) i j).1 hij
      exact ⟨nofun, fun _ => a2 rfl, nofun, fun _ => a4 rfl⟩
    · obtain ⟨a1, -, a3, -⟩ := (hu.even γ i j).2 hij
      refine ⟨fun _ => a1 rfl, nofun, fun _ => ?_, nofun⟩
      funext m
      simp [PP, a3 rfl]
  · intro γ
    have h1 : RM c ((u γ)ᵀ * u (G.frame.conj γ)) ((u' γ)ᵀ * u' (G.frame.conj γ)) :=
      RM_mul (fun i j => hR γ j i) (hR _)
    rw [hu.form] at h1
    refine RM_uniq h1 (RM_smul ((relSub x.Fr e k.g c).1 _)) ?_
    have h2 : (TT x.Fr k.g).mapMatrix (u' γ)ᵀ = (TT x.Fr k.g).mapMatrix (k.ρ1 x.Fr (h.p₀ γ))ᵀ :=
      congrArg Matrix.transpose (hT γ)
    rw [map_mul, h2, hT, ← map_mul, p3, r3, p6]
  · intro w γ hγ
    refine RM_uniq (hR γ) ((hu.ine w γ hγ).symm ▸ RM_one) ?_
    rw [hT, r4 w _ (p5 w γ hγ)]
  · intro v i t
    exact hu.ψ_red v i t
  · intro v i t
    rw [pushU_val]
    exact ⟨nofun, fun _ => rfl, nofun, fun _ => (hu.ψ_even v i t).2.2.2 rfl⟩
  · intro v i t ht
    ext1
    rw [pushU_val, hu.ψ_mu v i t ht]
    ext <;> simp [PP]
  · intro v t
    have h1 := RM_prod (c := c) (U := fun i => u (G.φ v (t i)) - algebraMap _ _ (ψ v i (t i) : DD x.Fr e))
      (V := fun i => u' (G.φ v (t i)) - algebraMap _ _ (pushU c (ψ v i) (hψ0 v i) (t i) : DD x.Fr k.g)) (fun m i j => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        exact ((relSub x.Fr e k.g c).2.1 _ _ _ _ (hR _ i j) (RM_smul (hRψ v m (t m)) i j)).2.1)
    rw [hu.ord] at h1
    refine RM_uniq h1 RM_zero ?_
    obtain ⟨w1, w2, w3⟩ := r6 v
    rw [← conj_prod _ _ w1 w2 (fun m => k.ρ1 x.Fr (G0.φ v (t m))) (fun m => algebraMap x.A _ (x.ψ v m (t m) : x.A))
      (fun m => (w3 (t m)).1) (fun m => (w3 (t m)).2 m), map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext m
    dsimp only [Function.comp_apply]
    rw [map_sub, map_sub, hT, p4, Algebra.algebraMap_eq_smul_one]
    congr 1
    ext1 i j
    change TT _ _ (_ * _) = TT _ _ (_ * _)
    rw [map_mul, map_mul]
    congr 1
    exact DD.ext (hu.ψ_red v m (t m)) rfl rfl rfl
  · intro i j
    obtain ⟨a1, -, a3, a4⟩ := hu.bnd i j
    simp only [hu']
    refine ⟨a1, fun m => ?_, fun m => ?_, a4⟩
    · have : (fun γ => (PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j)).ep m) =
          fun γ => ∑ s, kapF h k m γ i s * x.ρX x.Fr (h.p₀ γ) s j := funext fun γ => (ha γ).2 m i j
      rw [this]
      exact o3 _ _ _ fun s _ => (o2 _ _ (b3 m i s) (b1 s j)).2.1
    · exact o3 _ Finset.univ (fun a γ => c a m * (u γ i j).ep' a) fun a _ => (o2 _ _ (o1 _) (a3 a)).2.1
  · intro m
    funext γ
    have : (u' γ).map (fun z => z.ep m) = kapF h k m γ * x.ρX x.Fr (h.p₀ γ) := by
      ext i j
      rw [Matrix.map_apply, hu']
      exact (ha γ).2 m i j
    rw [epC, this, mul_assoc, hinv', mul_one]
  · intro m
    funext γ
    have : (u' γ).map (fun z => z.ep' m) = ∑ a, c a m • (u γ).map (fun z => z.ep' a) := by
      ext i j
      rw [Matrix.map_apply, hu', Matrix.sum_apply]
      rfl
    rw [epC', this, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PhDecDApply
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private noncomputable def UpperTheory.V.Pa.phDecD {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) : S.Bh →+ S.F where
  toFun b := Φ (b • y) - S.rF b * Φ y
  map_zero' := by simp
  map_add' b b' := by rw [add_smul, map_add (f := _), map_add (f := _)]; ring

private theorem UpperTheory.V.Pa.phDecD_apply {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) (b : S.Bh) :
    phDecD S Φ y b = Φ (b • y) - S.rF b * Φ y := rfl

private theorem UpperTheory.V.Pa.phDecD_mem {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (hΦ : Φ ∈ S.Ph)
    (y : S.U.N) : phDecD S Φ y ∈ S.Tp := by
  obtain ⟨h1, h2⟩ := hΦ
  have hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0 := fun q hq => by
    rw [← S.rF_ker] at hq; exact hq
  have dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q := by
    intro b
    obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
    refine ⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]
    simp
  refine ⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩
  · obtain ⟨o, q, hq, rfl⟩ := dec b
    obtain ⟨o', q', hq', rfl⟩ := dec b'
    have hqq : q * q' ∈ S.J2 := by
      refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hq hq'
    have e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y =
        algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) +
          algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    simp only [phDecD_apply]
    rw [e]
    simp only [add_smul, map_add (f := _), map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']
    ring
  · rw [phDecD_apply, h1, sub_self]
  · have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
      refine Ideal.span_le.2 ?_
      rintro a ⟨x, hx, z, hz, e⟩
      obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx z hz
      have : a = c := S.U.inj (e.symm.trans e')
      rw [this]
      exact hc
    rw [phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b (hi hb)]
    simp

private theorem UpperTheory.V.Pa.phDec_expand {F A : Type} [Field F] [AddCommGroup A] (T : Submodule F (A →+ F)) {e : ℕ}
    (v : Module.Basis (Fin e) F T) (d : T) (b : A) :
    (d : A →+ F) b = ∑ k, (v k : A →+ F) b * v.coord k d := by
  let ev : T →ₗ[F] F :=
    { toFun := fun α => (α : A →+ F) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev d = ∑ k, ev (v k) * v.coord k d
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← v.sum_repr d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]

theorem UpperTheory.V.Pa.phDec :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Φ ∈ S.Ph, ∃ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) ∧ (∀ k, μ k ∈ S.La) ∧ ∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y := by
  intro l _ S Φ hΦ
  have : Module.Finite S.F S.Tp := (tpDual l S).1
  let v := Module.finBasis S.F S.Tp
  let D : S.U.N →+ S.Tp :=
    { toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩
      map_zero' := by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp [phDecD_apply]
      map_add' := fun y y' => by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add (f := _)]
        ring }
  have hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y := fun _ _ => rfl
  have hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y := by
    intro c y
    refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
    have := (D y).2.1 b c
    rw [hD, hD, hD, map_mul] at this
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]
    linear_combination this
  refine ⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_,
    fun b y => ?_⟩
  · change v.coord k (D (c • y)) = S.rF c * v.coord k (D y)
    rw [hs, map_smul, smul_eq_mul]
  · have := phDec_expand S.Tp v (D y) b
    rw [hD] at this
    change Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)
    rw [← this]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUConj
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section Comp

variable {X : Type} [CommRing X] {e n : ℕ}

private theorem dd_a_add (x y : DD X e) : (x + y).a = x.a + y.a := rfl

private theorem ep_component_add (x y : DD X e) : (x + y).ep = x.ep + y.ep := rfl

private theorem dd_ep'_add (x y : DD X e) : (x + y).ep' = x.ep' + y.ep' := rfl

private theorem dd_eta_add (x y : DD X e) : (x + y).eta = x.eta + y.eta := rfl

private theorem dd_a_zero : (0 : DD X e).a = 0 := rfl

private theorem dd_ep_zero : (0 : DD X e).ep = 0 := rfl

private theorem dd_ep'_zero : (0 : DD X e).ep' = 0 := rfl

private theorem dd_eta_zero : (0 : DD X e).eta = 0 := rfl

private theorem dd_a_one : (1 : DD X e).a = 1 := rfl

private theorem dd_ep_one : (1 : DD X e).ep = 0 := rfl

private theorem dd_ep'_one : (1 : DD X e).ep' = 0 := rfl

private theorem dd_eta_one : (1 : DD X e).eta = 0 := rfl

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X e) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X e) (k : Fin e) :
    (∑ i ∈ s, f i).ep k = ∑ i ∈ s, (f i).ep k := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X e) (k : Fin e) :
    (∑ i ∈ s, f i).ep' k = ∑ i ∈ s, (f i).ep' k := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X e) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  rfl

private theorem mmul_a (M N : Matrix (Fin n) (Fin n) (DD X e)) :
    (M * N).map (fun a => a.a) = M.map (fun a => a.a) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_a]

private theorem mmul_ep (M N : Matrix (Fin n) (Fin n) (DD X e)) (k : Fin e) :
    (M * N).map (fun a => a.ep k) =
      M.map (fun a => a.a) * N.map (fun a => a.ep k) + M.map (fun a => a.ep k) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_ep, Finset.sum_add_distrib]

private theorem mmul_ep' (M N : Matrix (Fin n) (Fin n) (DD X e)) (k : Fin e) :
    (M * N).map (fun a => a.ep' k) =
      M.map (fun a => a.a) * N.map (fun a => a.ep' k) + M.map (fun a => a.ep' k) * N.map (fun a => a.a) := by
  ext i j
  simp [Matrix.mul_apply, sum_ep', Finset.sum_add_distrib]

private theorem P_a (Y : Fin e → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Y).map (fun a => a.a) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, dd_a_add, dd_a_one]
  · simp [Matrix.one_apply, DD.epM, hij, dd_a_add, dd_a_zero]

private theorem P_ep (Y : Fin e → Matrix (Fin n) (Fin n) X) (k : Fin e) :
    (1 + DD.epM Y).map (fun a => a.ep k) = Y k := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, ep_component_add, dd_ep_one]
  · simp [Matrix.one_apply, DD.epM, hij, ep_component_add, dd_ep_zero]

private theorem P_ep' (Y : Fin e → Matrix (Fin n) (Fin n) X) (k : Fin e) :
    (1 + DD.epM Y).map (fun a => a.ep' k) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, DD.epM, dd_ep'_add, dd_ep'_one]
  · simp [Matrix.one_apply, DD.epM, hij, dd_ep'_add, dd_ep'_zero]

private theorem epM_mul (Y Z : Fin e → Matrix (Fin n) (Fin n) X) : DD.epM Y * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  apply DD.ext
  · simp [DD.mul_a, DD.epM, dd_a_zero]
  · funext m
    simp [DD.mul_ep, DD.epM, dd_ep_zero]
  · funext m
    simp [DD.mul_ep', DD.epM, dd_ep'_zero]
  · simp [DD.mul_eta, DD.epM, dd_eta_zero]

private theorem epM_add (Y Z : Fin e → Matrix (Fin n) (Fin n) X) : DD.epM Y + DD.epM Z = DD.epM (Y + Z) := by
  ext i j <;> simp [DD.epM]

private theorem epM_zero : DD.epM (0 : Fin e → Matrix (Fin n) (Fin n) X) = 0 := by
  ext i j <;> rfl

private theorem twoPow_mul_twoPow (Y Z : Fin e → Matrix (Fin n) (Fin n) X) (h : Y + Z = 0) :
    (1 + DD.epM Y) * (1 + DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_add, mul_one, epM_mul, add_zero, add_assoc, add_comm (DD.epM Z),
    epM_add, h, epM_zero, add_zero]

private theorem P_tr (Y Z : Fin e → Matrix (Fin n) (Fin n) X) (h : ∀ k, (Y k)ᵀ = Z k) :
    (1 + DD.epM Y)ᵀ = 1 + DD.epM Z := by
  rw [transpose_add, transpose_one]
  congr 1
  ext i j <;> simp [DD.epM, ← h]

private theorem conj_prod {R : Type} [Ring R] (P Q : R) (h1 : P * Q = 1) (h2 : Q * P = 1) (s : List R) :
    (s.map fun a => P * a * Q).prod = P * s.prod * Q := by
  induction s with
  | nil => simp [h1]
  | cons a s ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h2, one_mul]

variable {A : Type} [CommRing A] [Algebra A X]

private theorem mem_ev (x : DD X e) : x ∈ ddPart A X e true false true false ↔ x.ep = 0 ∧ x.eta = 0 := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  simp

private theorem mem_od (x : DD X e) : x ∈ ddPart A X e false true false true ↔ x.a = 0 ∧ x.ep' = 0 := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  simp

private theorem ep_eta_mul_eq_zero_of_ep_eta_eq_zero (x y : DD X e) (hx : x.ep = 0 ∧ x.eta = 0) (hy : y.ep = 0 ∧ y.eta = 0) :
    (x * y).ep = 0 ∧ (x * y).eta = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · funext j
    simp [DD.mul_ep, hx1, hy1]
  · simp [DD.mul_eta, hx1, hx2, hy1, hy2]

private theorem ep_eta_mul_eq_zero_of_a_ep'_eq_zero (x y : DD X e) (hx : x.a = 0 ∧ x.ep' = 0) (hy : y.a = 0 ∧ y.ep' = 0) :
    (x * y).ep = 0 ∧ (x * y).eta = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · funext j
    simp [DD.mul_ep, hx1, hy1]
  · simp [DD.mul_eta, hx1, hx2, hy1, hy2]

private theorem a_ep'_mul_eq_zero_of_ep_eta_zero_of_a_ep'_zero (x y : DD X e) (hx : x.ep = 0 ∧ x.eta = 0) (hy : y.a = 0 ∧ y.ep' = 0) :
    (x * y).a = 0 ∧ (x * y).ep' = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · simp [DD.mul_a, hy1]
  · funext j
    simp [DD.mul_ep', hx1, hy1, hy2]

private theorem a_ep'_mul_eq_zero_of_a_ep'_zero_of_ep_eta_zero (x y : DD X e) (hx : x.a = 0 ∧ x.ep' = 0) (hy : y.ep = 0 ∧ y.eta = 0) :
    (x * y).a = 0 ∧ (x * y).ep' = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · simp [DD.mul_a, hx1]
  · funext j
    simp [DD.mul_ep', hx1, hx2]

private theorem even_mul (a : ℕ) (M N : Matrix (Fin n) (Fin n) (DD X e))
    (hM : M ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true))
    (hN : N ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true)) :
    M * N ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true) := by
  have hM' : ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e true false true false) ∧
        (¬(↑i < a ↔ ↑j < a) → M i j ∈ ddPart A X e false true false true) := hM
  have hN' : ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e true false true false) ∧
        (¬(↑i < a ↔ ↑j < a) → N i j ∈ ddPart A X e false true false true) := hN
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mem_ev]
    by_cases hik : (↑i < a ↔ ↑k < a)
    · have h1 := (hM' i k).1 hik
      have h2 := (hN' k j).1 (hik.symm.trans hij)
      rw [mem_ev] at h1 h2
      exact ep_eta_mul_eq_zero_of_ep_eta_eq_zero _ _ h1 h2
    · have h1 := (hM' i k).2 hik
      have h2 := (hN' k j).2 (fun hkj => hik (hij.trans hkj.symm))
      rw [mem_od] at h1 h2
      exact ep_eta_mul_eq_zero_of_a_ep'_eq_zero _ _ h1 h2
  · intro hij
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mem_od]
    by_cases hik : (↑i < a ↔ ↑k < a)
    · have h1 := (hM' i k).1 hik
      have h2 := (hN' k j).2 (fun hkj => hij (hik.trans hkj))
      rw [mem_ev] at h1
      rw [mem_od] at h2
      exact a_ep'_mul_eq_zero_of_ep_eta_zero_of_a_ep'_zero _ _ h1 h2
    · have h1 := (hM' i k).2 hik
      have h2 := (hN' k j).1 (by tauto)
      rw [mem_od] at h1
      rw [mem_ev] at h2
      exact a_ep'_mul_eq_zero_of_a_ep'_zero_of_ep_eta_zero _ _ h1 h2

private theorem even_P (a : ℕ) (Y : Fin e → Matrix (Fin n) (Fin n) X) (hY : ∀ k, Y k ∈ Od A X n a) :
    1 + DD.epM Y ∈ blkMat n a (ddPart A X e true false true false) (ddPart A X e false true false true) := by
  have hYk : ∀ k, ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → Y k i j ∈ (⊥ : Submodule A X)) ∧
        (¬(↑i < a ↔ ↑j < a) → Y k i j ∈ (⊤ : Submodule A X)) := hY
  intro i j
  constructor
  · intro hij
    rw [mem_ev]
    have h0 : ∀ k, Y k i j = 0 := fun k => (Submodule.mem_bot A).1 ((hYk k i j).1 hij)
    constructor
    · funext k
      by_cases hij' : i = j
      · subst hij'
        simp [Matrix.one_apply, DD.epM, h0, ep_component_add, dd_ep_one]
      · simp [Matrix.one_apply, DD.epM, hij', h0, ep_component_add, dd_ep_zero]
    · by_cases hij' : i = j
      · subst hij'
        simp [Matrix.one_apply, DD.epM, dd_eta_add, dd_eta_one]
      · simp [Matrix.one_apply, DD.epM, hij', dd_eta_add, dd_eta_zero]
  · intro hij
    rw [mem_od]
    have hne : i ≠ j := fun h => hij (h ▸ Iff.rfl)
    constructor
    · simp [Matrix.one_apply, DD.epM, hne, dd_a_add, dd_a_zero]
    · funext k
      simp [Matrix.one_apply, DD.epM, hne, dd_ep'_add, dd_ep'_zero]

end Comp

section Bnd

variable {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {n e : ℕ}

private theorem bnd_const (M : Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) :
    BndD (PowerSeries.X : PowerSeries K) fun _ : G => M := by
  intro i j
  obtain ⟨hc, -⟩ := bndOps K G
  exact ⟨hc _, fun _ => hc _, fun _ => hc _, hc _⟩

private theorem bnd_mul (M N : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e))
    (hM : BndD (PowerSeries.X : PowerSeries K) M) (hN : BndD (PowerSeries.X : PowerSeries K) N) :
    BndD (PowerSeries.X : PowerSeries K) fun g => M g * N g := by
  obtain ⟨-, hops, hsum, -, -⟩ := bndOps K G
  have hadd : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g :=
    fun φ ψ hφ hψ => (hops φ ψ hφ hψ).1
  have hmul : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g :=
    fun φ ψ hφ hψ => (hops φ ψ hφ hψ).2.1
  intro i j
  refine ⟨?_, fun m => ?_, fun m => ?_, ?_⟩
  · have hf : (fun g => (((fun g => M g * N g) g) i j).a) =
        fun g => ∑ k ∈ Finset.univ, (M g i k).a * (N g k j).a := by
      funext g
      simp only [Matrix.mul_apply, sum_a, DD.mul_a]
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).a)
      (fun k _ => hmul _ _ (hM i k).1 (hN k j).1)
  · have hf : (fun g => (((fun g => M g * N g) g) i j).ep m) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a) := by
      funext g
      simp only [Matrix.mul_apply, sum_ep, DD.mul_ep]
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep m + (M g i k).ep m * (N g k j).a)
      (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.1 m)) (hmul _ _ ((hM i k).2.1 m) (hN k j).1))
  · have hf : (fun g => (((fun g => M g * N g) g) i j).ep' m) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a) := by
      funext g
      simp only [Matrix.mul_apply, sum_ep', DD.mul_ep']
    rw [hf]
    exact hsum (Fin n) Finset.univ (fun k g => (M g i k).a * (N g k j).ep' m + (M g i k).ep' m * (N g k j).a)
      (fun k _ => hadd _ _ (hmul _ _ (hM i k).1 ((hN k j).2.2.1 m)) (hmul _ _ ((hM i k).2.2.1 m) (hN k j).1))
  · have hf : (fun g => (((fun g => M g * N g) g) i j).eta) =
        fun g => ∑ k ∈ Finset.univ, ((M g i k).a * (N g k j).eta + (M g i k).eta * (N g k j).a +
          ∑ m ∈ Finset.univ, ((M g i k).ep m * (N g k j).ep' m + (M g i k).ep' m * (N g k j).ep m)) := by
      funext g
      simp only [Matrix.mul_apply, sum_eta, DD.mul_eta]
    rw [hf]
    refine hsum (Fin n) Finset.univ _ (fun k _ => ?_)
    refine hadd _ _ (hadd _ _ (hmul _ _ (hM i k).1 (hN k j).2.2.2) (hmul _ _ (hM i k).2.2.2 (hN k j).1)) ?_
    exact hsum (Fin e) Finset.univ _
      (fun m _ => hadd _ _ (hmul _ _ ((hM i k).2.1 m) ((hN k j).2.2.1 m))
        (hmul _ _ ((hM i k).2.2.1 m) ((hN k j).2.1 m)))

end Bnd

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.defUConj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (e : ℕ) (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), DefU h x u ψ → (∀ k, epC h x u k - z k ∈ BdM h x x.Fr) → ∃ u', DefU h x u' ψ ∧ (∀ k, epC h x u' k = z k) ∧ ∀ k, epC' h x u' k = epC' h x u k := by
  intro l _ L G G0 h n x e u ψ z hu hB
  have hB' : ∀ k, ∃ Y ∈ Od x.A x.Fr n x.a, Yᵀ = -Y ∧
      epC h x u k - z k = dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y := hB
  choose Y hYod hYt hYz using hB'
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) (DD x.Fr e), P = 1 + DD.epM Y := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) (DD x.Fr e), Q = 1 + DD.epM (-Y) := ⟨_, rfl⟩
  have hPQ : P * Q = 1 := by
    rw [hP, hQ]
    exact twoPow_mul_twoPow Y (-Y) (add_neg_cancel Y)
  have hQP : Q * P = 1 := by
    rw [hP, hQ]
    exact twoPow_mul_twoPow (-Y) Y (neg_add_cancel Y)
  have hPa : P.map (fun a => a.a) = 1 := by
    rw [hP]
    exact P_a Y
  have hQa : Q.map (fun a => a.a) = 1 := by
    rw [hQ]
    exact P_a (-Y)
  have hPep : ∀ k, P.map (fun a => a.ep k) = Y k := by
    intro k
    rw [hP]
    exact P_ep Y k
  have hQep : ∀ k, Q.map (fun a => a.ep k) = -Y k := by
    intro k
    rw [hQ]
    exact P_ep (-Y) k
  have hPep' : ∀ k, P.map (fun a => a.ep' k) = 0 := by
    intro k
    rw [hP]
    exact P_ep' Y k
  have hQep' : ∀ k, Q.map (fun a => a.ep' k) = 0 := by
    intro k
    rw [hQ]
    exact P_ep' (-Y) k
  have hPt : Pᵀ = Q := by
    rw [hP, hQ]
    exact P_tr Y (-Y) (fun k => by rw [hYt k]; rfl)
  have hQt : Qᵀ = P := by
    rw [hP, hQ]
    exact P_tr (-Y) Y (fun k => by
      show (-Y k)ᵀ = Y k
      rw [Matrix.transpose_neg, hYt k, neg_neg])
  have hPev := even_P x.a Y hYod
  have hQev := even_P x.a (-Y) (fun k => Submodule.neg_mem _ (hYod k))
  rw [← hP] at hPev
  rw [← hQ] at hQev
  have hinv : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ) * x.ρX x.Fr (h.p₀ γ⁻¹) = 1 := by
    intro γ
    simp only [NP.ρX, ← Matrix.map_mul, map_inv]
    rw [← map_mul, mul_inv_cancel, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ c : DD x.Fr e,
      P * algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c * Q =
        algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, hPQ]
  refine ⟨fun g => P * u g * Q,
    { one := ?_, mul := ?_, red := ?_, even := ?_, form := ?_, ine := ?_,
      ψ_red := hu.ψ_red, ψ_even := hu.ψ_even, ψ_mu := hu.ψ_mu, ord := ?_, bnd := ?_ }, ?_, ?_⟩
  · show P * u 1 * Q = 1
    rw [hu.one, mul_one, hPQ]
  · intro g g'
    show P * u (g * g') * Q = P * u g * Q * (P * u g' * Q)
    rw [hu.mul]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, hQP, one_mul]
  · intro g
    show (P * u g * Q).map (fun a => a.a) = _
    rw [mmul_a, mmul_a, hPa, hQa, one_mul, mul_one, hu.red]
  · intro g
    exact even_mul x.a _ _ (even_mul x.a _ _ hPev (hu.even g)) hQev
  · intro g
    show (P * u g * Q)ᵀ * (P * u (G.frame.conj g) * Q) = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hPt, hQt]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, hQP, one_mul, ← mul_assoc (u g)ᵀ, hu.form g, Matrix.smul_mul, one_mul,
      Matrix.mul_smul, hPQ]
  · intro w g hg
    show P * u g * Q = 1
    rw [hu.ine w g hg, mul_one, hPQ]
  · intro v g
    show (List.ofFn fun i => P * u ((G.φ v) (g i)) * Q -
      algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))).prod = 0
    have key : ∀ i, P * u ((G.φ v) (g i)) * Q -
        algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i)) =
        P * (u ((G.φ v) (g i)) -
          algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) ↑((ψ v i) (g i))) * Q := by
      intro i
      rw [mul_sub, sub_mul, hc]
    have hl : ∀ W : Fin n → Matrix (Fin n) (Fin n) (DD x.Fr e),
        List.ofFn (fun i => P * W i * Q) = (List.ofFn W).map (fun a => P * a * Q) := by
      intro W
      rw [List.map_ofFn]
      rfl
    simp only [key]
    rw [hl, conj_prod P Q hPQ hQP, hu.ord v g, mul_zero, zero_mul]
  · show BndD x.t fun g => P * u g * Q
    exact bnd_mul (K := x.K) (G := G.G₀) (fun g => P * u g) (fun _ => Q)
      (bnd_mul (K := x.K) (G := G.G₀) (fun _ => P) u (bnd_const P) hu.bnd) (bnd_const Q)
  · intro k
    funext γ
    have hz : epC h x u k γ - z k γ =
        x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k := congrFun (hYz k) γ
    have hz' : z k γ = epC h x u k γ -
        (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k) := by
      rw [← hz, sub_sub_cancel]
    rw [hz']
    show ((P * u γ * Q).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) =
      ((u γ).map fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹) -
        (x.ρX x.Fr (h.p₀ γ) * Y k * x.ρX x.Fr (h.p₀ γ⁻¹) - Y k)
    simp only [mmul_ep, mmul_a, hPa, hQa, hPep, hQep, one_mul, mul_one, hu.red]
    simp only [add_mul, mul_neg, neg_mul, Matrix.mul_assoc, hinv, Matrix.mul_one]
    abel
  · intro k
    funext γ
    show ((P * u γ * Q).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹) =
      ((u γ).map fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹)
    simp only [mmul_ep', mmul_a, hPa, hQa, hPep', hQep', one_mul, mul_one, mul_zero, zero_mul,
      zero_add, add_zero]
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.claim2 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ m : Fin S.k.g → S.U.N, S.DualM m → ∀ Φ ∈ S.Ph, ∃ α : Fin S.k.g → S.Tp, (∀ j b, (α j : S.Bh →+ S.F) b = Φ (b • m j) - S.rF b * Φ (m j)) ∧ Lifts S.h S.k fun j => S.alC (α j) := by
  intro l _ S m hm Φ hΦ
  obtain ⟨e, α, μ, hα, hμ, hΦd⟩ := phDec l S Φ hΦ
  let c : Fin e → Fin S.k.g → S.F := fun k j => μ k (m j)
  obtain ⟨u, ψ, hu, h1, h2⟩ := defUTest l S e α μ Φ hα hμ hΦd
  obtain ⟨u', hu', h1', h2'⟩ := defUConj l S.L S.G S.G0 S.h S.n S.x e u ψ
    (fun k => ∑ j, c k j • kapF S.h S.k j) hu
    (fun k => by rw [h1 k]; exact hm (μ k) (hμ k))
  obtain ⟨u'', ψ'', hu'', h1'', h2''⟩ := defUPush l S.L S.G S.G0 S.h S.n S.x S.k e u' ψ c hu' h1'
  have hL := defULift l S.L S.G S.G0 S.h S.n S.x S.k u'' ψ'' hu'' h1''
  refine ⟨fun j => ⟨∑ k, c k j • α k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hα k)⟩, ?_, ?_⟩
  · intro j b
    show (∑ k, c k j • α k) b = _
    rw [hΦd, add_sub_cancel_left]
    simp [c, mul_comm]
  · have e2 : (fun j => S.alC (∑ k, c k j • α k)) = epC' S.h S.x u'' := by
      funext j
      rw [h2'' j, (alSel l S).2.2.1 (Fin e) (fun k => c k j) α]
      simp only [h2', h2]
    show Lifts S.h S.k (fun j => S.alC (∑ k, c k j • α k))
    rw [e2]
    exact hL
