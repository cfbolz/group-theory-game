import subgroup.definitions group.group_powers
import data.set.finite

/-
Let G be a group. The type of subgroups of G is `subgroup G`. 
In other words, if `H : subgroup G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Lagrange's theorem states that given a finite groups G, all 
subgroups of G has order divided by the order of G.

In Lean, we represent a finite group by adding the predicate 
[fintype G] to some group G.

In definitions, we've defined left cosets as 
def lcoset (g : G) (K : subgroup G) := {s : G | ∃ k ∈ K, s = g * k}
-/

namespace mygroup

open group set

variables {G : Type} [group G] [fintype G] (H : subgroup G) 

/- The subgroups of a finite group are finite -/
theorem finite_subgroup : finite (H : set G) :=
finite.of_fintype _

noncomputable instance : has_coe (subgroup G) (finset G) := 
⟨λ H, @finite.to_finset G (H : set G) (finite_subgroup H)⟩

#check (H : finset G).card

end mygroup