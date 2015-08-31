
Section Graph.

  Variable A : Type.
  
  Definition graph := A -> A -> Type.

  Definition edge (G:graph) s d := G s d.

End Graph.

Arguments edge {_} _ _ _.