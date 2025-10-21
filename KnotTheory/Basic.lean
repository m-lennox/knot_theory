structure OrientedDiagramNode where
  private mk ::
  o1 : Nat
  o2 : Nat
  u1 : Nat
  u2 : Nat
  distinct : o1 ≠ o2 ∧ u1 ≠ u2

def mkOrientedDiagramNode (o1 o2 u1 u2 : Nat) : Option OrientedDiagramNode :=
  if h : o1 ≠ o2 ∧ u1 ≠ u2 then
    some { o1, o2, u1, u2, distinct := h }
  else
    none

def OrientedDiagramNode.segments (self : OrientedDiagramNode) : List Nat :=
  [self.o1, self.o2, self.u1, self.u2]

structure OrientedPreDiagram where
  nodes : Array OrientedDiagramNode

def OrientedPreDiagram.crossing_num (self : OrientedPreDiagram) : Nat :=
  self.nodes.size

def num_in (nodes : Array OrientedDiagramNode) (segment : Nat) : Nat :=
  (nodes.map (fun node => ((node.o1 == segment).toNat + (node.u1 == segment).toNat))).sum

def num_out (nodes : Array OrientedDiagramNode) (segment : Nat) : Nat :=
  (nodes.map (fun node => ((node.o2 == segment).toNat + (node.u2 == segment).toNat))).sum

structure OrientedDiagram extends OrientedPreDiagram where
  segment_node_correspondence : ∀ s : Nat, (num_in nodes s = num_out nodes s) ∧ (num_in nodes s ∈ [0, 1])

#eval (OrientedDiagramNode.mk 1 2 3 4 (by simp)).segments
