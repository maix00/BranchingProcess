import Topology.Cadlag.Skorokhod.Evaluation

example {E : Type*} [MetricSpace E] (f : CadlagPath unitInterval E)
    (t : unitInterval) (hf : ContinuousAt f t) :
    ContinuousAt (fun g : CadlagPath unitInterval E => g t) f :=
  Skorokhod.continuousAt_apply_of_continuousAt f t hf

#print axioms Skorokhod.continuousAt_apply_of_continuousAt
