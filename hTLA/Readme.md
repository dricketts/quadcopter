Design choices
==============

1) Shallow Encoding
   This should make it easier to extend the language in the future.

2) Heterogeneous states


Description
-----------

The system is built in minimal layers, each one is an intuitionistic logic
(by lifting).

StateProp := State -> Prop

- embed :: Prop -> StateProp

ActionProp := State -> State -> Prop

- embed   :: Prop -> ActionProp
- initial :: StateProp -> ActionProp
- final   :: StateProp -> ActionProp
- stutter :: forall X, (State -> X) -> ActionProp

TraceProp := stream State -> Prop

- always     :: TraceProp -> TraceProp
- eventually :: TraceProp -> TraceProp
- starts     :: ActionProp -> TraceProp
- now        :: StateProp -> TraceProp
- through    :: TraceProp -> TraceProp  ["until (and including) the next time"]

The leaf operators are achieved using standard shallow encodings; this often
requires pointwise lifting of operations.


Speculative Features
====================

1) Hybrid (Dense) Traces
   Hybrid traces embed the function for continuous evolution directly inside the
   trace. This has several benefits.
   1) It decreases the gap between the model and the implementation
   2) It allows us to directly make statements about the evolution function.
