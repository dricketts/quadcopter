This directory contains our Sys abstraction (specified in rTLA, our variant of TLA) and the systems that we've specified using our Sys abstraction. It also contains an old version of our height shim, verified in monolithically rTLA without the Sys abstraction. This version no longer builds, primarily for syntactic reasons, but we include it here for comparison.

Velocity Shim
-------------
- FirstDerivShimCtrl.v - the shim logic, assuming an upper bound on the current velocity.
- FirstDerivShim.v - the shim logic composed with various sensor and delay compensation modules

Height Shim
-----------
- SecondDerivShimCtrl.v - the shim logic, assuming an upper bound on the current velocity and height
- SecondDerivShim.v - the shim logic composed with various sensor and delay compensation modules

Error Correction
----------------
- SensorWithError.v - a sensor module that continuously reads a physical variable to within err of the actual value
- SensorWithDelayRange.v - a delay compensation module based on the first derivative of a variable and a current upper bound on the variable
- SensorWithDelayRangeSndOrder.v - a delay compensation module based on the second derivative of a variable and a current upper bound on the variable and its first derivative

Old Height Shim
---------------
This shim no longer builds, but here are the relevant files:

- AbstractIndAccCtrl.v
- OneDimAccShim1.v - a concrete height upper bound shim. This is a refinement of AbstractIndAccCtrl.v.
- OneDimAccShim2.v - another concrete height upper bound shim. This is a refinement of AbstractIndAccCtrl.v as well.
- OneDimAccShimUtil.v - this file defines useful functions and lemmas for the two height upper bound shims.

