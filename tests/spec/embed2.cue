// This case tests the unification of embedded disjunction that has a closed struct.
x: 1
(close({}) | int) // ok, embedded closed struct can be unified with the parent struct.