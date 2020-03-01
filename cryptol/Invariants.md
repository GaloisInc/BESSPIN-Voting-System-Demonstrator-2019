# sbb_invariants.h

## SBB
- SBB_Machine_Invariant
- SBB_String
- SBB_Strings_Invariant
- gpio_mem_button_lights
- gpio_mem_motors
- barcode_state
- SBB_Invariant

## SBB Concrete Refinement
- cbl_gpio_rel
Relates an integer to the state of cast button light (1 if lit)
- sbl_gpio_rel
Relates an integer to the state of spoil button light (1 if lit)
- barcode_rel
Relates Barcode_Valid to hw_barcode being has_valid_barcode
- motor_gpio_rel
Relates a motor state to two integers, standing for forward and backward bits
- paper_present_rel
Relates a paper present value to the state of SBB satisfying Paper_Present
- SBB_Refinement
Relates SBB state to all sorts of concrete values

## Lemmas
- SBB_Impl_Prop_Lights_Jointness
SBB_Refinement /\ SBB_Machine_Invariant /\ !ABORT => Prop_Lights_On_Jointness
- SBB_Impl_Prop_Only_Valid_Barcode
SBB_Refinement /\ SBB_Machine_Invariant /\ !ABORT => Prop_Only_Valid_Barcode
...

# `sbb_asm_prop.h`

## `SBB_Properties`
- `Accepted_Barcode`
Predicate holding if logical state in {WaitForDecision, Cast, Spoil}
- `Prop_Only_Valid_Barcode`
Accepted Barcode state => barcode is `has_valid_barcode`
- `Prop_Lights_On_With_Ballot`
Either light is lit => barcode is `has_valid_barcode`
- `Prop_Lights_On_Jointness`
Cast button light lit <=> Spoil button light lit
- `Prop_Lights_Off_Power_On`
Logical state is Standby => both lights are off
- `Prop_Initialized_Motor_Off`
Logical state in {Initialize, Standby} => motor off
- `Prop_Motor_On_Paper_Present`
Motor on => Paper present

# `SBB_State_Invariants`
- `valid_range`
Predicate relating 3 values, such that lo <= x <= hi
- `M_ASM_valid`, ...
Bunch of predicates making sure the variables from the state stay in their range
- `Initialize_Inv`, `Standby_Inv`, ...
Bunch of predicates describing expectations in a given logical state
- `SBB_States_Invariant`
Relates logical states to the predicate describing its expectations
