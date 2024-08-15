# Remarks

Here are some various remarks about the project :
  - The `eval` semantics of program isn’t clean.
  - The conversions in `shared/bir_cv*Lib.sml` should create a theorem by using the input term. Here, we are creating the output theorem from the right side and rewriting it to make the input term appear (but there is no guarantee).
  - Implementation in the actual HolBA project can be done in two ways :
    - You either keep the project structure the same and add support for unimplemented operations in the `bir_cv` representation.
    The representation of HolBA and the `compute` one here are really similar (to a few differences like enforcing typing in environment manipulation).
    - The other way would be to change the BIR representation in HolBA and use the `bir_cv` representation instead. This would remove translation cost but a lot more rewriting would be necessary.
