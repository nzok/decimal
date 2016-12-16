module FixedTest (
    main
) where

import Data.Ratio (numerator, denominator, (%))
import Fixed
import Test.QuickCheck hiding (Fixed, scale)

-- for makeFixed use FP

siGen :: Gen Integer            -- signed integer
siGen = choose (-499,499)

piGen :: Gen Integer            -- positive integer
piGen = choose (1,499)

type R = Decimal

ssGen :: Gen (Scale R)  -- scale
ssGen = choose (0,4) >>= (return . Scale)

tpGen :: Gen Integer    -- tiny positive integer
tpGen = choose (1,10)

tsGen :: Gen (Fixed R)  -- tiny scaled decimal
tsGen =
    let tiGen = choose (-5,5)
        txGen = choose (0,2) >>= (return . Scale)
    in  do i <- tiGen
           s <- txGen
           return $ FP i s

sdGen :: Gen (Fixed R)  -- scaled decimal
sdGen =
    do i <- siGen
       s <- ssGen
       return $ FP i s

nzGen :: Gen (Fixed R)  -- non-zero scaled decimal
nzGen =
    do j <- piGen
       n <- elements [False,True]
       let i = if n then negate j else j
       s <- ssGen
       return $ FP i s

prop_integers_have_scale_zero =
    forAll siGen $ \i ->
    scale (fromInteger i :: Fixed R) == 0

prop_fromInteger_is_invertible =
    forAll siGen $ \i ->
    toInteger (fromInteger i :: Fixed R) == i
{-

prop_scale =
    forAll siGen $ \i ->
    forAll ssGen $ \s ->
    scale (toScaledDecimal i s) == s

prop_scale_of_make =
    forAll siGen $ \i ->
    forAll ssGen $ \s ->
    let x = makeScaledDecimal i s in
    scale x == s && toScaledDecimal x s == x

prop_ratio =
    forAll siGen $ \n ->
    forAll piGen $ \d ->
    forAll ssGen $ \s ->
    ratio (toScaledDecimal n s) (toScaledDecimal d s) == ratio n d

prop_equality_ignores_scale =
    forAll siGen $ \n ->
    forAll ssGen $ \s ->
    forAll ssGen $ \t ->
    toScaledDecimal n s == toScaledDecimal n t

-}

prop_equality_is_reflexive =
    forAll sdGen $ \x ->
    x == x

prop_equality_is_symmetric =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x == y) == (y == x)

prop_equality_is_transitive =
    forAll tsGen $ \x ->
    forAll tsGen $ \y ->
    forAll tsGen $ \z ->
    x == y ==> (y == z) == (x == z)

prop_order_trichotomy =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (length $ filter id $ [x < y, x == y, x > y]) == 1

prop_order_is_irreflexive =
    forAll sdGen $ \x ->
    not (x < x)

prop_order_is_transitive =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    if x < y && y < z then x < z else
    if x > y && y > z then x > z else True

prop_negate_negates_sign =
    forAll sdGen $ \x ->
    signum (negate x) == negate (signum x)

prop_negate_cancels =
    forAll sdGen $ \x ->
    negate (negate x) == x

prop_abs_is_not_negative =
    forAll sdGen $ \x ->
    abs x >= 0 && (abs x == 0) == (x == 0)

prop_abs_of_negate_is_abs =
    forAll sdGen $ \x ->
    abs (negate x) == abs x

prop_abs_times_sign_is_identity =
    forAll sdGen $ \x ->
    abs x * signum x == x

prop_gcd_is_ok =
    forAll nzGen $ \x ->
    forAll nzGen $ \y ->
    lia_gcd x y `lia_divides` x &&
    lia_gcd x y `lia_divides` y

prop_lcm_is_ok =
    forAll nzGen $ \x ->
    forAll nzGen $ \y ->
    x `lia_divides` lia_lcm x y &&
    y `lia_divides` lia_lcm x y

{-
prop_less_and_greater_are_opposites =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x < y) == (y > x)

prop_less_and_greater_equal_are_complements =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x < y) /= (x >= y)

prop_to_integer_is_inverse_of_from_integer =
    forAll siGen $ \i ->
    toInteger (fromInteger i :: ScaledDecimal) == i

prop_addition_distributes_over_make =
    forAll siGen $ \i ->
    forAll siGen $ \j ->
    forAll ssGen $ \s ->
    makeScaledDecimal i s + makeScaledDecimal j s == makeScaledDecimal (i+j) s
    
-}

prop_zero_is_additive_identity =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let z = FP 0 s in
    z + x == x && x + z == x && x - z == x

prop_addition_commutes =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    x + y == y + x

prop_addition_associates =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    x + (y + z) == (x + y) + z

prop_negation_is_compatible_with_subtraction =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    x - y == x + negate y

prop_subtraction_is_skew_commutative =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    x - y == negate (y - x)

prop_zero_is_multiplicative_zero =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let z = toFixed 0 s in
    z * x == z && x * z == z

prop_one_is_multiplicative_identity =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let w = toFixed 1 s in
    w * x == x && x * w == x

prop_minus_one_is_multiplicative_negater =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let m = toFixed (negate 1) s in
    m * x == negate x && x * m == negate x

prop_multiplication_commutes =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    x * y == y * x

prop_multiplication_associates =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    x * (y * z) == (x * y) * z
{-
prop_multiplication_distributes_over_make =
    forAll siGen $ \i ->
    forAll siGen $ \j ->
    forAll ssGen $ \s ->
    forAll ssGen $ \t ->
    makeScaledDecimal i s * makeScaledDecimal j t ==
      makeScaledDecimal (i*j) (s+t)
-}
prop_left_distribution_holds =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    x * (y + z) == x * y + x * z

prop_signum_abstracts_times =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    signum (x * y) == signum x * signum y

prop_right_distribution_holds =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    (y + z) * x == y * x + z * x

prop_zero_pow_is_zero =
    forAll ssGen $ \s ->
    let z = toFixed 0 s in
    forAll tpGen $ \n ->
    z ^ n == z

prop_one_pow_is_one =
    forAll ssGen $ \s ->
    let w = toFixed 1 s in
    forAll tpGen $ \n ->
    w ^ n == w

prop_pow_zero_is_unity =
    forAll sdGen $ \x ->
    x ^ 0 == 1

prop_pow_one_is_identity =
    forAll sdGen $ \x ->
    x ^ 1 == x

prop_pow_two_is_square =
    forAll sdGen $ \x ->
    x ^ 2 == x * x

{-
was_power_of_10 :: Integer -> Bool

was_power_of_10 n
  | n`mod`2 == 0 = was_power_of_10 (n`div`2)
  | n`mod`5 == 0 = was_power_of_10 (n`div`5)
  | True         = n == 1

prop_sds_are_rationals =
    forAll siGen $ \n ->
    forAll ssGen $ \s ->
    toRational (toScaledDecimal n s) == ratio n 1

prop_sds_are_decimal_rationals =
    forAll sdGen $ \x ->
    was_power_of_10 (denominator (toRational x))

prop_recip_is_trivial =
    forAll nzGen $ \x ->
    recip x == 1 / x

-- I want to say something about division.  For example,
-- (n*x)/x == n && (n*x)/n == x.
-- But I can't; these "laws" are NOT valid for scaled (/).

prop_div_mod_fit_together =
    forAll sdGen $ \x ->
    forAll nzGen $ \y ->
    let (q,r) = x `divMod` y in
    scale q == 0 &&
    scale r == max (scale x) (scale y) &&
    q * y + r == x

prop_div_is_floored_division =
    forAll sdGen $ \x ->
    forAll nzGen $ \y ->
    x `div` y == fromInteger (floor (ratio x y))

prop_quot_rem_fit_together =
    forAll sdGen $ \x ->
    forAll nzGen $ \y ->
    let (q,r) = x `quotRem` y in
    scale q == 0 &&
    scale r == max (scale x) (scale y) &&
    q * y + r == x

prop_quot_is_truncated_division =
    forAll sdGen $ \x ->
    forAll nzGen $ \y ->
    x `quot` y == fromInteger (truncate (ratio x y))

prop_pred_is_inverse_of_succ =
    forAll sdGen $ \x ->
    succ (pred x) == x

prop_succ_is_inverse_of_pred =
    forAll sdGen $ \x ->
    pred (succ x) == x

prop_succ_increments_bottom_digit =
    forAll sdGen $ \x ->
    succ x == x + makeScaledDecimal 1 (scale x)

prop_pred_decrements_bottom_digit =
    forAll sdGen $ \x ->
    pred x == x - makeScaledDecimal 1 (scale x)

prop_read_of_integer_is_ok =
    forAll siGen $ \n ->
    read (show n) == toScaledDecimal n 0

prop_read_of_show_is_exact =
    forAll sdGen $ \x ->
    read (show x) == x

prop_show_of_integer_is_ok =
    forAll siGen $ \n ->
    show (fromIntegral n :: ScaledDecimal) == show n

trim :: String -> String
trim str = loop (reverse str)
  where loop ('0' : cs) = loop cs
        loop cs = if '.' `elem` cs then reverse cs else str

prop_show_of_read_is_almost_identity =
    forAll sdGen $ \x ->
    let str = show x in
    trim (show (read str :: ScaledDecimal)) == trim str

prop_truncate_truncates =
    forAll sdGen $ \x ->
    let t = fromIntegral (truncate x) in
    if x < 0 then x <= t && t-1 < x else t <= x && x < t+1

prop_floor_floors =
    forAll sdGen $ \x ->
    let t = fromIntegral (floor x) in
    t <= x && x < t+1

prop_ceiling_ceilings =
    forAll sdGen $ \x ->
    let t = fromIntegral (ceiling x) in
    t >= x && x > t-1

prop_round_rounds =
    forAll sdGen $ \x ->
    let t = fromIntegral (round x) in
    abs (x - t)*2 <= 1
-}

prop_convert_Down =
    forAll sdGen $ \x ->
    let (y,z) = convertFixed Down x in
    fromInteger y <= x && x < fromInteger (y + 1) &&
    fromInteger y + z == x

prop_convert_Up =
    forAll sdGen $ \x ->
    let (y,z) = convertFixed Up x in
    fromInteger y >= x && x > fromInteger (y - 1) &&
    fromInteger y + z == x

prop_convert_In =
    forAll sdGen $ \x ->
    let (y,z) = convertFixed In x in
    (if x > 0 then y >= 0 && fromInteger y <= x && x < fromInteger (y+1) else
     if x < 0 then y <= 0 && fromInteger y >= x && x > fromInteger (y-1) else
     y == 0 && z == x) &&
    fromInteger y + z == x

prop_convert_Out =
    forAll sdGen $ \x ->
    let (y,z) = convertFixed Out x in
    (if x > 0 then y > 0 && fromInteger y >= x && x > fromInteger (y-1) else
     if x < 0 then y < 0 && fromInteger y <= x && x < fromInteger (y+11) else
     y == 0 && z == x) &&
    fromInteger y + z == x

prop_convert_Even =
    forAll sdGen $ \x ->
    let (y,z) = convertFixed Even x in
    even y &&
    fromInteger y + z == x

prop_read_inverts_show =
    forAll sdGen $ \x ->
    case readFixedDecimal (show x) of
      [(y,"")] -> y == x
      _        -> False

main =
    do {-
       check prop_scale
       check prop_scale_of_make
       check prop_ratio
       check prop_equality_ignores_scale
       -}
       check prop_convert_Down
       check prop_convert_Up
       check prop_convert_In
       check prop_convert_Out
       check prop_convert_Even

       check prop_integers_have_scale_zero
       check prop_fromInteger_is_invertible

       check prop_equality_is_reflexive
       check prop_equality_is_symmetric
       check prop_equality_is_transitive
       check prop_order_trichotomy
       check prop_order_is_irreflexive
       check prop_order_is_transitive

       check prop_negate_negates_sign
       check prop_negate_cancels

       check prop_abs_is_not_negative
       check prop_abs_of_negate_is_abs
       check prop_abs_times_sign_is_identity

       check prop_zero_is_additive_identity
       check prop_addition_commutes
       check prop_addition_associates
       check prop_negation_is_compatible_with_subtraction
       check prop_subtraction_is_skew_commutative

       check prop_zero_is_multiplicative_zero
       check prop_one_is_multiplicative_identity
       check prop_minus_one_is_multiplicative_negater
       check prop_signum_abstracts_times
       check prop_multiplication_commutes
       check prop_multiplication_associates
       check prop_left_distribution_holds
       check prop_right_distribution_holds

       check prop_zero_pow_is_zero
       check prop_one_pow_is_one
       check prop_pow_zero_is_unity
       check prop_pow_one_is_identity
       check prop_pow_two_is_square

       check prop_gcd_is_ok
       check prop_lcm_is_ok
       check prop_read_inverts_show
       {-
       check prop_less_and_greater_are_opposites
       check prop_less_and_greater_equal_are_complements
       check prop_to_integer_is_inverse_of_from_integer
       check prop_addition_distributes_over_make
       check prop_multiplication_distributes_over_make

       check prop_sds_are_rationals
       check prop_sds_are_decimal_rationals
       check prop_recip_is_trivial
       check prop_div_mod_fit_together
       check prop_div_is_floored_division
       check prop_quot_rem_fit_together
       check prop_quot_is_truncated_division
       check prop_pred_is_inverse_of_succ
       check prop_succ_is_inverse_of_pred
       check prop_succ_increments_bottom_digit
       check prop_pred_decrements_bottom_digit
       check prop_read_of_integer_is_ok
       check prop_read_of_show_is_exact
       check prop_show_of_integer_is_ok
       check prop_show_of_read_is_almost_identity
       check prop_truncate_truncates
       check prop_floor_floors
       check prop_ceiling_ceilings
       check prop_round_rounds
       -}
       return ()
  where check  = quickCheckWith myArgs
        myArgs = Args {replay = Nothing, maxSuccess = 1000,
                       maxDiscardRatio = 500, maxSize = 100, chatty = True}

