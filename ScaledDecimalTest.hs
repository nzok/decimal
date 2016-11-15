import Ratio (numerator, denominator, (%))
import Scaled
import ScaledDecimal
import Test.QuickCheck

makeScaledDecimal :: Integer -> Int -> ScaledDecimal
makeScaledDecimal n s | s >= 0 =
    toScaledDecimal (ratio n (10 ^ s)) s

siGen :: Gen Integer            -- signed integer
siGen = choose (-49,49)

piGen :: Gen Integer		-- positive integer
piGen = choose (1,49)

ssGen :: Gen Int		-- scale
ssGen = choose (0,4)

tsGen :: Gen ScaledDecimal      -- tiny scaled decimal
tsGen =
    let tiGen :: Gen Integer
        txGen :: Gen Int
        tiGen = choose (-5,5)
        txGen = choose (0,2)
    in  do i <- tiGen
           s <- txGen
           return $ makeScaledDecimal i s

sdGen :: Gen ScaledDecimal	-- scaled decimal
sdGen =
    do i <- siGen
       s <- ssGen
       return $ makeScaledDecimal i s

nzGen :: Gen ScaledDecimal	-- non-zero scaled decimal
nzGen =
    do j <- piGen
       n <- elements [False,True]
       let i = if n then negate j else j
       s <- ssGen
       return $ makeScaledDecimal i s



prop_ints_have_scale_zero =
    forAll siGen $ \i ->
    scale i == 0

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
    ratio (makeScaledDecimal n s) (makeScaledDecimal d s) == ratio n d

prop_equality_ignores_scale =
    forAll siGen $ \n ->
    forAll ssGen $ \s ->
    forAll ssGen $ \t ->
    toScaledDecimal n s == toScaledDecimal n t

prop_equality_commutes =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x == y) == (y == x)

prop_equality_is_transitive =
    forAll tsGen $ \x ->
    forAll tsGen $ \y ->
    forAll tsGen $ \z ->
    x == y ==> (y == z) == (x == z)

prop_less_and_greater_are_opposites =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x < y) == (y > x)

prop_less_and_greater_equal_are_complements =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    (x < y) /= (x >= y)

prop_negate_negates_sign =
    forAll sdGen $ \x ->
    signum (negate x) == negate (signum x)

prop_negate_cancels =
    forAll sdGen $ \x ->
    negate (negate x) == x

prop_abs_of_negate_is_abs =
    forAll sdGen $ \x ->
    abs (negate x) == abs x

prop_abs_times_sign_is_identity =
    forAll sdGen $ \x ->
    abs x * signum x == x

prop_to_integer_is_inverse_of_from_integer =
    forAll siGen $ \i ->
    toInteger (fromInteger i :: ScaledDecimal) == i

prop_zero_is_additive_identity =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let z = toScaledDecimal 0 s in
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

prop_addition_distributes_over_make =
    forAll siGen $ \i ->
    forAll siGen $ \j ->
    forAll ssGen $ \s ->
    makeScaledDecimal i s + makeScaledDecimal j s == makeScaledDecimal (i+j) s
    
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
    let z = toScaledDecimal 0 s in
    z * x == z && x * z == z

prop_one_is_multiplicative_identity =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let w = toScaledDecimal 1 s in
    w * x == x && x * w == x

prop_minus_one_is_multiplicative_negater =
    forAll sdGen $ \x ->
    forAll ssGen $ \s ->
    let m = toScaledDecimal (negate 1) s in
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

prop_multiplication_distributes_over_make =
    forAll siGen $ \i ->
    forAll siGen $ \j ->
    forAll ssGen $ \s ->
    forAll ssGen $ \t ->
    makeScaledDecimal i s * makeScaledDecimal j t ==
      makeScaledDecimal (i*j) (s+t)

prop_left_distribution_holds =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    x * (y + z) == x * y + x * z

prop_right_distribution_holds =
    forAll sdGen $ \x ->
    forAll sdGen $ \y ->
    forAll sdGen $ \z ->
    (y + z) * x == y * x + z * x

was_power_of_10 :: Integer -> Bool

was_power_of_10 n
  | n <= 0         = False
  | n `mod` 2 == 0 = was_power_of_10 (n `div` 2)
  | n `mod` 5 == 0 = was_power_of_10 (n `div` 5)
  | True           = n == 1

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

prop_pow_zero_is_unity =
    forAll sdGen $ \x ->
    x ^ 0 == 1

prop_pow_one_is_identity =
    forAll sdGen $ \x ->
    x ^ 1 == x

prop_pow_two_is_square =
    forAll sdGen $ \x ->
    x ^ 2 == x * x

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
  where loop []         = "0"
        loop ('0' : cs) = loop cs
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

main =
    do check prop_ints_have_scale_zero
       check prop_scale
       check prop_scale_of_make
       check prop_ratio
       check prop_equality_ignores_scale
       check prop_equality_commutes
       check prop_equality_is_transitive
       check prop_less_and_greater_are_opposites
       check prop_less_and_greater_equal_are_complements
       check prop_negate_negates_sign
       check prop_negate_cancels
       check prop_abs_of_negate_is_abs
       check prop_abs_times_sign_is_identity
       check prop_to_integer_is_inverse_of_from_integer
       check prop_zero_is_additive_identity
       check prop_addition_commutes
       check prop_addition_associates
       check prop_addition_distributes_over_make
       check prop_negation_is_compatible_with_subtraction
       check prop_subtraction_is_skew_commutative
       check prop_zero_is_multiplicative_zero
       check prop_one_is_multiplicative_identity
       check prop_minus_one_is_multiplicative_negater
       check prop_multiplication_commutes
       check prop_multiplication_associates
       check prop_multiplication_distributes_over_make
       check prop_left_distribution_holds
       check prop_right_distribution_holds
       check prop_sds_are_rationals
       check prop_sds_are_decimal_rationals
       check prop_recip_is_trivial
       check prop_div_mod_fit_together
       check prop_div_is_floored_division
       check prop_quot_rem_fit_together
       check prop_quot_is_truncated_division
       check prop_pow_zero_is_unity
       check prop_pow_one_is_identity
       check prop_pow_two_is_square
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
       return ()
  where check  = quickCheckWith myArgs
        myArgs = Args {replay = Nothing, maxSuccess = 500,
                       maxDiscard = 500, maxSize = 100, chatty = True}

