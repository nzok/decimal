import Ratio (numerator, denominator, (%))
import Scaled
import ScaledBinary
import Test.QuickCheck

makeScaledBinary :: Integer -> Int -> ScaledBinary
makeScaledBinary n s | s >= 0 =
    toScaledBinary (ratio n (2 ^ s)) s

siGen :: Gen Integer            -- signed integer
siGen = choose (-49,49)

piGen :: Gen Integer            -- positive integer
piGen = choose (1,49)

ssGen :: Gen Int                -- scale
ssGen = choose (0,7)

tsGen :: Gen ScaledBinary      -- tiny scaled binary
tsGen =
    let tiGen :: Gen Integer
        txGen :: Gen Int
        tiGen = choose (-5,5)
        txGen = choose (0,2)
    in  do i <- tiGen
           s <- txGen
           return $ makeScaledBinary i s

sbGen :: Gen ScaledBinary       -- scaled binary
sbGen =
    do i <- siGen
       s <- ssGen
       return $ makeScaledBinary i s

nzGen :: Gen ScaledBinary       -- non-zero scaled binary
nzGen =
    do j <- piGen
       n <- elements [False,True]
       let i = if n then negate j else j
       s <- ssGen
       return $ makeScaledBinary i s



prop_ints_have_scale_zero =
    forAll siGen $ \i ->
    scale i == 0

prop_scale =
    forAll siGen $ \i ->
    forAll ssGen $ \s ->
    scale (toScaledBinary i s) == s

prop_scale_of_make =
    forAll siGen $ \i ->
    forAll ssGen $ \s ->
    let x = makeScaledBinary i s in
    scale x == s && toScaledBinary x s == x

prop_ratio =
    forAll siGen $ \n ->
    forAll piGen $ \d ->
    forAll ssGen $ \s ->
    ratio (toScaledBinary n s) (toScaledBinary d s) == ratio n d

prop_equality_ignores_scale =
    forAll siGen $ \n ->
    forAll ssGen $ \s ->
    forAll ssGen $ \t ->
    toScaledBinary n s == toScaledBinary n t

prop_equality_commutes =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    (x == y) == (y == x)

prop_equality_is_transitive =
    forAll tsGen $ \x ->
    forAll tsGen $ \y ->
    forAll tsGen $ \z ->
    x == y ==> (y == z) == (x == z)

prop_less_and_greater_are_opposites =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    (x < y) == (y > x)

prop_less_and_greater_equal_are_complements =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    (x < y) /= (x >= y)

prop_negate_negates_sign =
    forAll sbGen $ \x ->
    signum (negate x) == negate (signum x)

prop_negate_cancels =
    forAll sbGen $ \x ->
    negate (negate x) == x

prop_abs_of_negate_is_abs =
    forAll sbGen $ \x ->
    abs (negate x) == abs x

prop_abs_times_sign_is_identity =
    forAll sbGen $ \x ->
    abs x * signum x == x

prop_to_integer_is_inverse_of_from_integer =
    forAll siGen $ \i ->
    toInteger (fromInteger i :: ScaledBinary) == i

prop_zero_is_additive_identity =
    forAll sbGen $ \x ->
    forAll ssGen $ \s ->
    let z = toScaledBinary 0 s in
    z + x == x && x + z == x && x - z == x

prop_addition_commutes =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    x + y == y + x

prop_addition_associates =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    forAll sbGen $ \z ->
    x + (y + z) == (x + y) + z

prop_negation_is_compatible_with_subtraction =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    x - y == x + negate y

prop_subtraction_is_skew_commutative =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    x - y == negate (y - x)

prop_zero_is_multiplicative_zero =
    forAll sbGen $ \x ->
    forAll ssGen $ \s ->
    let z = toScaledBinary 0 s in
    z * x == z && x * z == z

prop_one_is_multiplicative_identity =
    forAll sbGen $ \x ->
    forAll ssGen $ \s ->
    let w = toScaledBinary 1 s in
    w * x == x && x * w == x

prop_minus_one_is_multiplicative_negater =
    forAll sbGen $ \x ->
    forAll ssGen $ \s ->
    let m = toScaledBinary (negate 1) s in
    m * x == negate x && x * m == negate x

prop_multiplication_commutes =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    x * y == y * x

prop_multiplication_associates =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    forAll sbGen $ \z ->
    x * (y * z) == (x * y) * z

prop_left_distribution_holds =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    forAll sbGen $ \z ->
    x * (y + z) == x * y + x * z

prop_right_distribution_holds =
    forAll sbGen $ \x ->
    forAll sbGen $ \y ->
    forAll sbGen $ \z ->
    (y + z) * x == y * x + z * x

is_power_of_2 :: Integer -> Bool

is_power_of_2 1 = True
is_power_of_2 n = n > 0 && n `mod` 2 == 0 && is_power_of_2 (n`div`2)

prop_sds_are_rationals =
    forAll siGen $ \n ->
    forAll ssGen $ \s ->
    toRational (toScaledBinary n s) == ratio n 1

prop_sds_are_binary_rationals =
    forAll sbGen $ \x ->
    is_power_of_2 (denominator (toRational x))

prop_recip_is_trivial =
    forAll nzGen $ \x ->
    recip x == 1 / x

-- *** This is NOT valid ***
prop_division_with_integer_result_is_ok =
    forAll nzGen $ \x ->
    forAll siGen $ \n ->
    let n' = toScaledBinary n 0 in
    n' / x == n' * recip x

prop_div_mod_fit_together =
    forAll sbGen $ \x ->
    forAll nzGen $ \y ->
    let (q,r) = x `divMod` y in
    scale q == 0 &&
    scale r == max (scale x) (scale y) &&
    q * y + r == x

prop_div_is_floored_division =
    forAll sbGen $ \x ->
    forAll nzGen $ \y ->
    x `div` y == fromInteger (floor (ratio x y))

prop_quot_rem_fit_together =
    forAll sbGen $ \x ->
    forAll nzGen $ \y ->
    let (q,r) = x `quotRem` y in
    scale q == 0 &&
    scale r == max (scale x) (scale y) &&
    q * y + r == x

prop_quot_is_truncated_division =
    forAll sbGen $ \x ->
    forAll nzGen $ \y ->
    x `quot` y == fromInteger (truncate (ratio x y))

prop_pow_zero_is_unity =
    forAll sbGen $ \x ->
    x ^ 0 == 1

prop_pow_one_is_identity =
    forAll sbGen $ \x ->
    x ^ 1 == x

prop_pow_two_is_square =
    forAll sbGen $ \x ->
    x ^ 2 == x * x

prop_pred_is_inverse_of_succ =
    forAll sbGen $ \x ->
    succ (pred x) == x

prop_succ_is_inverse_of_pred =
    forAll sbGen $ \x ->
    pred (succ x) == x

prop_succ_increments_bottom_digit =
    forAll sbGen $ \x ->
    succ x == x + makeScaledBinary 1 (scale x)

prop_pred_decrements_bottom_digit =
    forAll sbGen $ \x ->
    pred x == x - makeScaledBinary 1 (scale x)

prop_read_of_integer_is_ok =
    forAll siGen $ \n ->
--  (read (show n) :: ScaledBinary) == toScaledBinary n 0
    read (show n) == toScaledBinary n 0

prop_read_of_show_is_exact =
    forAll sbGen $ \x ->
    read (show x) == x

prop_show_of_integer_is_ok =
    forAll siGen $ \n ->
    show (fromIntegral n :: ScaledBinary) == show n

trim :: String -> String
trim str = loop (reverse str)
  where loop []         = "0"
        loop ('0' : cs) = loop cs
        loop cs = if '.' `elem` cs then reverse cs else str

prop_show_of_read_is_almost_identity =
    forAll sbGen $ \x ->
    let str = show x in
    trim (show (read str :: ScaledBinary)) == trim str

prop_truncate_truncates =
    forAll sbGen $ \x ->
    let t = fromIntegral (truncate x) in
    if x < 0 then x <= t && t-1 < x else t <= x && x < t+1

prop_floor_floors =
    forAll sbGen $ \x ->
    let t = fromIntegral (floor x) in
    t <= x && x < t+1

prop_ceiling_ceilings =
    forAll sbGen $ \x ->
    let t = fromIntegral (ceiling x) in
    t >= x && x > t-1

prop_round_rounds =
    forAll sbGen $ \x ->
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
       check prop_negation_is_compatible_with_subtraction
       check prop_subtraction_is_skew_commutative
       check prop_zero_is_multiplicative_zero
       check prop_one_is_multiplicative_identity
       check prop_minus_one_is_multiplicative_negater
       check prop_multiplication_commutes
       check prop_multiplication_associates
       check prop_left_distribution_holds
       check prop_right_distribution_holds
       check prop_sds_are_rationals
       check prop_sds_are_binary_rationals
       check prop_recip_is_trivial
--     check prop_division_with_integer_result_is_ok
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

-- Output conversion was wrong
-- round was wrong
