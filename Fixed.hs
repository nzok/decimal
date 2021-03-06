{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances   #-}

module Fixed (
 -- type classes
    Has_Radix(..),
 -- types
    Binary,
    Decimal,
    Fixed(..),
    Fixed_Frame(..),
    Result_Scale(..),
    Rounding_Mode(..),
    Scale(..),
 -- functions
    scale,
    shift,
    toFixed,
    align,
    lia_divides,    lia_gcd,    lia_lcm,
    lia_signum,
    lia_dim,
    convert,
    rescale,
    convertFixed,
    quotient,
    fit,
    divide,
    readFixedDecimal
) where

import Numeric (showSigned)
import Data.Char (isDigit)
import Data.Ratio

data Binary
data Decimal

class Has_Radix t
  where radix :: t -> Integer

instance Has_Radix Binary
  where radix _ = 2

instance Has_Radix Decimal
  where radix _ = 10

newtype Scale t = Scale Integer
                  deriving (Eq, Ord, Show, Num)

shift :: forall t . Has_Radix t => Integer -> Scale t -> Integer
shift m (Scale p) =
  if p >= 0 then m * radix (undefined :: t) ^ p
  else m `quot` radix (undefined :: t) ^ negate p

data Fixed t = FP !Integer !(Scale t)

scale :: forall t . Has_Radix t => Fixed t -> Scale t
scale (FP _ s) = s

ulp :: Has_Radix t => Fixed t -> Fixed t
ulp (FP _ s) = FP 1 s

toFixed :: Has_Radix t => Integer -> Scale t -> Fixed t
toFixed n s = FP (shift n s) s

align :: forall t a . Has_Radix t =>
    Fixed t -> Fixed t -> (Integer -> Integer -> a) -> a

align (FP m1 s1) (FP m2 s2) f
  | s1 > s2 = f m1 (shift m2 (s1-s2))
  | s1 < s2 = f (shift m1 (s2-s1)) m2
  | True    = f m1 m2

instance (Has_Radix t) => Eq (Fixed t)
  where x1 == x2 = align x1 x2 (==)

  -- automatically defines /=

instance (Has_Radix t) => Ord (Fixed t)
  where compare x1 x2 = align x1 x2 compare

  -- automatically defines < <= > >= max min

lia_divides :: Has_Radix t => Fixed t -> Fixed t -> Bool
lia_divides x y = align x y (\m n -> m /= 0 && n`rem`m == 0)

lia_gcd :: Has_Radix t => Fixed t -> Fixed t -> Fixed t
lia_gcd x y = FP (align x y gcd) (scale x `max` scale y)

lia_lcm :: Has_Radix t => Fixed t -> Fixed t -> Fixed t
lia_lcm x y = FP (align x y lcm) (scale x `max` scale y)

instance (Has_Radix t) => Show (Fixed t)
  where
    showsPrec p x = showSigned showPos p x
      where showPos x@(FP m s) rest =
              if s <= 0 then shows (shift m (negate s)) rest
              else shows i ('.' : show_fract s r)
              where p = shift 1 s
                    (i,r) = quotRem m p
                    show_fract 0 _ = rest
                    show_fract d f = shows h (show_fract (d-1) l)
                      where (h,l) = quotRem (10 * f) p


instance (Has_Radix t) => Num (Fixed t)
  where
    x + y = FP (align x y (+)) (scale x `max` scale y)
    x - y = FP (align x y (-)) (scale x `max` scale y)
    negate (FP m s) = FP (negate m) s
    abs    (FP m s) = FP (abs    m) s
    signum (FP m s) = FP (signum m) 0
    fromInteger n   = FP n 0
    (FP m1 s1) * (FP m2 s2)  = FP (m1*m2) (s1+s2)

lia_signum :: (Ord t, Num t) => t -> t
lia_signum x = if x < 0 then -1 else 1

lia_dim :: (Ord t, Num t) => t -> t -> t
lia_dim x y = if x < y then fromInteger 0 else x - y

instance (Has_Radix t) => Real (Fixed t)
  where
    toRational (FP m s) =
      if s >= 0 then m % (shift 1 s) else (shift m (negate s)) % 1

-- Integral has
  -- quotRem, quot, rem
  -- divMod, div, mod
  -- toInteger

instance (Has_Radix t) => Enum (Fixed t)
  where
    succ (FP m s) = FP (succ m) s
    pred (FP m s) = FP (pred m) s
    toEnum n      = FP (fromIntegral n) 0
    fromEnum (FP m s) = fromIntegral m

instance (Has_Radix t) => Integral (Fixed t)
  where
    quotRem x y = (q, x - q*y) where q = FP (align x y quot) 0
    divMod  x y = (q, x - q*y) where q = FP (align x y div ) 0
    toInteger x@(FP m s) =
      if s > 0 then m `div` (shift 1 s) else shift m (negate s)

-- Fractional has
  -- / recip fromRational

-- RealFrac has
  -- properFraction   :: (Integral b) => a -> (b,a)
  -- properFraction x = i f   such that i integral, i+f = x
  -- truncate, round  :: (Integral b) => a -> b
  -- round is round to even
  -- ceiling, floor   :: (Integral b) => a -> b

data Rounding_Mode
   = Down
   | Up
   | In
   | Out
   | Exact
   | Even
   | Nearest Rounding_Mode

convert :: RealFrac t => Rounding_Mode -> t -> Integer

convert round x =
  case round of
    Down      -> if d < 0 then i-1 else i
    Up        -> if d > 0 then i+1 else i
    In        -> i
    Out       -> i + d
    Exact     -> if d == 0 then i else error "inexact"
    Even      -> if even i then i else
                 if d /= 0 then i + d else
                 if (i + 1 `mod` 4) == 0 then i+1 else i-1
    Nearest h -> if d == 0 then i else
                 case compare (2*abs f) 1 of
                   LT -> i
                   GT -> i + d
                   EQ -> i + convert h f
  where (i,f) = properFraction x
        d     = if f < 0 then -1 else if f > 0 then 1 else 0

rescale :: forall t r . (Has_Radix t, Real r) =>
           Rounding_Mode -> Integer -> r -> Fixed t

rescale round digits x = FP (convert round y) (Scale digits)
  where y = toRational x * toRational (radix (undefined :: t) ^ digits)

convertFixed :: Has_Radix t =>
    Rounding_Mode -> Fixed t -> (Integer, Fixed t)

convertFixed round x = (q, x - fromInteger q)
  where q = convert round (toRational x)

quotient :: Has_Radix t =>
    Rounding_Mode -> Fixed t -> Fixed t ->
    (Integer, Fixed t)
quotient round x y = (q, x - fromInteger q * y)
  where q = convert round (toRational x / toRational y)

data Result_Scale
   = Exact_Scale   !Integer
   | Maximum_Scale !Integer

data -- Has_Radix t =>
     Fixed_Frame t = Fixed_Frame !Result_Scale !Rounding_Mode
                                 !(Maybe (Integer, Integer))

fit :: Has_Radix t =>
    Fixed_Frame t -> Fixed t -> Fixed t
fit (Fixed_Frame rs round bounds) x@(FP m (Scale s))
  = check_bounds bounds m' y
  where
    y@(FP m' _) =
      case rs of
        Exact_Scale e   -> if e == s then x else
                           rescale round e x
        Maximum_Scale e -> if e >= s then x else
                           rescale round e x

check_bounds :: Ord t => Maybe (t,t) -> t -> r -> r

check_bounds Nothing      _ y = y
check_bounds (Just (l,u)) x y =
  if l <= x && x <= u then y else error "overflow"

divide :: forall t u v . (Has_Radix t, Real u, Real v) =>
          Fixed_Frame t -> u -> v -> Fixed t
divide (Fixed_Frame rs round bounds) x y
  = check_bounds bounds m (FP m (Scale s))
  where
    s = case rs of
          (Exact_Scale   z) -> z
          (Maximum_Scale z) -> z
    p = radix (undefined :: t) ^ s
    q = toRational x / toRational y
    m = convert round (q * fromInteger p)

readFixedDecimal :: ReadS (Fixed Decimal)

readFixedDecimal ('-':cs) = after_sign negate cs
readFixedDecimal cs       = after_sign id     cs

after_sign :: (Integer -> Integer) -> ReadS (Fixed Decimal)

after_sign f (c:cs)
  | isDigit c = after_digit f (add_digit 0 c) cs
after_sign _ _ = []

after_digit :: (Integer -> Integer) -> Integer ->
               ReadS (Fixed Decimal)

after_digit f n (c:cs)
  | isDigit c = after_digit f (add_digit n c) cs
after_digit f n ('.':c:cs)
  | isDigit c = after_dot f (Scale 1) (add_digit n c) cs
after_digit f n ('.':_) = []
after_digit f n cs = [(FP (f n) (Scale 0), cs)]

after_dot :: (Integer -> Integer) -> Scale Decimal -> Integer ->
             ReadS (Fixed Decimal)

after_dot f s n (c:cs)
  | isDigit c = after_dot f (s+1) (add_digit n c) cs
after_dot f s n cs = [(FP (f n) s, cs)]

add_digit :: Integer -> Char -> Integer

add_digit n c =
   n * 10 + fromIntegral (fromEnum c - fromEnum '0')

instance Read (Fixed Decimal)
  where
    readsPrec _ = readFixedDecimal

-- ReadS a = String -> [(a,String)]

