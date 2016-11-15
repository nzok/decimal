module Scaled (
    Scaled(..),
    ceilingTo,
    floorTo,
    roundTo,
    truncateTo
) where
import Ratio ((%))

class Integral a => Scaled a
  where
    scale :: a -> Int
    scale _ = 0
    ratio :: a -> a -> Rational
    ratio x y = fromIntegral x % (fromIntegral y :: Integer)

instance Scaled Int

instance Scaled Integer

truncateTo, floorTo, ceilingTo, roundTo :: Real a => a -> a -> a
helper :: Real a => (Rational -> Integer) -> a -> a -> a

helper f x y = fromIntegral (f (toRational x / toRational y)) * y
truncateTo = helper truncate
floorTo    = helper floor
ceilingTo  = helper ceiling
roundTo    = helper round
