//! Type aliases for common uses

use typenum::op;
use typenum::NonZero;
use typenum::Unsigned;
use typenum::U1;
use typenum::U100;
use typenum::U1000;
use typenum::U1000000;
use typenum::U1000000000;
use typenum::U36;
use typenum::U60;

/// There are 3600 seconds in an hour
pub type U3600 = op!(U36 * U100);

use crate::Duration;
use crate::Instant;
use crate::Rate;

/// Alias for nanosecond duration
pub type NanosDuration<T> = Duration<T, U1, U1000000000>;

/// Alias for nanosecond duration (`u32` backing storage)
pub type NanosDurationU32 = Duration<u32, U1, U1000000000>;

/// Alias for nanosecond duration (`u64` backing storage)
pub type NanosDurationU64 = Duration<u64, U1, U1000000000>;

/// Alias for microsecond duration
pub type MicrosDuration<T> = Duration<T, U1, U1000000>;

/// Alias for microsecond duration (`u32` backing storage)
pub type MicrosDurationU32 = Duration<u32, U1, U1000000>;

/// Alias for microsecond duration (`u64` backing storage)
pub type MicrosDurationU64 = Duration<u64, U1, U1000000>;

/// Alias for millisecond duration
pub type MillisDuration<T> = Duration<T, U1, U1000>;

/// Alias for millisecond duration (`u32` backing storage)
pub type MillisDurationU32 = Duration<u32, U1, U1000>;

/// Alias for millisecond duration (`u64` backing storage)
pub type MillisDurationU64 = Duration<u64, U1, U1000>;

/// Alias for second duration
pub type SecsDuration<T> = Duration<T, U1, U1>;

/// Alias for second duration (`u32` backing storage)
pub type SecsDurationU32 = Duration<u32, U1, U1>;

/// Alias for second duration (`u64` backing storage)
pub type SecsDurationU64 = Duration<u64, U1, U1>;

/// Alias for minutes duration
pub type MinutesDuration<T> = Duration<T, U60, U1>;

/// Alias for minutes duration (`u32` backing storage)
pub type MinutesDurationU32 = Duration<u32, U60, U1>;

/// Alias for minutes duration (`u64` backing storage)
pub type MinutesDurationU64 = Duration<u64, U60, U1>;

/// Alias for hours duration
pub type HoursDuration<T> = Duration<T, U3600, U1>;

/// Alias for hours duration (`u32` backing storage)
pub type HoursDurationU32 = Duration<u32, U3600, U1>;

/// Alias for hours duration (`u64` backing storage)
pub type HoursDurationU64 = Duration<u64, U3600, U1>;

/// Alias for durations that come from timers with a specific frequency
pub type TimerDuration<T, FreqHz: Unsigned + NonZero> = Duration<T, U1, FreqHz>;

/// Alias for durations that come from timers with a specific frequency (`u32` backing storage)
pub type TimerDurationU32<FreqHz: Unsigned + NonZero> = Duration<u32, U1, FreqHz>;

/// Alias for durations that come from timers with a specific frequency (`u64` backing storage)
pub type TimerDurationU64<FreqHz: Unsigned + NonZero> = Duration<u64, U1, FreqHz>;

// -------------------------------

/// Alias for instants that come from timers with a specific frequency
pub type TimerInstant<T, FreqHz: Unsigned + NonZero> = Instant<T, U1, FreqHz>;

/// Alias for instants that come from timers with a specific frequency (`u32` backing storage)
pub type TimerInstantU32<FreqHz: Unsigned + NonZero> = Instant<u32, U1, FreqHz>;

/// Alias for instants that come from timers with a specific frequency (`u64` backing storage)
pub type TimerInstantU64<FreqHz: Unsigned + NonZero> = Instant<u64, U1, FreqHz>;

// -------------------------------

/// Alias for hertz rate
pub type Hertz<T> = Rate<T, U1, U1>;

/// Alias for hertz rate (`u32` backing storage)
pub type HertzU32 = Rate<u32, U1, U1>;

/// Alias for hertz rate (`u64` backing storage)
pub type HertzU64 = Rate<u64, U1, U1>;

/// Alias for kilohertz rate
pub type Kilohertz<T> = Rate<T, U1000, U1>;

/// Alias for kilohertz rate (`u32` backing storage)
pub type KilohertzU32 = Rate<u32, U1000, U1>;

/// Alias for kilohertz rate (`u64` backing storage)
pub type KilohertzU64 = Rate<u64, U1000, U1>;

/// Alias for megahertz rate
pub type Megahertz<T> = Rate<T, U1000000, U1>;

/// Alias for megahertz rate (`u32` backing storage)
pub type MegahertzU32 = Rate<u32, U1000000, U1>;

/// Alias for megahertz rate (`u64` backing storage)
pub type MegahertzU64 = Rate<u64, U1000000, U1>;

/// Alias for rate that come from timers with a specific frequency
pub type TimerRate<T, FreqHz: Unsigned + NonZero> = Rate<T, FreqHz, U1>;

/// Alias for rate that come from timers with a specific frequency (`u32` backing storage)
pub type TimerRateU32<FreqHz: Unsigned + NonZero> = Rate<u32, FreqHz, U1>;

/// Alias for rate that come from timers with a specific frequency (`u64` backing storage)
pub type TimerRateU64<FreqHz: Unsigned + NonZero> = Rate<u64, FreqHz, U1>;
