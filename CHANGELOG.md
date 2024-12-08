# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Removed

### Changed

The following `Duration` implementations are constrained to `PrimInt` instead of just u32/64,
when the bases are the same.

- `from_ticks`
- `ticks`
- `+`
- `+=`
- `-`
- `-=`

The following `Instant` implementations are constrained to `PrimInt` instead of just u32/64,
when the bases are the same.

- `from_ticks`
- `ticks`
- `Instant -= Duration`
- `Instant += Duration`

The following `Instant` implementations are constrained to `PrimInt` instead of just u32/64,
when the bases are the same.

- `raw`
- `from_raw`
- `-`
- `+`
- `+=`

### Fixed

`<Duration as defmt::Format>::format` is working again

### Added

## [v0.1.2]

### Added

`Period` struct to encapsulate tick-period in seconds

### Fixed

Constrained `Instant` so that you cannot erroniously have a 0-divisor for eth period

### Changed

`Instant` is encapsulated as a `Duration` since a reference.
`Duration` delegates tick-period length to the `Period` struct

## [v0.1.0]

### Added

### Fixed

### Changed

- Initial release of the `fugit` fork `typus_fugit`

