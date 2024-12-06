# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Added

### Fixed

`<Duration as defmt::Format>::format` is working again

### Changed

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

