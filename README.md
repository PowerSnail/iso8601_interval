# Parsing ISO 8601 time interval into chrono DateTime

It is a small addition to the `chrono` crate, parsing ISO 8601 time interval [^wiki] into [`IsoInterval`] which contains a pair of `DateTime` objects, that respectively mark the 
beginning and end of the interval.

This utility is missing in `chrono` possibly due to the fuzziness of duration, which can be specified against year and month, so the time passed is inherently not absolute.

Interval is absolute in that regard, because when a starting or end point is fixed, the exact number of seconds passed can be calculated.

The dates, as parsed, are in `FixedOffset` time zone, and can be switched out by calling [`IsoInterval::with_time_zone`].

[^wiki]: <https://en.wikipedia.org/wiki/ISO_8601#Time_intervals>