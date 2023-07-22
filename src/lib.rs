//! # Parsing ISO 8601 time interval into chrono DateTime
//!
//! It is a small addition to the [`chrono`] crate, parsing ISO 8601 time interval [^wiki] into
//! [`IsoInterval`] which contains a pair of [`DateTime`] objects, that respectively mark the
//! beginning and end of the interval.
//!
//! [^wiki]: <https://en.wikipedia.org/wiki/ISO_8601#Time_intervals>
//!
//! This utility is missing in `chrono` possibly due to the fuzziness of duration, which can be
//! specified against year and month, so the time passed is inherently not absolute. Intervals, on
//! the other hand, are absolute in that regard, because when a starting or end point is fixed, the
//! exact number of seconds passed can be calculated.
//!
//! The dates, as parsed, are in [`chrono::FixedOffset`] time zone, and can be switched out
//! by calling [`IsoInterval::with_time_zone`].

use std::{
    fmt,
    fmt::{Display, Formatter},
    ops::{Add, Sub},
    str::FromStr,
};

use chrono::{DateTime, Days, Duration, FixedOffset, Months, TimeZone};
use nom::{
    branch::alt,
    bytes::complete::take_while,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt, recognize},
    error::ParseError,
    number::complete::recognize_float_parts,
    sequence::{pair, preceded, separated_pair, terminated, tuple},
    IResult, Parser,
};
use thiserror::Error;

/// An interval in time.
#[derive(Debug)]
pub struct IsoInterval<Tz: TimeZone> {
    /// The beginning of the interval
    pub from: DateTime<Tz>,

    /// The end of the interval
    pub to: DateTime<Tz>,
}

impl<Tz: TimeZone> IsoInterval<Tz> {
    /// Constructs an interval from the two ends
    pub fn from_range(from: DateTime<Tz>, to: DateTime<Tz>) -> Self {
        IsoInterval { from, to }
    }

    /// Constructs an interval from the beginning and the length of the duration
    pub fn from_duration(from: DateTime<Tz>, duration: IsoDuration) -> Self {
        let to = from.clone() + &duration;
        Self::from_range(from, to)
    }

    /// Convert the interval to a different time zone
    pub fn with_time_zone<TzTo: TimeZone>(&self, tz: &TzTo) -> IsoInterval<TzTo> {
        IsoInterval::from_range(self.from.with_timezone(tz), self.to.with_timezone(tz))
    }

    /// The real and absolute duration marked by this interval
    pub fn duration(&self) -> chrono::Duration {
        self.to.clone() - self.from.clone()
    }
}

impl FromStr for IsoInterval<FixedOffset> {
    type Err = ParseIntervalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parse_interval(s) {
            Ok((_, value)) => Ok(value),
            Err(e) => {
                let source_msg = e.to_string();
                let position = match e.map(|e| e.input.as_ptr() as usize - s.as_ptr() as usize) {
                    nom::Err::Incomplete(_) => 0,
                    nom::Err::Error(n) => n,
                    nom::Err::Failure(n) => n,
                };
                Err(ParseIntervalError {
                    msg: format!(
                        "Malformed Interval: \n\t{}\n\t{}^\n{}",
                        &s,
                        " ".repeat(position),
                        source_msg
                    ),
                })
            }
        }
    }
}

/// Error of parsing
#[derive(Error, Debug)]
#[error("{msg}")]
pub struct ParseIntervalError {
    msg: String,
}

/// Duration specified according to ISO 8601, in years, months, days, hours, minutes, and seconds.
/// Seconds field can have fractional part, up to nanosecond precision.
///
/// This instance of duration is not an absolute measurement of time, due to the fact that months
/// and years can have different number of days.
/// Restriction: Only the seconds field can have fraction, but no other field can. ISO 8601 allows any field to have fraction, if it is last.

#[derive(Debug, Default, PartialEq, Eq)]
pub struct IsoDuration {
    year: i64,
    month: i64,
    day: i64,
    hour: i64,
    minute: i64,
    second: i64,
    nanos: i64,
}

#[allow(dead_code)]
impl IsoDuration {
    fn new(
        year: i64,
        month: i64,
        day: i64,
        hour: i64,
        minute: i64,
        second: i64,
        nanos: i64,
    ) -> Self {
        IsoDuration {
            year,
            month,
            day,
            hour,
            minute,
            second,
            nanos,
        }
    }
}

impl Display for IsoDuration {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        //write!(f, "{}", self.)
        //todo: handle case all fields zero -> PD0

        if self == &IsoDuration::default() {
            write!(f, "PT0S")?; // an arbitrary choice from among the many ways to represent 0 duration.
        } else {
            write!(f, "P")?;
            if self.year != 0 {
                write!(f, "{}Y", self.year)?;
            };
            if self.month != 0 {
                write!(f, "{}M", self.month)?;
            };
            if self.day != 0 {
                write!(f, "{}D", self.day)?;
            };
            if self.hour != 0 || self.minute != 0 || self.second != 0 || self.nanos != 0 {
                write!(f, "T")?;
                if self.hour != 0 {
                    write!(f, "{}H", self.hour)?;
                };
                if self.minute != 0 {
                    write!(f, "{}M", self.minute)?;
                };
                if self.second != 0 || self.nanos != 0 {
                    if self.nanos != 0 {
                        // want to display nanos as fraction after seconds, must fix it so nanos portion doesn't display its own leading negative sign
                        if self.second >= 0 && self.nanos >= 0 {
                            write!(f, "{}.{:09}S", self.second, self.nanos)?;
                        } else if self.second < 0 && self.nanos < 0 {
                            write!(f, "{}.{:09}S", self.second, -self.nanos)?;
                        } else {
                            // mixed signs -- rely on bigint arithmetic to borrow and carry between the 2 variables
                            let real_nanos: i128 =
                                (self.second * 1_000_000_000 + self.nanos).into();
                            if real_nanos < 0 {
                                let real_second = real_nanos / 1_000_000_000;
                                if real_second == 0 {
                                    write!(f, "-0.{:09}S", -real_nanos % 1_000_000_000)?;
                                } else {
                                    write!(
                                        f,
                                        "{}.{:09}S",
                                        real_second,
                                        -real_nanos % 1_000_000_000
                                    )?;
                                }
                            } else {
                                write!(
                                    f,
                                    "{}.{:09}S",
                                    real_nanos / 1_000_000_000,
                                    real_nanos % 1_000_000_000
                                )?;
                            }
                        }
                    } else {
                        write!(f, "{}S", self.second)?;
                    }
                }
            }
        }
        Ok(())
    }
}

/// Things that can take durations for adding and subtracting.
pub trait IsoDurationAddable {
    fn add(value: Self, duration: IsoDuration) -> Self;
}

impl<Tz: TimeZone> Add<&IsoDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn add(self, rhs: &IsoDuration) -> Self::Output {
        let mut date = self;
        let n_months = rhs.year * 12 + rhs.month;
        if n_months >= 0 {
            date = date + Months::new(n_months as u32);
        } else {
            date = date - Months::new(-n_months as u32);
        }
        if rhs.day > 0 {
            date = date + Days::new(rhs.day as u64);
        } else {
            date = date - Days::new(-rhs.day as u64);
        }
        date = date + Duration::seconds(rhs.second + rhs.minute * 60 + rhs.hour * 3600);
        date = date + Duration::nanoseconds(rhs.nanos);
        date
    }
}

impl<Tz: TimeZone> Sub<&IsoDuration> for DateTime<Tz> {
    type Output = DateTime<Tz>;

    fn sub(self, rhs: &IsoDuration) -> Self::Output {
        let mut date = self;
        let n_months = rhs.year * 12 + rhs.month;
        if n_months >= 0 {
            date = date - Months::new(n_months as u32);
        } else {
            date = date + Months::new(-n_months as u32);
        }
        if rhs.day > 0 {
            date = date - Days::new(rhs.day as u64);
        } else {
            date = date + Days::new(-rhs.day as u64);
        }
        date = date - Duration::seconds(rhs.second + rhs.minute * 60 + rhs.hour * 3600);
        date = date - Duration::nanoseconds(rhs.nanos);
        date
    }
}

fn parse_interval(i: &str) -> IResult<&str, IsoInterval<FixedOffset>> {
    alt((
        map(
            separated_pair(parse_duration, char('/'), parse_datetime),
            |(duration, to)| IsoInterval::from_duration(to - &duration, duration),
        ),
        map(
            separated_pair(parse_datetime, char('/'), parse_duration),
            |(from, duration)| IsoInterval::from_duration(from, duration),
        ),
        map(
            separated_pair(parse_datetime, char('/'), parse_datetime),
            |(from, to)| IsoInterval::from_range(from, to),
        ),
    ))(i)
}

fn parse_datetime(i: &str) -> IResult<&str, DateTime<FixedOffset>> {
    map_res(take_while(|c| c != '/'), |s| {
        DateTime::parse_from_rfc3339(s)
    })(i)
}

fn parse_seconds(i: &str) -> IResult<&str, (i64, i64)> {
    let (residue, (sign, sec_str, ns_str, _exp)) = recognize_float_parts(i)?;
    let mut sec = sec_str.parse::<i64>().unwrap_or_default();
    if !sign {
        sec = -sec;
    };
    if ns_str.len() > 0 {
        let ns = (ns_str.to_string() + "000000000")[..9]
            .parse::<u32>()
            .unwrap_or_default();
        return Ok((
            residue,
            (sec, (if sign { ns as i64 } else { -(ns as i64) })),
        ));
    }
    return Ok((residue, (sec, 0)));
}

fn parse_duration(i: &str) -> IResult<&str, IsoDuration> {
    let (i, (year, month, day)) = preceded(
        char('P'),
        tuple((
            map(opt(terminated(parse_i64, char('Y'))), |v| v.unwrap_or(0)),
            map(opt(terminated(parse_i64, char('M'))), |v| v.unwrap_or(0)),
            map(opt(terminated(parse_i64, char('D'))), |v| v.unwrap_or(0)),
        )),
    )(i)?;

    let (i, (hour, minute, (second, nanos))) = or_default(
        (0, 0, (0, 0)),
        preceded(
            char('T'),
            tuple((
                or_default(0, terminated(parse_i64, char('H'))),
                or_default(0, terminated(parse_i64, char('M'))),
                or_default((0, 0), terminated(parse_seconds, char('S'))),
            )),
        ),
    )(i)?;

    Ok((
        i,
        IsoDuration {
            year,
            month,
            day,
            hour,
            minute,
            second,
            nanos: if second < 0 { -nanos } else { nanos },
        },
    ))
}

fn parse_i64(i: &str) -> IResult<&str, i64> {
    map_res(recognize(pair(opt(char('-')), digit1)), |s: &str| {
        s.parse::<i64>()
    })(i)
}

fn or_default<I: Clone, O: Clone, E: ParseError<I>, F>(
    val: O,
    mut parser: F,
) -> impl FnMut(I) -> IResult<I, O, E>
where
    F: Parser<I, O, E>,
{
    move |input: I| {
        let i = input.clone();
        parser.parse(i).or(Ok((input, val.clone())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;
    use chrono::{Datelike, Timelike};
    use rstest::rstest;

    #[test]
    fn interval_form1() {
        let interval1: IsoInterval<_> = "2003-02-15T00:00:00Z/P2M".parse().unwrap();
        assert_eq!(interval1.from.year(), 2003);
        assert_eq!(interval1.from.month(), 2);
        assert_eq!(interval1.from.day(), 15);
        assert_eq!(interval1.from.hour(), 0);
        assert_eq!(interval1.from.minute(), 0);
        assert_eq!(interval1.from.second(), 0);

        assert_eq!(interval1.to.year(), 2003);
        assert_eq!(interval1.to.month(), 4);
        assert_eq!(interval1.to.day(), 15);
        assert_eq!(interval1.to.hour(), 0);
        assert_eq!(interval1.to.minute(), 0);
        assert_eq!(interval1.to.second(), 0);

        let interval2: IsoInterval<_> = "2007-03-01T13:00:00Z/P1Y2M10DT2H30M".parse().unwrap();
        assert_eq!(interval2.from.year(), 2007);
        assert_eq!(interval2.from.month(), 3);
        assert_eq!(interval2.from.day(), 1);
        assert_eq!(interval2.from.hour(), 13);
        assert_eq!(interval2.from.minute(), 0);
        assert_eq!(interval2.from.second(), 0);

        assert_eq!(interval2.to.year(), 2008);
        assert_eq!(interval2.to.month(), 5);
        assert_eq!(interval2.to.day(), 11);
        assert_eq!(interval2.to.hour(), 15);
        assert_eq!(interval2.to.minute(), 30);
        assert_eq!(interval2.to.second(), 00);
    }

    #[test]
    fn form2() {
        let interval2: IsoInterval<_> =
            "2007-03-01T13:00:00Z/2008-05-11T15:30:00Z".parse().unwrap();
        assert_eq!(interval2.from.year(), 2007);
        assert_eq!(interval2.from.month(), 3);
        assert_eq!(interval2.from.day(), 1);
        assert_eq!(interval2.from.hour(), 13);
        assert_eq!(interval2.from.minute(), 0);
        assert_eq!(interval2.from.second(), 0);

        assert_eq!(interval2.to.year(), 2008);
        assert_eq!(interval2.to.month(), 5);
        assert_eq!(interval2.to.day(), 11);
        assert_eq!(interval2.to.hour(), 15);
        assert_eq!(interval2.to.minute(), 30);
        assert_eq!(interval2.to.second(), 00);
    }

    #[test]
    fn form3() {
        let interval2: IsoInterval<_> = "P1Y2M10DT2H30M/2008-05-11T15:30:00Z".parse().unwrap();
        assert_eq!(interval2.from.year(), 2007);
        assert_eq!(interval2.from.month(), 3);
        assert_eq!(interval2.from.day(), 1);
        assert_eq!(interval2.from.hour(), 13);
        assert_eq!(interval2.from.minute(), 0);
        assert_eq!(interval2.from.second(), 0);

        assert_eq!(interval2.to.year(), 2008);
        assert_eq!(interval2.to.month(), 5);
        assert_eq!(interval2.to.day(), 11);
        assert_eq!(interval2.to.hour(), 15);
        assert_eq!(interval2.to.minute(), 30);
        assert_eq!(interval2.to.second(), 00);
    }

    #[rstest]
    #[case("2007-03-01T13:00:00Z/P1Y2M10DT2H30M", 0, 0)]
    #[case("2007-03-01T13:00:00Z/P1Y2M10DT2H30M10S", 10, 0)]
    #[case("2007-03-01T13:00:00Z/P1Y2M10DT2H30M10.304S", 10, 304_000_000)]
    #[case("2007-03-01T13:00:00Z/PT-3H+10.304S", 10, 304_000_000)]
    #[case("2007-03-01T13:00:00Z/PT3H-10.304S", 50, 304_000_000)]
    // neg sec in duration borrows from the end dt minute as needed
    // bugbug: ns portion should be negative!
    #[case("2007-03-01T13:00:00Z/PT0.000000304S", 0, 304)]
    #[case("2007-03-01T13:00:00Z/PT0.0000304S", 0, 30400)]

    fn sec_ns(#[case] instr: &str, #[case] exp_sec: u32, #[case] exp_ns: u32) {
        let obs_dur: IsoInterval<_> = instr.parse().unwrap();
        assert_eq!(exp_sec, obs_dur.to.second(), "exp sec != obs sec");
        assert_eq!(exp_ns, obs_dur.to.nanosecond(), "exp ns != obs ns");
    }

    #[rstest]
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 0, 0), "PT0S")]
    #[case(IsoDuration::new(0,0,-3,0,0,0,0), "P-3D")]
    #[case(IsoDuration::new(2023, 12, 11, 0, 0, 0, 0), "P2023Y12M11D")] // don't display HMS if not non-zero
    #[case(IsoDuration::new(-1, -2, -3, -4, -5, -6, -7), "P-1Y-2M-3DT-4H-5M-6.000000007S")]
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 1, 0), "PT1S")] // no nanoseconds if they're zero
    #[case(IsoDuration::new(0, 0, 0, 0, 0, -1, 0), "PT-1S")] // no nanoseconds if they're zero (negative)
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 1, 1), "PT1.000000001S")] // try all the nanosecond display edge cases
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 1, -1), "PT0.999999999S")]
    #[case(IsoDuration::new(0, 0, 0, 0, 0, -1, 1), "PT-0.999999999S")] //x
    #[case(IsoDuration::new(0, 0, 0, 0, 0, -1, -1), "PT-1.000000001S")]
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 0, -1), "PT-0.000000001S")] //x
    #[case(IsoDuration::new(0, 0, 0, 0, 0, -2, 1), "PT-1.999999999S")]
    #[case(IsoDuration::new(0, 0, 0, 0, 0, 2, -1), "PT1.999999999S")]

    fn display_iso_duration(#[case] in_dur: IsoDuration, #[case] expect: &str) {
        assert_eq!(expect, &in_dur.to_string(), "expected :: observed");
    }

    #[rstest]
    #[case("2020-01-01T00:00:00Z", &IsoDuration::new(0,0,0,0,0,0,1), "2020-01-01T00:00:00.000000001Z")]
    #[case("2020-01-01T00:00:00Z", &IsoDuration::new(0,0,0,0,0,0,1_000_000_000 + 1), "2020-01-01T00:00:01.000000001Z")] // nanoseconds carries to seconds as needed

    fn dt_add_duration(
        #[case] start: &str,
        #[case] addend: &IsoDuration,
        #[case] exp: &str,
    ) -> Result<(), Box<dyn Error>> {
        let start_dt = DateTime::parse_from_rfc3339(start)?;
        let exp_dt = DateTime::parse_from_rfc3339(exp)?;
        assert_eq!(start_dt + addend, exp_dt);

        Ok(())
    }
}
