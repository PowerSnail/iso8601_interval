use std::{
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
    sequence::{pair, preceded, separated_pair, terminated, tuple},
    IResult, Parser,
};
use thiserror::Error;

pub struct IsoInterval<Tz: TimeZone> {
    pub from: DateTime<Tz>,
    pub to: DateTime<Tz>,
}

impl<Tz: TimeZone> IsoInterval<Tz> {
    pub fn from_range(from: DateTime<Tz>, to: DateTime<Tz>) -> Self {
        IsoInterval { from, to }
    }

    fn from_duration(from: DateTime<Tz>, duration: IsoDuration) -> Self {
        let to = from.clone() + &duration;
        Self::from_range(from, to)
    }

    pub fn with_time_zone<TzTo: TimeZone>(&self, tz: &TzTo) -> IsoInterval<TzTo> {
        IsoInterval::from_range(self.from.with_timezone(tz), self.to.with_timezone(tz))
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

#[derive(Error, Debug)]
#[error("{msg}")]
pub struct ParseIntervalError {
    msg: String,
}

struct IsoDuration {
    year: i64,
    month: i64,
    day: i64,
    hour: i64,
    minute: i64,
    second: i64,
}

trait IsoDurationAddable {
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

fn parse_duration(i: &str) -> IResult<&str, IsoDuration> {
    let (i, (year, month, day)) = preceded(
        char('P'),
        tuple((
            map(opt(terminated(parse_i64, char('Y'))), |v| v.unwrap_or(0)),
            map(opt(terminated(parse_i64, char('M'))), |v| v.unwrap_or(0)),
            map(opt(terminated(parse_i64, char('D'))), |v| v.unwrap_or(0)),
        )),
    )(i)?;

    let (i, (hour, minute, second)) = or_default(
        (0, 0, 0),
        preceded(
            char('T'),
            tuple((
                or_default(0, terminated(parse_i64, char('H'))),
                or_default(0, terminated(parse_i64, char('M'))),
                or_default(0, terminated(parse_i64, char('S'))),
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
        },
    ))
}

fn parse_i64(i: &str) -> IResult<&str, i64> {
    map_res(recognize(pair(opt(char('-')), digit1)), |s: &str| {
        s.parse::<i64>()
    })(i)
}

pub fn or_default<I: Clone, O: Clone, E: ParseError<I>, F>(
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
    use chrono::{Datelike, Timelike};

    use crate::IsoInterval;

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
}