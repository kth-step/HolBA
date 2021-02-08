
Simple Standard ML JSON parser
==============================

https://hg.sr.ht/~cannam/sml-simplejson

An RFC-compliant JSON parser in one SML file (json.sml) with no
dependency on anything outside the Basis library. Also includes a
simple serialiser.

Tested with MLton, Poly/ML, and SML/NJ compilers.

Parser notes:

 * Complies with RFC 7159, The JavaScript Object Notation (JSON)
   Data Interchange Format

 * Passes all of the JSONTestSuite parser accept/reject tests that
   exist at the time of writing, as listed in "Parsing JSON is a
   Minefield" (http://seriot.ch/parsing_json.php)
 
 * Two-pass parser using naive exploded strings, therefore not
   particularly fast and not suitable for large input files

 * Only supports UTF-8 input, not UTF-16 or UTF-32. Doesn't check
   that JSON strings are valid UTF-8 -- the caller must do that --
   but does handle \u escapes

 * Converts all numbers to type "real". If that is a 64-bit IEEE
   float type (common but not guaranteed in SML) then we're pretty
   standard for a JSON parser

 * For simplicity this implementation returns object fields in the
   order in which they appear in the input, without checking for
   duplicates. But JSON object fields are unordered, so callers
   should take care not to accidentally rely on this

Copyright 2017 Chris Cannam.
Parts based on the JSON parser in the Ponyo library by Phil Eaton.

MIT/X11 licence. See the file COPYING for details.
