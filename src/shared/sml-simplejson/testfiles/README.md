# JSON Parsing Test Suite
A comprehensive test suite for RFC 7159 compliant JSON parsers

These test files come from the JSONTestSuite repository, created as an appendix to the article [Parsing JSON is a Minefield 💣](http://seriot.ch/parsing_json.php).

**/test\_parsing/**

The name of these files tell if their contents should be accepted or rejected.

- `y_` content must be accepted by parsers
- `n_` content must be rejected by parsers
- `i_` parsers are free to accept or reject content

**/test\_transform/**

These files contain weird structures and characters that parsers may understand differently, eg:

- huge numbers
- dictionaries with similar keys
- NULL characters
- escaped invalid strings

