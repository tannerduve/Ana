"""Shared pinned Lean JSON compact codec for independent evaluation evidence.

Extracted unchanged from the journal auditor. This is not a general JSON
canonicalization standard; decimal representation limits and the pinned tiny-zero
printer refusal are deliberate. Existing audit imports remain re-exported.
"""
from decimal import Decimal
import json

class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def _quote(value):
    pieces = ['"']
    special = {'"': '\\"', '\\': '\\\\', '\n': '\\n', '\r': '\\r'}
    for char in value:
        code = ord(char)
        require(not 0xD800 <= code <= 0xDFFF, "non-scalar JSON string")
        pieces.append(special.get(char, f"\\u{code:04x}" if code < 32 else char))
    pieces.append('"')
    return "".join(pieces)


def _number(value):
    """Pinned Lean 4.33.1 JsonNumber printer, preserving decimal precision."""
    require(value.is_finite(), "non-finite JSON number")
    sign, digits, exponent = value.as_tuple()
    magnitude = "".join(map(str, digits)).lstrip("0") or "0"
    sign = "-" if sign and magnitude != "0" else ""
    if exponent >= 0:
        require(len(magnitude) + exponent <= 8192, "JSON number exceeds audit size bound")
        return sign + (magnitude + "0" * exponent if magnitude != "0" else "0")
    places = -exponent
    shifted = min(0, 9 + len(magnitude) - places)
    decimal_places = places + shifted
    require(decimal_places <= 1024 * 1024, "JSON number exceeds audit size bound")
    whole = magnitude[:-decimal_places] if len(magnitude) > decimal_places else "0"
    fraction = magnitude[-decimal_places:].rjust(decimal_places, "0").rstrip("0")
    if not fraction and shifted == 0:
        return sign + whole
    # The pinned upstream printer emits invalid 0.e-N for tiny scaled zeros.
    # Refuse it instead of blessing an invalid JSON journal or hiding the defect.
    require(bool(fraction), "pinned Lean printer has invalid tiny-zero serialization")
    return sign + whole + "." + fraction + ("e" + str(shifted) if shifted else "")


def compact(value):
    if value is None:
        return "null"
    if type(value) is bool:
        return "true" if value else "false"
    if type(value) is int:
        # Decimal(int) is exact and avoids Python's global int/string digit cap.
        return _number(Decimal(value))
    if isinstance(value, Decimal):
        return _number(value)
    if isinstance(value, str):
        return _quote(value)
    if isinstance(value, list):
        return "[" + ",".join(compact(item) for item in value) + "]"
    if isinstance(value, dict):
        require(all(isinstance(key, str) for key in value), "non-string JSON key")
        return "{" + ",".join(_quote(key) + ":" + compact(value[key]) for key in sorted(value)) + "}"
    raise AuditError("unsupported JSON value; parse noninteger numbers exactly with Decimal")


def _loads(text):
    def invalid_constant(value):
        raise AuditError("non-finite JSON number: " + value)
    def integer(token):
        require(len(token.lstrip("-")) <= 8192, "JSON integer exceeds audit size bound")
        return int(Decimal(token))
    return json.loads(text, parse_int=integer, parse_float=Decimal, parse_constant=invalid_constant)
