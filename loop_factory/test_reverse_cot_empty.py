#!/usr/bin/env python3
"""Diagnostics for reverse_cot empty-output behavior."""

import types
import unittest

import reverse_cot


class _FakeCompletions:
    def __init__(self, responses):
        self._responses = list(responses)
        self.calls = 0

    def create(self, **kwargs):
        if self.calls < len(self._responses):
            r = self._responses[self.calls]
        else:
            r = self._responses[-1]
        self.calls += 1
        return r


class _FakeClient:
    def __init__(self, responses):
        self.chat = types.SimpleNamespace(
            completions=_FakeCompletions(responses)
        )


def _mk_resp(content, finish_reason="stop"):
    msg = types.SimpleNamespace(content=content)
    choice = types.SimpleNamespace(message=msg, finish_reason=finish_reason)
    return types.SimpleNamespace(choices=[choice])


class TestReverseCotEmpty(unittest.TestCase):
    def test_empty_content_with_length_finish_reason_returns_empty(self):
        """Reproduce logs: finish_reason=length + empty content => empty COT."""
        client = _FakeClient([
            _mk_resp("", "length"),
            _mk_resp("", "length"),
            _mk_resp("", "length"),
        ])
        out = reverse_cot.generate_reverse_cot(
            system_prompt="ctx",
            user_prompt="q",
            code_output="int main(){while(i<n){i++;}}",
            client=client,
            model="dummy",
            max_retries=3,
        )
        self.assertEqual(out, "")
        self.assertEqual(client.chat.completions.calls, 3)

    def test_non_empty_plain_text_succeeds(self):
        client = _FakeClient([_mk_resp("I track i and n, then derive bounds.", "stop")])
        out = reverse_cot.generate_reverse_cot(
            system_prompt="ctx",
            user_prompt="q",
            code_output="int main(){while(i<n){i++;}}",
            client=client,
            model="dummy",
            max_retries=3,
        )
        self.assertTrue(out.strip())
        self.assertIn("track", out.lower())


if __name__ == "__main__":
    unittest.main()
