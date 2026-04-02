"""
bot.py — Poker Bot Skeleton

All networking, parsing, and game-state tracking is handled for you.
Your ONLY job is to implement the `decide()` function at the bottom.

Usage:
    python bot.py [--host HOST] [--port PORT] [--name NAME]

You receive:
    state  — a GameState object with everything you need (see below)

You return one of:
    "fold"
    "check"         (only valid when to_call == 0)
    "call"
    "allin"
    ("raise", amount)   ← amount is the total bet level you want to set
"""

import socket
import json
import argparse
import random

# ─────────────────────────────────────────────
# GAME STATE OBJECT  (read-only, given to you)
# ─────────────────────────────────────────────

class GameState:
    """Everything you could ever want to know about the current decision."""

    def __init__(self, raw: dict, history: list, my_pid: int):
        # ── Identity ─────────────────────────
        self.my_pid        = my_pid

        # ── Cards ────────────────────────────
        self.hole_cards    = raw["hole_cards"]      # e.g. ["Ah","Kd"]
        self.community     = raw["community"]       # e.g. ["2c","7h","Td"]  (0–5 cards)
        self.street        = raw["street"]          # "preflop" | "flop" | "turn" | "river"

        # ── Money ────────────────────────────
        self.chips         = raw["chips"]           # your remaining chips
        self.pot           = raw["pot"]             # total pot size
        self.to_call       = raw["to_call"]         # chips you must add to call
        self.current_bet   = raw["current_bet"]     # highest bet this street
        self.min_raise     = raw["min_raise"]       # minimum legal raise total

        # ── Table ────────────────────────────
        self.num_players   = raw["num_players"]     # players in this hand
        self.player_bets   = raw["player_bets"]     # {pid: bet} this street
        self.player_chips  = raw["player_chips"]    # {pid: chips}
        self.player_folded = raw["player_folded"]   # {pid: bool}
        self.player_allin  = raw["player_allin"]    # {pid: bool}

        # ── History ──────────────────────────
        self.history       = history                # list of past action dicts

    # ── Derived helpers ──────────────────────

    @property
    def can_check(self):
        return self.to_call == 0

    @property
    def active_opponents(self):
        """Number of players still in the hand (not folded, not me)."""
        return sum(1 for pid, folded in self.player_folded.items()
                   if not folded and str(pid) != str(self.my_pid))

    @property
    def pot_odds(self):
        """Fraction of pot you need to invest to call (0.0 if check is free)."""
        if self.to_call == 0:
            return 0.0
        return self.to_call / (self.pot + self.to_call)

    @property
    def all_cards(self):
        """Your hole cards + community cards."""
        return self.hole_cards + self.community

    def __repr__(self):
        return (f"<GameState street={self.street} "
                f"hole={self.hole_cards} community={self.community} "
                f"pot={self.pot} chips={self.chips} to_call={self.to_call}>")


# ─────────────────────────────────────────────
# ════════════════════════════════════════════
#   YOUR BOT LOGIC — EDIT ONLY THIS SECTION
# ════════════════════════════════════════════
# ─────────────────────────────────────────────

from itertools import combinations as _combinations
from collections import Counter as _Counter

# ══════════════════════════════════════════════════════════════
#   CARD UTILITIES
# ══════════════════════════════════════════════════════════════

_RANKS = "23456789TJQKA"   # index 0 = 2, index 12 = Ace

def _parse_card(card_str):
    """Parse "Ah" → (rank_int 0-12, suit_char).  Returns None on any error."""
    try:
        return (_RANKS.index(card_str[0]), card_str[1])
    except (IndexError, ValueError, TypeError):
        return None

def _parse_cards(card_list):
    """Parse a list of card strings, silently dropping unparseable entries."""
    result = []
    for c in (card_list or []):
        p = _parse_card(c)
        if p is not None:
            result.append(p)
    return result


# ══════════════════════════════════════════════════════════════
#   DRAW DETECTOR
#
#   Detects incomplete hands that have strong equity going forward.
#   Returns a bonus in [0.0, 0.25] to add to the raw strength score.
#
#   Only applied on flop and turn — draws have zero value on the river
#   because no more cards will be dealt.
#
#   Bonuses (matching Gemini spec):
#     Flush draw  (4 cards same suit)  → +0.15
#     OESD        (4 consecutive ranks) → +0.10
#     Both draws at once               → +0.25 (capped)
#
#   Two bugs fixed vs. the Gemini version:
#     BUG 1 — suit extraction used the whole card string instead of card[1]
#             e.g. "Ah" was treated as a suit, not 'h'
#     BUG 2 — rank extraction used the whole card string instead of card[0]
#             e.g. ranks.index("Ah") would crash; correct is ranks.index('A')
# ══════════════════════════════════════════════════════════════

def detect_draws(hole_cards: list, community_cards: list, street: str = "") -> float:
    """
    Return a draw-equity bonus to add to the raw strength score.
    Returns 0.0 on the river or preflop (no future cards / no board yet).
    """
    if street == "river":
        return 0.0
    if len(community_cards) < 3:     # preflop: no board to evaluate
        return 0.0

    all_cards = hole_cards + community_cards
    bonus = 0.0

    # ── Flush Draw ────────────────────────────────────────────────
    # Use card[1] for suit (e.g. 'h' from 'Ah') — BUG 1 fixed here
    try:
        suit_counts: dict = {}
        for c in all_cards:
            s = c[1]                  # ← correct: index 1 is the suit character
            suit_counts[s] = suit_counts.get(s, 0) + 1
        if any(v == 4 for v in suit_counts.values()):
            bonus += 0.15             # one card away from a flush
    except (IndexError, TypeError):
        pass

    # ── Open-Ended Straight Draw (OESD) ──────────────────────────
    # Use card[0] for rank (e.g. 'A' from 'Ah') — BUG 2 fixed here
    try:
        rank_set = sorted(set(
            _RANKS.index(c[0])        # ← correct: index 0 is the rank character
            for c in all_cards
            if len(c) >= 1 and c[0] in _RANKS
        ))
        for i in range(len(rank_set) - 3):
            if rank_set[i + 3] - rank_set[i] == 3:   # 4 consecutive ranks
                bonus += 0.10
                break
    except (IndexError, ValueError, TypeError):
        pass

    return bonus


# ══════════════════════════════════════════════════════════════
#   HAND EVALUATOR  (no external libraries)
#
#   _eval5  : score exactly 5 cards → float in [0, 9)
#             integer part = hand category (0=high card … 8=str.flush)
#             fractional part = primary rank / 13  (tiebreak within category)
#
#   Strength bands (after dividing by 9 to normalise to [0,1]):
#     High card       0.000 – 0.111
#     One pair        0.111 – 0.222
#     Two pair        0.222 – 0.333
#     Three of a kind 0.333 – 0.444
#     Straight        0.444 – 0.556
#     Flush           0.556 – 0.667
#     Full house      0.667 – 0.778
#     Four of a kind  0.778 – 0.889
#     Straight flush  0.889 – 1.000
# ══════════════════════════════════════════════════════════════

def _eval5(cards):
    """Score exactly 5 (rank, suit) tuples. Returns float in [0, 9)."""
    ranks = sorted([c[0] for c in cards], reverse=True)
    suits = [c[1] for c in cards]

    is_flush    = len(set(suits)) == 1
    is_straight = False
    s_high      = 0
    if len(set(ranks)) == 5:
        if ranks[0] - ranks[4] == 4:
            is_straight, s_high = True, ranks[0]
        elif set(ranks) == {12, 0, 1, 2, 3}:   # A-2-3-4-5 wheel
            is_straight, s_high = True, 3

    if is_straight and is_flush:
        return 8.0 + s_high / 13.0             # straight flush / royal flush

    cnt    = _Counter(ranks)
    groups = sorted(cnt.items(), key=lambda x: (x[1], x[0]), reverse=True)
    top_n, top_r = groups[0][1], groups[0][0]

    if top_n == 4:                              # four of a kind
        return 7.0 + top_r / 13.0
    if top_n == 3 and len(groups) >= 2 and groups[1][1] == 2:   # full house
        return 6.0 + top_r / 13.0
    if is_flush:
        return 5.0 + ranks[0] / 13.0
    if is_straight:
        return 4.0 + s_high / 13.0
    if top_n == 3:                              # three of a kind
        return 3.0 + top_r / 13.0
    if top_n == 2 and len(groups) >= 2 and groups[1][1] == 2:   # two pair
        return 2.0 + max(groups[0][0], groups[1][0]) / 13.0
    if top_n == 2:                              # one pair
        return 1.0 + top_r / 13.0
    return 0.0 + ranks[0] / 13.0               # high card


def _best_score(cards):
    """Best 5-card _eval5 score from 5–7 (rank, suit) tuples."""
    if len(cards) < 5:
        return 0.0
    return max(_eval5(combo) for combo in _combinations(cards, 5))


def _postflop_strength(hole_cards, community_cards):
    """Normalised [0,1] made-hand strength from hole + community cards."""
    cards = _parse_cards(hole_cards) + _parse_cards(community_cards)
    if len(cards) < 5:
        return 0.0
    return _best_score(cards) / 9.0


# ══════════════════════════════════════════════════════════════
#   PREFLOP HEURISTICS
#
#   Calibration checkpoints:
#     AA  → 0.95   KK  → 0.90   QQ  → 0.85   22  → 0.38
#     AKs → 0.62   AKo → 0.56   T9s → 0.42   72o → 0.07
# ══════════════════════════════════════════════════════════════

def _preflop_strength(hole_cards):
    """Return a [0,1] preflop strength heuristic for the two hole cards."""
    cards = _parse_cards(hole_cards)
    if len(cards) < 2:
        return 0.20

    r1, s1 = cards[0]
    r2, s2 = cards[1]
    hi, lo    = max(r1, r2), min(r1, r2)
    is_pair   = (r1 == r2)
    is_suited = (s1 == s2)
    gap       = (hi - lo) if not is_pair else 0

    if is_pair:
        score = 0.38 + (hi / 12.0) * 0.57
    else:
        score  = 0.10
        score += (hi / 12.0) * 0.30
        score += (lo / 12.0) * 0.15
        score += 0.06 if is_suited else 0.0
        score -= gap  * 0.03
        score += 0.05 if lo >= 8 else 0.0    # both broadway (T+)

    return max(0.05, min(score, 1.0))


# ══════════════════════════════════════════════════════════════
#   OPPONENT AGGRESSION SCANNER
#   Scans the last 30 opponent actions in state.history.
#   Returns [0.75, 1.25]: values < 1.0 mean aggressive table (tighten up).
# ══════════════════════════════════════════════════════════════

def _table_aggression(history):
    try:
        opp_acts = [e for e in (history or [])[-30:]
                    if e.get("type") == "player_action"]
        if len(opp_acts) < 4:
            return 1.0
        raise_freq = sum(1 for e in opp_acts if e.get("action") == "raise") / len(opp_acts)
        return max(0.75, min(1.25, 1.0 - (raise_freq - 0.30) * 1.5))
    except Exception:
        return 1.0


# ══════════════════════════════════════════════════════════════
#   RAISE SIZING
#   Probe (+25% pot) / Value (+45%) / Power (+65%) / Max (+90%)
#   All clamped to [min_raise, chips + current_bet].
# ══════════════════════════════════════════════════════════════

def _raise_size(strength, state):
    if strength >= 0.85:
        frac = 0.90
    elif strength >= 0.70:
        frac = 0.65
    elif strength >= 0.55:
        frac = 0.45
    else:
        frac = 0.25
    amount = state.min_raise + int(state.pot * frac)
    amount = max(amount, state.min_raise)
    amount = min(amount, state.chips + state.current_bet)
    return amount


# ══════════════════════════════════════════════════════════════
#   MAIN DECISION FUNCTION
# ══════════════════════════════════════════════════════════════

def decide(state: GameState):
    """
    Returns one of: "fold" | "check" | "call" | "allin" | ("raise", int)
    Never raises an exception — any internal error falls back to check/fold.
    """
    try:

        # ── Step 1: Raw hand strength ─────────────────────────────
        if state.community:
            strength = _postflop_strength(state.hole_cards, state.community)
        else:
            strength = _preflop_strength(state.hole_cards)

        # ── Step 2: Draw bonus (detect_draws, bugs fixed) ─────────
        # Adds equity for flush draws (+0.15) and OESDs (+0.10).
        # Skipped on the river — no cards remain to complete a draw.
        draw_bonus = detect_draws(state.hole_cards, state.community, state.street)
        strength   = min(strength + draw_bonus, 1.0)

        # ── Step 3: Table aggression & pot-odds context ───────────
        opp         = max(1, state.active_opponents)
        agg         = _table_aggression(state.history)
        opp_squeeze = 1.0 + (opp - 1) * 0.05   # 1op=1.00, 3op=1.10, 5op=1.20
        required_equity = state.pot_odds * 1.30 * opp_squeeze / agg

        # ── Step 4: RNG bluff / aggression filter ─────────────────
        # Applied BEFORE standard logic so it can override a normal
        # fold/call into an all-in. Guard: only fire when we would NOT
        # already fold on pot-odds alone (avoids lighting chips on fire
        # with absolute trash into a huge bet).
        #
        # Tier 1 — Weak Bluff   (0.25 ≤ strength < 0.40):  5% all-in
        #   Rationale: a score in this range usually means marginal pair
        #   or a draw — enough board connection to make the bluff semi-
        #   credible. Pure air (< 0.25) is excluded on purpose.
        #
        # Tier 2 — Semi-Bluff   (0.75 ≤ strength ≤ 0.87): 20% all-in
        #   Rationale: strong made hands in this tier (flush, full house
        #   range) are value hands we sometimes want to over-rep. The 20%
        #   frequency keeps opponents from knowing whether we "really have
        #   it" or are turning a value hand into a bluff-shove.
        #
        # Tier 3 — Value Shove  (strength ≥ 0.88):         100% all-in
        #   Rationale: quads / straight flush — always get the money in.
        #
        # Safety: each tier gate also checks that strength beats the pot-
        # odds floor, so we don't bluff-shove into a 5× pot bet with 72o.

        if strength >= 0.88:
            # Tier 3: unconditional value shove
            return "allin"

        if 0.75 <= strength <= 0.87 and strength >= required_equity:
            # Tier 2: 20% probability semi-bluff shove
            if random.random() < 0.20:
                return "allin"
            # RNG didn't fire → fall through to standard logic below

        if 0.25 <= strength < 0.40 and strength >= required_equity:
            # Tier 1: 5% probability weak bluff shove
            if random.random() < 0.05:
                return "allin"
            # RNG didn't fire → fall through to standard logic below

        # ── Step 5: Standard deterministic logic ─────────────────
        # (Runs whenever RNG tiers don't trigger, ensuring the bot
        #  always falls back to safe, coherent play.)

        # Short-stack / pot-committed all-ins (non-RNG, always correct)
        if state.to_call > 0:
            call_fraction = state.to_call / max(state.chips, 1)
            stack_vs_pot  = state.chips   / max(state.pot,   1)
            committed   = call_fraction >= 0.40 and strength >= 0.42
            short_shove = stack_vs_pot   <  3.0 and strength >= 0.55
            if committed or short_shove:
                return "allin"

        # Free action: check or bet
        if state.can_check:
            if strength >= 0.60:
                return ("raise", _raise_size(strength, state))
            if strength >= 0.42 and state.street in ("flop", "turn"):
                # Semi-bluff / thin value while future cards remain
                return ("raise", _raise_size(strength * 0.85, state))
            return "check"

        # Facing a bet
        if strength < 0.15:
            return "fold"

        if strength >= 0.68:
            return ("raise", _raise_size(strength, state))

        if strength >= required_equity:
            return "call"

        # Cheap preflop speculative call (implied odds for sets / draws)
        if (state.street == "preflop"
                and state.to_call <= state.chips * 0.12
                and strength >= 0.32):
            return "call"

        return "fold"

    except Exception:
        # Absolute last-resort fallback — must never crash the bot
        return "check" if state.can_check else "fold"

# ─────────────────────────────────────────────
# BOT CLIENT  (networking — do not edit)
# ─────────────────────────────────────────────

class BotClient:
    def __init__(self, host, port, name="Bot"):
        self.host    = host
        self.port    = port
        self.name    = name
        self.pid     = None
        self.player_names = {}
        self.history = []
        self.sock    = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._buf    = b''     # persistent recv buffer

    def connect(self):
        self.sock.connect((self.host, self.port))
        print(f"[{self.name}] Connected to {self.host}:{self.port}")
        self.send({"type": "login", "name": self.name})

    def send(self, msg: dict):
        data = json.dumps(msg) + '\n'
        self.sock.sendall(data.encode())

    def recv(self):
        """Read exactly one message; leftovers stay buffered for next call."""
        while b'\n' not in self._buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                return None
            self._buf += chunk
        line, self._buf = self._buf.split(b'\n', 1)
        return json.loads(line.decode())

    def run(self):
        self.connect()
        while True:
            msg = self.recv()
            if msg is None:
                print(f"[{self.name}] Server disconnected.")
                break

            mtype = msg.get("type")

            # ── Welcome ──────────────────────────────────
            if mtype == "welcome":
                self.pid = msg["pid"]
                self.player_names = msg.get("player_names", {})
                print(f"[{self.name}] Assigned PID={self.pid}, "
                      f"chips={msg['chips']}, bb={msg['big_blind']}, "
                      f"players={msg['num_players']}")

            # ── Hole cards dealt ─────────────────────────
            elif mtype == "hole_cards":
                print(f"[{self.name}] Dealt: {msg['cards']}  "
                      f"chips={msg['chips']}  pot={msg['pot']}")
                self.history.append(msg)

            # ── Community cards ──────────────────────────
            elif mtype == "community_cards":
                print(f"[{self.name}] Board ({msg['street']}): {msg['cards']}  pot={msg['pot']}")
                self.history.append(msg)

            # ── It's your turn ───────────────────────────
            elif mtype == "action_request":
                state  = GameState(msg, self.history, self.pid)
                action = decide(state)

                # Normalise and validate the action
                response = self._build_response(action, state)
                print(f"[{self.name}] Action → {response}")
                self.send(response)
                self.history.append({"type": "my_action", **response})

            # ── Someone else acted ───────────────────────
            elif mtype == "player_action":
                pid = msg["pid"]
                name = self.player_names.get(str(pid), f"Player {pid}")
                act = msg["action"]
                amt = msg.get("amount", "")
                print(f"[{self.name}] {name} → {act} {amt}  chips={msg.get('chips','?')}")
                self.history.append(msg)

            # ── Showdown ─────────────────────────────────
            elif mtype == "showdown":
                winners_names = [self.player_names.get(str(w), f"Player {w}") for w in msg['winners']]
                print(f"[{self.name}] SHOWDOWN — winners: {winners_names}  "
                      f"pot={msg['pot']}  best hand: {msg['hand_name']}")
                for pid, cards in msg["hands"].items():
                    name = self.player_names.get(str(pid), f"Player {pid}")
                    print(f"           {name}: {cards}")
                print(f"           Stacks: {msg['stacks']}")
                self.history.append(msg)

            elif mtype == "winner":
                name = self.player_names.get(str(msg['pid']), f"Player {msg['pid']}")
                print(f"[{self.name}] {name} wins pot={msg['pot']} "
                      f"({msg['reason']})")
                print(f"           Stacks: {msg['stacks']}")

            elif mtype == "hand_start":
                dealer = self.player_names.get(str(msg['dealer']), f"Player {msg['dealer']}")
                sb = self.player_names.get(str(msg['sb']), f"Player {msg['sb']}")
                bb = self.player_names.get(str(msg['bb']), f"Player {msg['bb']}")
                print(f"[{self.name}] ── New hand ── dealer={dealer}  "
                      f"sb={sb}  bb={bb}")

            elif mtype == "game_over":
                winner = self.player_names.get(str(msg['winner']), f"Player {msg['winner']}") if msg['winner'] != -1 else "none"
                print(f"[{self.name}] GAME OVER — winner: {winner}")
                break

            else:
                # Unknown message — just log it
                print(f"[{self.name}] MSG: {msg}")

    def _build_response(self, action, state: GameState) -> dict:
        """Convert the decide() return value into a server message."""
        if isinstance(action, tuple):
            verb, amount = action
            amount = max(int(amount), state.min_raise)
            amount = min(amount, state.chips + state.current_bet)
            return {"action": verb, "amount": amount}

        action = action.lower()

        if action == "check":
            if not state.can_check:
                print(f"[{self.name}] WARNING: tried to check but must call {state.to_call} — folding")
                return {"action": "fold"}
            return {"action": "check"}

        if action == "allin":
            return {"action": "allin", "amount": state.chips + state.current_bet}

        if action in ("fold", "call"):
            return {"action": action}

        # Fallback
        print(f"[{self.name}] WARNING: unknown action '{action}' — folding")
        return {"action": "fold"}


# ─────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Poker Bot")
    ap.add_argument("--host", default="localhost")
    ap.add_argument("--port", type=int, default=9999)
    ap.add_argument("--name", default="Bot")
    args = ap.parse_args()

    bot = BotClient(args.host, args.port, args.name)
    bot.run()
