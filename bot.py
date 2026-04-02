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

def decide(state: GameState):
    """
    Given the current game state, return your action.

    Parameters
    ----------
    state : GameState
        Everything about the current hand (see class above).

    Returns
    -------
    One of:
        "fold"
        "check"               — only when state.can_check is True
        "call"
        "allin"
        ("raise", amount)     — amount = total bet you want (>= state.min_raise)

    WHAT YOU HAVE ACCESS TO
    ───────────────────────
    state.hole_cards      → your 2 cards, e.g. ["Ah", "Kd"]
    state.community       → board cards, e.g. ["2c", "7h", "Td"]
    state.street          → "preflop" | "flop" | "turn" | "river"
    state.chips           → your stack
    state.pot             → total pot
    state.to_call         → cost to call
    state.current_bet     → current highest bet this street
    state.min_raise       → minimum legal raise total
    state.can_check       → True if you can check for free
    state.active_opponents→ number of non-folded opponents
    state.pot_odds        → fraction of pot you'd invest to call
    state.player_chips    → {pid: chips} for all players
    state.player_folded   → {pid: bool}
    state.player_allin    → {pid: bool}
    state.history         → list of past action events this session
    """

    # ── Card parsing helper (inline) ────────────────────────────
    # Converts "Ah" → integer rank 12 (0-indexed in "23456789TJQKA")
    # Returns -1 on parse failure so hand_val degrades gracefully.
    RANKS = "23456789TJQKA"   # index 0=2 … 12=Ace

    def parse_rank(card_str):
        try:
            return RANKS.index(card_str[0])
        except (IndexError, ValueError):
            return -1

    def parse_suit(card_str):
        try:
            return card_str[1]
        except IndexError:
            return None

    # ── Hole-card strength (adapted from original hand_strength logic) ──
    # Original used integer ranks 2-14; we map "23456789TJQKA" → 0-12
    # and re-scale so the math is equivalent.
    try:
        r1 = parse_rank(state.hole_cards[0])
        r2 = parse_rank(state.hole_cards[1])
        s1 = parse_suit(state.hole_cards[0])
        s2 = parse_suit(state.hole_cards[1])
        parse_ok = (r1 >= 0 and r2 >= 0)
    except (IndexError, TypeError):
        parse_ok = False

    if parse_ok:
        # Pair bonus (+5), suit bonus (+1), scaled card value — mirrors
        # the original hand_strength() formula (ranks re-based to 0-12).
        pair_bonus  = 5 if r1 == r2 else 0
        suit_bonus  = 1 if s1 == s2 else 0
        # Original divided (r1+r2) by 28 with ranks 2-14.
        # With 0-12 indexing: equivalent divisor is 24 (max sum = 12+12).
        card_grade  = (r1 + r2) / 24.0
        strength    = pair_bonus + suit_bonus + card_grade
        # Normalise to 0-1 range (max raw strength ≈ 7.0: AA suited)
        strength    = min(strength / 7.0, 1.0)
    else:
        # TODO: Requires manual implementation due to unknown competition structure
        # Could not parse hole cards — fall back to a conservative default.
        strength = 0.3

    # ── Community-card adjustment ────────────────────────────────
    # Original code only evaluated 2-card hands. The competition provides
    # flop/turn/river cards. A full hand evaluator (5–7 card) would require
    # significant restructuring — see Manual Work report below.
    # For now we apply a small street-based confidence boost so the bot
    # doesn't ignore board cards entirely.
    street_bonus = {"preflop": 0.0, "flop": 0.02, "turn": 0.04, "river": 0.06}
    strength = min(strength + street_bonus.get(state.street, 0.0), 1.0)

    # ── Decision logic (adapted from original optimal_bet scaling) ──
    # Original: bet = strength * 20.  We map that onto fold/call/raise
    # thresholds and respect all required state constraints.

    # Pot-odds break-even threshold — call only if strength beats it.
    required_equity = state.pot_odds * 1.5   # 1.5× margin for safety

    if state.can_check:
        # Free to see next card — check weak hands, raise strong ones.
        if strength > 0.75:
            raise_to = min(
                state.min_raise + int(state.pot * 0.5),
                state.chips + state.current_bet
            )
            raise_to = max(raise_to, state.min_raise)
            return ("raise", raise_to)
        return "check"

    # Must call or fold.
    if strength < 0.25:
        return "fold"

    if strength > 0.80:
        # Very strong hand — raise aggressively.
        raise_to = min(
            state.min_raise + int(state.pot * 0.75),
            state.chips + state.current_bet
        )
        raise_to = max(raise_to, state.min_raise)
        return ("raise", raise_to)

    if strength >= required_equity:
        return "call"

    return "fold"

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
