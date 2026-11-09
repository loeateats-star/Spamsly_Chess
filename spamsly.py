#!/usr/bin/env python3
"""
Spamsly - spaced-repetition opening trainer
==========================================

A standalone tkinter + python-chess app. Upload a PGN (for example a ChessBase
export with 1,000+ games and many variations) or paste lines copied straight
out of ChessBase. Every game becomes a chapter, every variation becomes a
trainable line, and every one of *your* moves becomes a spaced-repetition card.

Requirements:
    pip install chess        (the python-chess library, imported as `chess`)

Run:
    python spamsly.py

Modes
-----
* Learn   : new lines in file order. First you learn the line (an arrow shows
            each new move and the annotations are shown). Then you must play
            the whole line from memory 3 times in a row without a mistake.
            A mistake resets the streak. Only then do its moves enter the
            review schedule at level 1 (review in 4h).
* Review  : lines whose moves are due. No hints. A correct move moves the card
            up one level; a mistake drops it two levels, shows the right move,
            and the line is re-tested at the end of the session.
* Drill   : walk every line in order (from the selected one) without touching
            the schedule.

Levels / intervals: 1=4h, 2=1d, 3=3d, 4=1w, 5=2w, 6=1m, 7=3m, 8=6m.

Sidelines (PGN variations) are kept, trained as their own lines and highlighted
in yellow. Playing a repertoire move that belongs to a different line flashes
yellow and is not counted as a mistake.

ChessBase material that is understood:
    * {comments}, ;comments, comments before a variation's first move
    * [%cal Gd2d4,Re7e5] arrows and [%csl Rd4] squares (drawn on the board
      in Learn mode); [%evp], [%clk], [%emt], [%tqu], [%mdl] etc. are hidden
    * NAGs ($1, $14, $146 ...) and symbols (!, ?!, +-, ±, N, ...)
    * Pasted plain text with no braces: prose between moves becomes comments,
      [square bracket] variations, 0-0 castling, German piece letters
      (S, L, T, D), figurines, "Z0"/"--" null moves.
Parsing of uploaded PGN files: an illegal move in a game's main line skips the
game; an illegal move inside a variation drops only that variation.

Progress is saved to "<your file>.pgn.progress.json" next to the PGN.
Pasted courses are stored in ~/.repertoire_trainer/pasted/.
"""

import bisect
import hashlib
import json
import os
import queue
import re
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, ttk

try:
    import chess
except ImportError:  # pragma: no cover
    print("This app needs python-chess. Install it with:  pip install chess")
    sys.exit(1)


# ===========================================================================
# Lenient PGN / ChessBase text parsing into move trees
# ===========================================================================

HEADER_RE = re.compile(r'^\s*\[\s*([A-Za-z0-9_]+)\s+"(.*)"\s*\]\s*$')
HEADER_ANY_RE = re.compile(r'(?m)^\s*\[\s*[A-Za-z0-9_]+\s+".*"\s*\]\s*$')
TOKEN_RE = re.compile(r"\{[^}]*\}?|\[%[^\]]*\]|;[^\n]*|[()\[\]]|\$\d+|[^\s(){}\[\];]+")
BARE_TOKEN_RE = re.compile(r"\[%[^\]]*\]|[()\[\]]|\$\d+|[^\s()\[\]]+")
MOVE_NUM_RE = re.compile(r"^(\d+)(\.+)(.*)$")
SUFFIX_RE = re.compile(r"[!?]+")
COMMAND_RE = re.compile(r"\[%[^\]]*\]")
CAL_RE = re.compile(r"\[%cal\s+([^\]]*)\]")
CSL_RE = re.compile(r"\[%csl\s+([^\]]*)\]")
SAN_RE = re.compile(
    r"^(?:"
    r"[NBRQK][a-h]?[1-8]?x?[a-h][1-8](?:=?[NBRQ])?"
    r"|[a-h](?:x[a-h])?[1-8](?:=?[NBRQ])?"
    r"|O-O(?:-O)?"
    r")$"
)
GERMAN_SAN_RE = re.compile(r"^[SLTD][a-h]?[1-8]?x?[a-h][1-8]$|^[a-h](?:x[a-h])?[18]=?[SLTD]$")
GERMAN = str.maketrans({"S": "N", "L": "B", "T": "R", "D": "Q"})
LONG_ALG_RE = re.compile(r"^[NBRQKP]?([a-h][1-8])[-x]?([a-h][1-8])=?([NBRQnbrq])?$")
NULL_MOVES = {"--", "0000", "Z0", "z0", "@@@@", "null", "<>", "pass"}
RESULTS = {"1-0", "0-1", "1/2-1/2", "1/2", "½-½", "*"}
FIGURINES = str.maketrans({
    "♔": "K", "♕": "Q", "♖": "R", "♗": "B", "♘": "N", "♙": "",
    "♚": "K", "♛": "Q", "♜": "R", "♝": "B", "♞": "N", "♟": "",
})
NON_SAN_CHARS_RE = re.compile(r"[^A-Za-z0-9=\-]")
NAG_TEXT = {1: "!", 2: "?", 3: "!!", 4: "??", 5: "!?", 6: "?!", 10: " =", 13: " ∞",
            14: " +=", 15: " =+", 16: " +/-", 17: " -/+", 18: " +-", 19: " -+", 146: " N"}
SYMBOL_TOKENS = {
    "!": "!", "?": "?", "!!": "!!", "??": "??", "!?": "!?", "?!": "?!",
    "+-": " +-", "-+": " -+", "+=": " +=", "=+": " =+", "+/=": " +=", "=/+": " =+",
    "+/-": " +/-", "-/+": " -/+", "=": " =", "N": " N",
    "±": " ±", "∓": " ∓", "⩲": " ⩲", "⩱": " ⩱",
    "∞": " ∞", "=/∞": " =/∞",
}


def pos_key(board):
    """Fast position identity (pieces, side to move, castling, legal en passant)."""
    ep = board.ep_square if (board.ep_square is not None and board.has_legal_en_passant()) else -1
    return (f"{board.pawns:x}.{board.knights:x}.{board.bishops:x}.{board.rooks:x}.{board.queens:x}."
            f"{board.kings:x}.{board.occupied_co[chess.WHITE]:x}.{int(board.turn)}."
            f"{board.clean_castling_rights():x}.{ep}")


def card_id(pkey, uci):
    """Short, stable id for 'this move from this position' (one SR card)."""
    return hashlib.blake2b(f"{pkey}|{uci}".encode(), digest_size=8).hexdigest()


def fast_san(board, move, tok):
    """SAN for display without the cost of board.san(): reuse the PGN token when it
    is plain SAN, then add the check/mate sign. Call *before* pushing the move."""
    if not SAN_RE.match(tok):
        return board.san(move)
    if move.promotion and "=" not in tok:
        tok = tok[:-1] + "=" + tok[-1]
    if board.gives_check(move):
        board.push(move)
        tok += "#" if board.is_checkmate() else "+"
        board.pop()
    return tok


class Node:
    """One move in a chapter's move tree (the root holds no move)."""
    __slots__ = ("parent", "children", "move", "san", "key", "turn", "fullmove",
                 "comment", "pre", "suffix", "is_main", "shapes")

    def __init__(self, parent, move, san, key, turn, fullmove, is_main):
        self.parent = parent
        self.children = []
        self.move = move
        self.san = san
        self.key = key            # spaced-repetition card id
        self.turn = turn          # side that plays this move
        self.fullmove = fullmove
        self.comment = ""         # comment after the move
        self.pre = ""             # comment before the move (start of a variation)
        self.suffix = ""
        self.is_main = is_main    # on the game's main line (False = sideline)
        self.shapes = None        # ChessBase arrows / coloured squares


class Chapter:
    __slots__ = ("number", "headers", "start_fen", "chess960", "root", "lines", "all_lines", "truncated", "alts")

    def __init__(self, number, headers, start_fen, chess960, root, truncated, alts):
        self.number = number
        self.headers = headers
        self.start_fen = start_fen
        self.chess960 = chess960
        self.root = root
        self.lines = []
        self.truncated = truncated
        self.alts = alts

    def new_board(self):
        return chess.Board(self.start_fen, chess960=self.chess960)

    def title(self):
        h = self.headers
        white, black = h.get("White", "?"), h.get("Black", "?")
        if white not in ("", "?") or black not in ("", "?"):
            t = f"{white} - {black}"
            event = ""
        else:
            t = h.get("Event", "") if h.get("Event", "?") != "?" else ""
            event = None
        extra = " ".join(x for x in (h.get("ECO", ""), h.get("Opening", ""), h.get("Variation", ""))
                         if x and x != "?")
        if extra:
            t = f"{t}  ({extra})" if t else extra
        elif event == "" and h.get("Event") and h["Event"] not in ("?", white, black):
            t += f"  ({h['Event']})"
        if not t:
            first = self.root.children[0]
            t = "Line " + move_label(first)
        return t


def move_label(node):
    if node.turn == chess.WHITE:
        return f"{node.fullmove}.{node.san}"
    return f"{node.fullmove}...{node.san}"


class Line:
    """A root-to-leaf path through a chapter tree."""
    __slots__ = ("chapter", "nodes", "index", "is_main", "label", "keys")

    def __init__(self, chapter, nodes, index):
        self.chapter = chapter
        self.nodes = nodes
        self.index = index
        self.keys = []
        first_side = next((i for i, n in enumerate(nodes) if not n.is_main), None)
        self.is_main = first_side is None
        if self.is_main:
            self.label = "Main line"
        else:
            seq = nodes[first_side:first_side + 4]
            parts = [move_label(n) if (j == 0 or n.turn == chess.WHITE) else n.san for j, n in enumerate(seq)]
            self.label = "Sideline: " + " ".join(parts) + (" ..." if len(nodes) > first_side + 4 else "")


def split_games(text):
    """Split raw PGN text into (headers, movetext) chunks, tracking multi-line comments."""
    games = []
    headers, move_lines = {}, []
    in_moves = False
    in_brace = False

    def flush():
        if headers or any(l.strip() for l in move_lines):
            games.append((headers, "\n".join(move_lines)))

    for line in text.splitlines():
        if not in_brace:
            if line.startswith("%"):
                continue
            m = HEADER_RE.match(line)
            if m:
                key, value = m.group(1), m.group(2)
                if in_moves:                    # a tag after movetext starts the next game
                    flush()
                    headers, move_lines, in_moves = {}, [], False
                headers.setdefault(key, value)  # repeated tags (e.g. WhiteFideId) keep the first
                continue
        if line.strip():
            in_moves = True
        move_lines.append(line)
        for ch in line:
            if in_brace:
                if ch == "}":
                    in_brace = False
            elif ch == "{":
                in_brace = True
            elif ch == ";":
                break
    flush()
    return games


def clean_token(tok):
    """Returns (kind, san) with kind in move | null | result | skip."""
    if tok in RESULTS:
        return "result", None
    if tok in NULL_MOVES:
        return "null", None
    tok = tok.translate(FIGURINES)
    tok = tok.replace("0-0-0", "O-O-O").replace("0-0", "O-O")
    tok = NON_SAN_CHARS_RE.sub("", tok)
    if tok in NULL_MOVES:
        return "null", None
    tok = tok.rstrip("-=")
    if not tok:
        return "skip", None
    if SAN_RE.match(tok) or LONG_ALG_RE.match(tok):
        return "move", tok
    if GERMAN_SAN_RE.match(tok):
        return "move", tok.translate(GERMAN)
    return "skip", None


def parse_move(board, tok):
    try:
        return board.parse_san(tok)
    except ValueError:
        m = LONG_ALG_RE.match(tok)
        if not m:
            raise
        uci = m.group(1) + m.group(2) + (m.group(3) or "").lower()
        move = chess.Move.from_uci(uci)
        if move not in board.legal_moves:
            move = chess.Move.from_uci(uci + "q")
            if move not in board.legal_moves:
                raise ValueError(f"illegal move {tok}")
        return move


def extract_shapes(text):
    shapes = []
    for m in CAL_RE.finditer(text):
        for item in m.group(1).split(","):
            item = item.strip()
            if len(item) == 5:
                try:
                    shapes.append(("arrow", item[0].upper(), chess.parse_square(item[1:3]),
                                   chess.parse_square(item[3:5])))
                except ValueError:
                    pass
    for m in CSL_RE.finditer(text):
        for item in m.group(1).split(","):
            item = item.strip()
            if len(item) == 3:
                try:
                    shapes.append(("square", item[0].upper(), chess.parse_square(item[1:3]), None))
                except ValueError:
                    pass
    return shapes


NON_BMP_RE = re.compile("[^\u0000-￿]")


CHESSABLE_LINK_RE = re.compile(r"\[/variation/[^\]]*\]")
COMMENT_JUNK = {"▷", "▶", "◁", "◀", "."}


def clean_comment(text):
    text = COMMAND_RE.sub(" ", text)
    text = CHESSABLE_LINK_RE.sub(" ", text)     # Chessable cross-reference links
    text = NON_BMP_RE.sub("", text)     # keeps Tk character offsets exact
    text = " ".join(text.split())
    return "" if text in COMMENT_JUNK else text


def is_bare_text(movetext):
    """True for text pasted from ChessBase without braces (prose between moves)."""
    if "{" in movetext:
        return False
    return any(w.isalpha() and len(w) >= 2 for w in re.split(r"[\s()\[\].,;:]+", movetext))


def parse_game(number, headers, movetext):
    """Build a Chapter (with full variation tree) or return None to skip the game."""
    try:
        bare = is_bare_text(movetext)
        tokens = (BARE_TOKEN_RE if bare else TOKEN_RE).findall(movetext)
        chess960 = "960" in headers.get("Variant", "")
        fen = headers.get("FEN")
        board = chess.Board(fen, chess960=chess960) if fen else chess.Board(chess960=chess960)
        start_fen = board.fen()
        root = Node(None, None, "", "", board.turn, board.fullmove_number, True)
        alts = {}
        current = root
        stack = []
        depth = 0
        skip_depth = None
        truncated = False
        pending_pre = ""
        pending_shapes = []
        just_opened = False
        pending_num = None
        expect_reply = False
        words = []

        def add_comment(text, shapes):
            nonlocal pending_pre
            if just_opened:
                if text:
                    pending_pre = (pending_pre + " " + text).strip()
                pending_shapes.extend(shapes)
            else:
                if text:
                    current.comment = (current.comment + " " + text).strip()
                if shapes:
                    if current.shapes is None:
                        current.shapes = []
                    current.shapes.extend(shapes)

        def flush_words():
            if words:
                add_comment(" ".join(words), [])
                words.clear()

        def goto(target):
            nonlocal current
            anc = set()
            n = target
            while n is not None:
                anc.add(id(n))
                n = n.parent
            while id(current) not in anc:
                board.pop()
                current = current.parent
            down = []
            n = target
            while n is not current:
                down.append(n)
                n = n.parent
            for n in reversed(down):
                board.push(n.move)
            current = target

        for tok in tokens:
            raw = tok
            c = tok[0]
            if c == "{" or c == ";" or tok.startswith("[%"):
                if skip_depth is None:
                    if c == "{":
                        body = tok[1:-1] if tok.endswith("}") else tok[1:]
                    elif c == ";":
                        body = tok[1:]
                    else:
                        body = tok
                    flush_words()
                    shapes = extract_shapes(body)
                    text = clean_comment(body)
                    if text or shapes:
                        add_comment(text, shapes)
                continue
            if tok == "(" or tok == "[":
                flush_words()
                stack.append(current)
                depth += 1
                pending_num, expect_reply = None, False
                if skip_depth is None:
                    if current.parent is None:
                        skip_depth = depth           # variation before any move: ignore
                    else:
                        board.pop()                  # alternative to the last move
                        current = current.parent
                        just_opened = True
                        pending_pre = ""
                        pending_shapes.clear()
                continue
            if tok == ")" or tok == "]":
                flush_words()
                if depth == 0:
                    continue
                target = stack.pop()
                if skip_depth is not None and depth == skip_depth:
                    skip_depth = None
                depth -= 1
                if skip_depth is None:
                    goto(target)
                just_opened = False
                pending_pre = ""
                pending_shapes.clear()
                pending_num, expect_reply = None, False
                continue
            if skip_depth is not None:
                continue
            if c == "$":
                sym = NAG_TEXT.get(int(tok[1:]))
                if sym and current.parent is not None and not just_opened:
                    current.suffix += sym
                continue

            m = MOVE_NUM_RE.match(tok)
            if m:
                pending_num = (int(m.group(1)), len(m.group(2)) >= 2)
                tok = m.group(3)
                if not tok:
                    continue
            if tok in SYMBOL_TOKENS:
                if current.parent is not None and not just_opened:
                    current.suffix += SYMBOL_TOKENS[tok]
                continue
            if not any(ch.isalnum() for ch in tok):
                continue                              # unknown glyph / junk
            kind, san_tok = clean_token(tok)
            if kind == "result":
                continue
            if kind == "skip":
                if bare:
                    words.append(raw)
                    expect_reply, pending_num = False, None
                continue
            if kind == "null":
                truncated = True
                if depth == 0:
                    break                             # main line ends here
                skip_depth = depth
                continue

            if bare:
                # In pasted text a move must carry the right move number, or be
                # Black's direct reply, otherwise it is part of a sentence.
                if pending_num is not None:
                    ok = (pending_num[0] == board.fullmove_number and
                          pending_num[1] == (board.turn == chess.BLACK))
                else:
                    ok = (expect_reply and board.turn == chess.BLACK) or just_opened or current is root
                pending_num = None
                if not ok:
                    words.append(raw)
                    expect_reply = False
                    continue
            try:
                move = parse_move(board, san_tok)
            except Exception:
                if bare:
                    words.append(raw)
                    expect_reply = False
                    continue
                if depth == 0:
                    return None                       # error in main line: skip game
                skip_depth = depth                    # error in sideline: drop it
                continue
            if move == chess.Move.null():
                truncated = True
                if depth == 0:
                    break
                skip_depth = depth
                continue

            flush_words()
            # Only moves written at depth 0 belong to the main line. Chessable often opens a
            # variation by repeating the main move ("7.g3 (7.g3 Nb6 ...) 7...Bg7"); the
            # variation's continuation must not take the main-line slot, so main moves are
            # always kept as children[0] and variation moves are never marked main.
            on_main = depth == 0
            existing = next((ch for ch in current.children if ch.move == move), None)
            if existing is not None:
                if on_main and not existing.is_main:
                    existing.is_main = True            # promote: the main line goes this way
                    current.children.remove(existing)
                    current.children.insert(0, existing)
                board.push(move)
                current = existing
            else:
                pk, uci = pos_key(board), move.uci()
                node = Node(current, move, fast_san(board, move, san_tok), card_id(pk, uci), board.turn,
                            board.fullmove_number, on_main)
                alts.setdefault(pk, set()).add(uci)
                sm = SUFFIX_RE.search(tok)
                if sm:
                    node.suffix = sm.group(0)
                if pending_pre:
                    node.pre = pending_pre
                if pending_shapes:
                    node.shapes = list(pending_shapes)
                if on_main:
                    current.children.insert(0, node)   # main line is always the first child
                else:
                    current.children.append(node)
                board.push(move)
                current = node
            pending_pre = ""
            pending_shapes.clear()
            just_opened = False
            expect_reply = current.turn == chess.WHITE
        flush_words()

        if not root.children:
            return None
        return Chapter(number, headers, start_fen, chess960, root, truncated, alts)
    except Exception:
        return None


def collect_paths(root):
    """All root-to-leaf paths, main line first (iterative, no recursion limit issues)."""
    paths, path = [], []
    it_stack = [iter(root.children)]
    while it_stack:
        child = next(it_stack[-1], None)
        if child is None:
            it_stack.pop()
            if path:
                path.pop()
            continue
        path.append(child)
        if child.children:
            it_stack.append(iter(child.children))
        else:
            paths.append(list(path))
            path.pop()
    return paths


def read_pgn_text(path):
    with open(path, "rb") as f:
        data = f.read()
    for enc in ("utf-8-sig", "cp1252"):
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            pass
    return data.decode("latin-1", errors="replace")


def prepare_pasted_text(text, name):
    """Turn pasted ChessBase text into PGN. Header-less text is split into one game
    per line that starts with '1.' (prose before it is kept as an intro comment)."""
    if HEADER_ANY_RE.search(text):
        return text
    parts = re.split(r"(?m)^(?=[ \t]*1\.(?!\.))", text)
    games, carry = [], ""
    for part in parts:
        if not re.match(r"[ \t]*1\.(?!\.)", part):
            carry += part
            continue
        games.append((carry + "\n" + part).strip())
        carry = ""
    if not games:
        games = [text.strip()]
    elif carry.strip():
        games[-1] += "\n" + carry
    safe = name.replace('"', "'")
    out = []
    for i, body in enumerate(games, start=1):
        out.append(f'[Event "{safe} - line {i}"]\n[Site "Pasted"]\n\n{body}\n')
    return "\n".join(out)


class Course:
    def __init__(self, path, chapters, total_entries):
        self.path = path
        self.name = os.path.splitext(os.path.basename(path))[0]
        self.total_entries = total_entries
        self.skipped = total_entries - len(chapters)
        self.truncated = sum(1 for ch in chapters if ch.truncated)
        self.alts = {}                 # position -> every repertoire move from it
        for ch in chapters:
            for epd, ucis in ch.alts.items():
                self.alts.setdefault(epd, set()).update(ucis)
            ch.alts = None
            seen = set()               # de-duplicate within a game only
            ch.all_lines = []
            # The main line ends where the main moves end, even if commentary variations
            # hang off its last move (e.g. "21.Bc4 (21.Bc4 d5 22.Na5)"), so build it explicitly.
            main, n = [], ch.root
            while n.children and n.children[0].is_main:
                n = n.children[0]
                main.append(n)
            for nodes in ([main] if main else []) + collect_paths(ch.root):
                uid = " ".join(n.move.uci() for n in nodes)
                if uid not in seen:
                    seen.add(uid)
                    ch.all_lines.append(Line(ch, nodes, 0))
        self.all_chapters = [ch for ch in chapters if ch.all_lines]
        # Chessable exports store one variation per game; their bracketed variations are
        # only commentary, so by default they are shown as notes instead of trained.
        self.is_chessable = any("chessable.com" in ch.headers.get("SourceTitle", "") for ch in chapters)
        self.color = chess.WHITE
        self.lines, self.chapters, self.user_keys = [], [], set()
        self.apply_sideline_mode(not self.is_chessable)

    def apply_sideline_mode(self, train_sidelines):
        """Choose whether variations are trained as their own lines or shown as notes only."""
        self.train_sidelines = train_sidelines
        self.lines = []
        for ch in self.all_chapters:
            ch.lines = [l for l in ch.all_lines if l.is_main or train_sidelines]
            for l in ch.lines:
                l.index = len(self.lines)
                self.lines.append(l)
        self.chapters = [ch for ch in self.all_chapters if ch.lines]
        self.set_color(self.color)

    def set_color(self, color):
        self.color = color
        self.user_keys = set()
        for line in self.lines:
            line.keys = [n.key for n in line.nodes if n.turn == color]
            self.user_keys.update(line.keys)


def serialize_chapter(ch):
    """Flatten a chapter tree into plain tuples so it can cross a process boundary."""
    r = ch.root
    flat = [(-1, None, "", "", r.turn, r.fullmove, r.comment, r.pre, r.suffix, True, r.shapes)]
    index = {id(r): 0}
    stack = [r]
    while stack:
        n = stack.pop()
        pi = index[id(n)]
        for c in n.children:
            index[id(c)] = len(flat)
            flat.append((pi, c.move.uci(), c.san, c.key, c.turn, c.fullmove, c.comment, c.pre,
                         c.suffix, c.is_main, c.shapes))
        stack.extend(n.children)
    return (ch.number, ch.headers, ch.start_fen, ch.chess960, ch.truncated, ch.alts, flat)


def deserialize_chapter(data):
    number, headers, start_fen, chess960, truncated, alts, flat = data
    nodes = []
    for pi, uci, san, key, turn, fullmove, comment, pre, suffix, is_main, shapes in flat:
        parent = nodes[pi] if pi >= 0 else None
        n = Node(parent, chess.Move.from_uci(uci) if uci else None, san, key, turn, fullmove, is_main)
        n.comment, n.pre, n.suffix, n.shapes = comment, pre, suffix, shapes
        if parent is not None:
            parent.children.append(n)
        nodes.append(n)
    return Chapter(number, headers, start_fen, chess960, nodes[0], truncated, alts)


def _parse_batch(batch):
    """Worker-process entry point: parse a batch of (number, headers, movetext)."""
    out = []
    for number, headers, movetext in batch:
        ch = parse_game(number, headers, movetext)
        out.append(serialize_chapter(ch) if ch is not None else None)
    return out


PARALLEL_MIN_GAMES = 120
BATCH_SIZE = 40


def load_course(path, progress=None):
    text = read_pgn_text(path)
    chunks = split_games(text)
    total = len(chunks)
    items = [(i, h, m) for i, (h, m) in enumerate(chunks, start=1)]
    del chunks, text

    cpus = os.cpu_count() or 1
    if total >= PARALLEL_MIN_GAMES and cpus > 1:
        try:
            from concurrent.futures import ProcessPoolExecutor
            batches = [items[i:i + BATCH_SIZE] for i in range(0, total, BATCH_SIZE)]
            chapters, done = [], 0
            with ProcessPoolExecutor(max_workers=min(8, cpus)) as ex:
                for res in ex.map(_parse_batch, batches):
                    chapters.extend(deserialize_chapter(r) for r in res if r is not None)
                    done += len(res)
                    if progress:
                        progress(done, total)
            return Course(path, chapters, total)
        except Exception:
            pass                                   # fall back to single-process parsing

    chapters = []
    for number, headers, movetext in items:
        ch = parse_game(number, headers, movetext)
        if ch is not None:
            chapters.append(ch)
        if progress and number % 50 == 0:
            progress(number, total)
    return Course(path, chapters, total)


# ===========================================================================
# Spaced repetition scheduler + persistence
# ===========================================================================

HOUR, DAY = 3600, 86400
INTERVALS = [0, 4 * HOUR, DAY, 3 * DAY, 7 * DAY, 14 * DAY, 30 * DAY, 90 * DAY, 180 * DAY]
LEVEL_LABELS = ["", "4h", "1d", "3d", "1w", "2w", "1m", "3m", "6m"]
MAX_LEVEL = 8
LEVEL_DROP = 2
DRILL_REPS = 3
# Moves you get wrong come back sooner: every recorded miss ("lapse") shrinks that move's
# future intervals by LAPSE_FACTOR (up to MAX_LAPSE_EFFECT misses), never below MIN_INTERVAL.
# A correct answer at level 4 (1 week) or higher forgives one miss.
LAPSE_FACTOR = 0.6
MAX_LAPSE_EFFECT = 4
MIN_INTERVAL = HOUR
FORGIVE_FROM_LEVEL = 4


def interval_for(level, lapses):
    return max(MIN_INTERVAL, INTERVALS[level] * LAPSE_FACTOR ** min(lapses, MAX_LAPSE_EFFECT))
APP_DIR = os.path.join(os.path.expanduser("~"), ".repertoire_trainer")


def progress_path_for(pgn_path):
    pgn_path = os.path.abspath(pgn_path)
    folder = os.path.dirname(pgn_path)
    if os.access(folder, os.W_OK):
        return pgn_path + ".progress.json"
    os.makedirs(APP_DIR, exist_ok=True)
    return os.path.join(APP_DIR, hashlib.sha1(pgn_path.encode()).hexdigest()[:16] + ".json")


def write_json_atomic(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, separators=(",", ":"))
    os.replace(tmp, path)


def load_config():
    try:
        with open(os.path.join(APP_DIR, "config.json"), encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(cfg):
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        write_json_atomic(os.path.join(APP_DIR, "config.json"), cfg)
    except Exception:
        pass


class Progress:
    def __init__(self, pgn_path):
        self.path = progress_path_for(pgn_path)
        self.color = "white"
        self.train_sidelines = None        # None = course default
        self.cards = {}                    # card id -> [level, due_timestamp]
        try:
            with open(self.path, encoding="utf-8") as f:
                data = json.load(f)
            self.color = data.get("color", "white")
            self.train_sidelines = data.get("train_sidelines")
            for k, v in data.get("cards", {}).items():
                if "|" in k:               # older "epd|uci" key format
                    try:
                        epd, uci = k.rsplit("|", 1)
                        k = card_id(pos_key(chess.Board.from_epd(epd)[0]), uci)
                    except Exception:
                        continue
                self.cards[k] = list(v)
        except Exception:
            pass

    def save(self):
        try:
            write_json_atomic(self.path, {"version": 2, "color": self.color,
                                          "train_sidelines": self.train_sidelines, "cards": self.cards})
        except Exception as exc:
            print("Could not save progress:", exc)

    def get(self, key):
        c = self.cards.get(key)
        return (c[0], c[1]) if c else (0, 0)

    def level(self, key):
        return self.get(key)[0]

    def lapses(self, key):
        """How many times this move was missed (cards are [level, due] or [level, due, lapses])."""
        c = self.cards.get(key)
        return c[2] if c and len(c) > 2 else 0

    def _set(self, key, level, due, lapses):
        self.cards[key] = [level, due, lapses] if lapses else [level, due]

    def learn(self, key, now):
        if self.level(key) == 0:
            lap = self.lapses(key)
            self._set(key, 1, now + interval_for(1, lap), lap)

    def success(self, key, now):
        lvl, due = self.get(key)
        if lvl == 0:
            self.learn(key, now)
        elif due <= now:
            lvl = min(MAX_LEVEL, lvl + 1)
            lap = self.lapses(key)
            if lap and lvl >= FORGIVE_FROM_LEVEL:
                lap -= 1
            self._set(key, lvl, now + interval_for(lvl, lap), lap)

    def fail(self, key, now):
        lap = self.lapses(key) + 1
        lvl = max(1, self.level(key) - LEVEL_DROP)
        self._set(key, lvl, now + interval_for(lvl, lap), lap)

    def mark_lapse(self, key):
        """Record a miss while learning (the move is not scheduled yet)."""
        lvl, due = self.get(key)
        self._set(key, lvl, due, self.lapses(key) + 1)

    def line_status(self, line, now):
        """('empty'|'new'|'due'|'learned', next_due, min_level)"""
        if not line.keys:
            return "empty", None, 0
        next_due, min_lvl = None, MAX_LEVEL
        cards = self.cards
        for k in line.keys:
            c = cards.get(k)
            if not c or c[0] == 0:
                return "new", None, 0
            if c[0] < min_lvl:
                min_lvl = c[0]
            if next_due is None or c[1] < next_due:
                next_due = c[1]
        return ("due" if next_due <= now else "learned"), next_due, min_lvl


def short(text, n):
    return text if len(text) <= n else text[:n - 3].rstrip() + "..."


def plural(n, word):
    return f"{n} {word}" + ("" if n == 1 else "s")


def fmt_delta(seconds):
    if seconds <= 0:
        return "now"
    if seconds < HOUR:
        return f"in {max(1, int(seconds // 60))}m"
    if seconds < DAY:
        return f"in {int(seconds // HOUR)}h"
    return f"in {int(seconds // DAY)}d"


# ===========================================================================
# Piece images: the 'cburnett' set by Colin M.L. Burnett (the classic lichess pieces),
# rendered from Wikimedia Commons (Chess_klt45.svg etc.; see those file pages for the
# license terms), downscaled to 64px and embedded so the script stays standalone.
# ===========================================================================

APP_ICON_PNG = "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"
PIECE_PNG_SIZE = 64
PIECE_PNGS = {
    "K": "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",
    "Q": "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",
    "R": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAADT0lEQVR42u2aP0gbcRTHjQpKUhOENmRwMKZTEUcxFHQwIiJEl6xOHSwIDSrooJOTk4uDQ80gStu0adeig0MF6+xqin+Gbi0dRIIkr+97vBMb7zrI/fkN7wufwbt77/vue7nk/tjSolKpVCqVSqVSqR6hTibuQKfL9hEm5lITl3URj7x81wvmkDlx4CvT71CTZ7651JzIurxDXb/0dKo5lFkC12uGWltbqaOj4w78zcsbzCuHmreoaWtr+6cGYBnWyTbNQq+GixfJLIFrDuaDg4NULpepUqlYDAwM2EO9YRJN7GJdoVC4294Gy6Ru16EOvaze9vbwhLfUzIUWwNTUFNVqNbKVy+Xsoa6Z303UsG51dZWahWVSV3OoQy+rty14wtu4AIrFIkUiEXuwB+Cju7Oz8yAALMM6tzr0RG/jA7i5uaHz83M6Oztz5Orqim5vbx8EgGVY51aHnuhtfABByYQAlmCeTCatc3NsbCxQ4AlvCWApjACW3c7XEFgOI4BnzAf5zaeJiQna3Nykra0tX4HH5OSkvePw/sg8DetqMMp8YuqJRML6Jq/X676d9+i9t7dH3d3d2Pk680Uun0MVQqjgaMTjcZqfn6f19XVfWFhYIAQtR/4z88SUmyKE8I4vTRupVIpmZmZodnbWU9ATveHBXu9NOPLNGmH+ZDIZuri4sD6uXoKe6A0P8TJOWeZXX1+fdUHjtdATveEhXhqABqABaAAagAagAWgAGoAGoAFoABqABmCAhnGvHovFaHx8nKanpz0FPdFbngcMmxjAIp7T9fT0WA8uS6WSp6AnesuzwEXTdj7NVPGGd21tjRqNhuenAHqit7xF/sFkTNn5FLONI9Pb20v7+/t0enrqCwcHB5ROp+1PwbZ4h67vMhC1t7db56mfwEPeCdTFO3RZA2G4rq6uQJAvQxszAjg6OqLLy8tAgJdxAVSr1cDeDMNLAwgpALwBKjDFe1iDrKys0MbGRiDA614A92cpyIy+6WWL/L+OoVzLjL4pB6NoNEr5fN5idHSUstksDQ0NBQo84W3PgZkkhJzvAeCmxDTJjVIwAeCa3K+rvcci9wnBBGA4vgbwnDlmfhrKsczomyLyMxM3lOh//ttcpVKpVKom/QV4tx2HFFZGcwAAAABJRU5ErkJggg==",
    "B": "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",
    "N": "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",
    "P": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAEhUlEQVR42u1aW0tcVxQe7zGCGryiqKh4AUlVvL5kfGrTi7Zjm7eoJEHUJ/VdBQV/QfOgIdC+OO2DlxYk2ib1rQqC4uWhFaoPDbmoDBodxzjozOr6ZG8IacYZHT1z9sn54IPDnLUv69tr773O3mOxmDBhwoQJEyZMmDBhQkPEMkuYVuYt8Rz7MTgew/yS+YT5iulmHonn35gNwsaQuMYcYDrDwsIoMTGRcnJyToln/IZ3zH5hazh0Md/GxMRQS0sLzc/Pk8vlOiWem5ubCe9gw+w0mvO5zBfh4eHU09NDx8fH9D7wG97BBraijGHQzfTU1tbS7u4u+cLOzg7BBrYiYgyDn5nU19dH/tDb2wsBwJ+MJMBTODU8POxXgKGhISnA74aLAIyuP2AdMGIEYD57qquraXt726fzW1tbVFVVBedPjLYT2JgHkZGRNDAwQF6v93/O4ze8i4iIkPnA10ZxHunuc4R1UlISDQ4O+twG8Q42Ygr8K9JkpZHH3IRDCO3FxUW/awBsxDQgUTZX5dR3Bo5gb9/c3KRAAduamhopwh+qpsbfYuFLSEigpaUlOi+Wl5cJZUVSZFPxc/cXjGBnZyednJycWwCUQVkRBROqRUEG8zU6H8i894WFhQUpwGtRpzKoZHrj4+M/uOIHCpRFHaiLWaGSAJ9j5AoLCylYFBQUyCi4rZIAn6HT+fn5QQuQl5cnBfhUJQFuYvXGAYfb7b6w80dHRxQdHS13ghKVBEhlrmPkpqenLyzA1NSUHP1/RJ3KIIr5GJ1vbGy8UBSgjM1mkwI8YkaqlgtUMw8RwuPj4x/8APIF2I6OjlJUVBScP2RWqZgJIgoeYgSzs7NpZmaGPB6PX+dhA9usrCw5+t+LupT9GNqGI5mZmWS328+cDng3MjJCGRkZ0vktVT+Gwpnl4kPGi5PelJQUampqOvOjCO9gA1txOowE6BmzTNSpjPM4zHiJUUxOTqb+/n5aW1sLeArAFmXeORt4KW6NlBDhDvMNOl5ZWXnqzEWBshUVFVKEXeZ3KmSADoQvtj+n0xl0Jri/v3+6HYop4dBzRogF72+MVn19/ZkXIOcFLkwaGhpkJPzFzNfjlmfHolVWVkYbGxt02UCd5eXlcmG0621rxImNE7e8k5OTdFVA3eKUCKfG31h0dOc/h/Ds6OgI6uMnkPS4vb1dToU/9fJfAmxP7vT0dFpdXaWrxsrKCqWlpZH4Y8VXehDgV4xIW1tbUKc/5zklam1tffesMKRIwujjNmdubo60wuzsrLxBQhTcCKUA9yzi0uMyt71AtkUkWSIKWkLlfATzR3Siu7s7oDT3soC2urq6pAA/iL5ojuvMFXRiYmKCtMbY2JgUYEn0RXMkM11IUa8i8fGH9fV1mR67xFqkOUoxAtiS9vb2NBcAbaampsoo+CQUAmAPJqS++Kub1kCbpaWlUoAvQiFAExqvq6sjh8NBBwcHmhJtWq1WKcDdUAjwAI3HxcVRUVERFRcXa0q0ibaFAPdDIUCHaFwPbLeE6AbYqhMqdXNswoQJEyb0gv8ABF4a0ASCCI4AAAAASUVORK5CYII=",
    "k": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAIpklEQVR42u2aaUxVWRLHQcR2CQou3RrG3bhFifrFLbHTOnR0Morg7uiARtOijToxcR1mNNE2ccV9d1qNEmOiRoM77TZxwT3uScf1gyuI6LDLmfpVn2teUBB4z+Y1vkr+4XJvnao6dc6tU1Xv+vn5yEc+8pGPfOSjcqAAwUCLgC/RAcGCbIvgL9EBIQJjEfKlTLq7IFGwV5Dk4oAkey/R8lRY+sll0kXhp4rsgCaCWME/BLNcJj3L3ou1PL4Y4HOAzwEVlyoJvhXsc3EA1z0E/hV98pUFcYLXH4n+6YIfLU+FpSjBq2KOQJ5FVtTJfyO4VII84KLg64rogBGC3BI4AJ6/eftkCFZBgqaC7wV/F8QI+gvC7AoGFhrzcwkm7+A/hcYGWplhVkeM1fm9TZyCfq8AipI6gh8EJwIDAzOqVatmqlevbvgr/xt/f/88efarnXAfQTU7NrkUDki2Yxj7FyvrV2Sjo5DODGyxNtX53I7oLbjZsGFDExcXZ3bs2GHOnj1rrly5on937txp4uPjTefOnU3lypWdyfxXEC44VgoHHLWry1iVhUxko8NVJzZgCzZhm7XxszQv/tW4ceOs1atXm8zMTPMpunfvnpk+fboJDg7GsHzBy1I4IJUxISEhZurUqebu3bumoKCgWH3Z2dlm3bp1plGjRlkyNt7TTZbpPXv2zHIMyc3NNadOnTKzZ882AwcONL1799a/M2bMMLt37zZPnjxRo969e6eOGDNmjKlatWpJJ6+8Y8eO1bHIgJCJbHS46sSG06dPq03YdufOHSO2ZoqcaZ6afHj37t3THzx4oIZcvnzZ9O/f39SsWbNI45s0aWImTZpkbty48X512LrNmzf/5ORbtGhhdu3apWOg69evm4kTJ6rMopyILZGRkfpaQPfv3zfdunUjsfqz21tftmHKhQsXVPDx48dNy5YtS7SKErBMgwYNzLx580xaWpquTkpKiunSpUuRY7p27WrQBW9qaqqZO3euykBWSXS2atXKnDhxQm1FF7a7+yp0Fs8W5OTkmIcPH5oOHTqYUrzHikqVKpk+ffqYW7du6cRu376tEy3MJyumz+CBly3O2NLqw0ZsxWbZqQXMwR0HxK9atUo9umHDBhMQEFBqgxy0b9/enD9/XifItma1nGetW7fW14Vn8LRr167MerBx48aNavOKFSu49093Iv/Phw8fVmGxsbFlNspBmzZtzLVr11TekSNH9CwHx44d03tXr15VHnf1jB8/XuUdPHjQ2BwioKyV21aiPRQdHe22YUACqnn+/LnJz8/XI46jkmvu8Rp4QseoUaPUZuIBcyhrhUndnpCYmKjCCGaeMM51hd6+fatg648bN85j8ufPn6/yt2/fzv8Jdi5louETJkzQs/jMmTNEVY8YSHJ08uTJ90kMK2UTJrdRu3ZtzRDZVTiaObgTBOs0a9bs9YsXLzTRGD58uMdWiSTGoQEDBnhM7ogRI9RWbG7atOlrWx+4RSsSEhIK8CiRum3bth4xtF69eu8dwLUnZBJAb968qau/ZMkSjsDlnsgEG0p+fZ8IDR06dMiEhoa6bSyvk0OeeLWwiahPPCEjxGZs91Q6PDQ8PDz98ePHGg8OHDjgVF9uOQBZwF0HyGRNUlKSysJGbMVmT3dyZw0aNCjz6dOn6uWLFy+ajh07FpumkslxzhOY4I2KitLSdc6cOYYEKysrS8E193gGD9kcYxhbXDaI7k6dOplLly6pTdgmsYVCaKY7kb8ooisTL97NxstQRkaGFio0KQpH4iFDhhhKZxz15s0bU1piDHUBMgYPHqwyXXWgE93YAD169IiUO0ee/fsj3SiP7oTRUrGlEQscOnfunOnXr58ZOnSo2b9//wf9Amd1KFD27t1rNm/ebJYtW2YWLlyo4Jp7PIPn2bNnH9T/yNy3b586NiIiQnU6hC3YhG2fY+U/cIJsvW5SgqawAi9fvlQjKD44fqC8vDwNRGvWrFGnUEFSstLCqlKliubrrq8O19zjGTzwMmbYsGFm7dq1miIjE0IHuiCOOl6boKCgFGz6PSbv2hv8WoxeMHr06DTHIBoYy5cv12qPLVuWau5jcQRZpMkUN9T6jsMl5X0tNiy0DdNy+VUpICwsLG7Lli15M2fO1GZG4YqRDI9qr0ePHrobpkyZoqkqgY+qDXDNPZ7BAy9jCmeHyEYHutApFeZEb/glKUKQ4xjJFqbUHTlypL7XBDKCptPhKQnByxjGbtq0SbM7ZCLbxSE5Vne5U4S8fzl169bVAEUgc3qCzjtLd4cozXG1Z88e7S0sWrRICyzANfcYCw+8jHFiitMTZCw60IVOr3CABKBI6RXkUueTiBC9idh0d3hn2dLkALVq1SpRawseeBnD2JUrV2qjE5nIRge60InucnfA1q1bx8pK5bNK1PRSN2jfz+V3AbeBLAIrxyWR3+6sfHSXuwMkaxskR1UuAaxwsuKsqPyeYHr16qWNCtraixcv1i0vgUyxfv16fQ14FhMTo7yktx/bMehAFzrR7RUxQKJzjmMskZqqjL7+tm3b9NgiWyOwUaV9iuCBlzGMRQayOBWcE8bmDd4TBInI9evX19U7evSoblPXyb569UobocnJyfr7AOktxx4/agCuucczeOBljKtTeL2QTWsOXV5zCkjfPmry5Mm5GO1E7fT0dO3KSE1u+vbtqz0E+vs1atQoNhDyDB54GcPYpUuXatqLTOdUQRc60V3uDpB3OVqysnxWiZ/OFixYoAGLSO6pIIgsMkFkowNd6ES3N5wCf5LV/mXatGlv3O0RlLT2F13/Qye6/bzo46e/Co4Lsj6jA6j1f7EfSQT6+XnnV2B8Arfe/sTtqYmnWpnf/pG+IvtK8J1gvuCw4LH9TuBTk4XnkeCQ328fTiOjit8fmPytM/iOJ1TQxR5f0fazlh/sdYR9Fmp5v/oSPpz0kY985CMflSf9H0OxJBE+ugPjAAAAAElFTkSuQmCC",
    "q": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAIuElEQVR42u1bfUyVVRi/N0HwAwmjQrGWmIrfumWmlprhB31o5txsuqngsvJrmm6ac9PM/kiNhVBzTSVMo5lWfkxgFVNLmyhYWSbDQrIEVMTKQuDydH6n57K343nPvZfde8HtPttvvpz3d57nOc/5es65rw5HSEISkpCEJCQhCbLcITBUYCXjIS67raWNQLxAnIDTwOsgsFnAJUAMPKfzOztxsu54ttWqZLJAkcAfAjUCnws8bMOdL9BgabwbKHvZps4w1lnDNk6xzVYhEwSqNQ36RaC3wm0nUKDhuvGlQKRSJ1GgTMOFzfGtIQBf2jSmUeBthduZe88uAKeYY5V01qXjfxHoxoUJRAuEGzh/GRp0TOFCz2cG/qcaW8cN/D8NfoWz72HNaTgqjxP4SOCowG6BZwQiNNxLBgfzNPynBa5ruCh7SsPPN+i/pOHDx0kCHwscEcjhtoT7skXN1fTs3wJLNdtVps0QrbdZ1NAjswV+t3B/47Iwm0Wz3maKZWh2olfYVysXbUn1dqtNECg3RLy/wr9XoFDhYVvbo1nQrDLbwp9t4EWyLpdi4wTbtsoAgQob3y8IdPcmAM8ahpydsx0FXuKeBKdUoJOHPT3NojPNQ+4QzTrdo+UltqnKHA++e7V1TvWgJNVQ9xhzbggke0iG8pW1wpQEJbNOcL828OZ68P05bwKQaBhGVzhttZMTFm6WgRfHQ9I6POMM/Cxl6NsJ0uurNr5XcNu82gFeFajVzOs3BdoaFk/rHl9laNQQJRts4DK7YFUpuYLdYgbfNmjWi1o+c3i9JbbjoX6ce90dgBcNcxXGi5VGzbPhpvowtV5QglVs6AQn++iyjFi0IYXb5LNE8NbndqDEMIxg4DulUUc1AcPf72gC8K4N96jC+9bQmET20d0BS2xyF5/kEWVf/cCmB6IEzmimTaKGpzsPFPA7tUHqcP7eZgeAT9lK3vKIP9LhKOWwA8XPa3h3CvyoadgbypztbnO4QdkDypryhob3A9tSZbrSUdWagDZb1Hz8vMB9CidW4CebU6E1JxhpOA6PtPBQ52cNDzbuUmzfzz5Zecf9eSjK0KSh2cqcvdcy/1SuNQFZYNinFyh3DLoUu0TJAJ28TarcDH8GYK6m1/5WEouulmxNRY5lMXrfEIAsy+KbY8MpZVtumWJJkqyjaa4/A/CYzQmu1DIc77cZsu7t6EEe1t8YAvANcx60bL8qfrZMv7tsRh18fdSfAcCQu2jj0NucPNktbm4s5VX9VwOnnDlLDZwythWmnCesgK/3+DMATsPFBKZCkkBPwynSnRNME6gzcOqYc9RDkGDrCc2x17oAOv19O/SOwamTPE0uGjj/eLgNst4K/WN4f5FtnTBwMgNxPZZquJtzO17poXGNXgTAEweHmr0e6qcGIgCP8rU0tXLU+HsBdMt9mmSjNQI+dgvUDfFXt0EAvmruTXBzMsLWiAxHACXlNghASiAD8LjNFfUtCA8Pp5iYGIqPj6f+/fvTxIkTac6cObR8+XJav349paWlUXp6ugSeUbZs2TLJmTBhgqyDutABXV42vp59DJj05NPd/ww7nU6KiIig2NhYGjt2LK1atYpycnKosLCQqqqqqLGxkXwV1EFd6IAu6IRu2IAt2LQ5efZ0BPgn8P+ln3369KGVK1dSfn4+1dTUaBtTW1tLpaWldOTIEdq7dy9t3bq1qeeBzZs307Zt2+Q7cMBFHZ3ARl5eHq1YsULaVgLwVjB+Oo8R+CQxMZGKi4tv6bWysjLas2cPrV69miZNmkQJCQkUFhbm81xGHdSFDuhCcC5cuHDLaIIP8AU+sW9BkbsXL16cC2euX79Ohw4dknN78ODBFBUV5cuc9RrQCd1DhgyRtmATtuGD8OUQfHIEU0aNGtV93Lhxl3r06EHt27cP+moPm7A9fvz430ePHv2Aw9Ey3/nMb9OmjWvYsGGUlJQUVMCmsO3+qqTFvi8KE9tb3tWrVynYApvJycm5gcz6vJJBgwZtPXz4MJ0/fz6ogE1h+z2Ho+U/dytqwazvVEsOf9y4zPDyjB8oNLIPzqC3vlOnTgkiO/tDCB08eBBbEQ0cOLBZe74vuQFswBZswjZ8EL50D3oAxL68YM2aNU2Jicvlohs3btC5c+coOzubFi5cKHP6Xr16UYcOHXxubMeOHWVd6Fi0aBHt2LGDSkpKpA3Ycide8KFt27bzW2IKrMNePHz4cFq7dq1MhSsrK5sCgn/hLPJ5ZIcnT56kffv2yTR406ZNtG7dOpnhAXhGGd6BAy7qoC50WLM/rP4FBQXSJmxzDvJasBsfq37vh17u3bs3TZ06lTZu3CgDcubMGRmUmzdv+rzNoU5FRYXUAV0bNmyQuvv27UtiyOsWw9igtb5fv35JwiHXli1bSGSD1KVLFyQlt8xXlGPOjhkzhqZPn05LliyRx96MjAzavn077dy5UwLPKMM7cMBFnQEDBkgd6roCW127dpW24QN8gU9BC8CsWbOevHz5suyp+vp62UtoxIwZM+S87dy5s1/PA9AFndA9c+ZMysrKkjYbGhqkD/AFPgUtAOIY2mXatGnn0HtXrlyhurq6pqGLOVtUVES7du2SR9bJkyfLYysagMMM5mxkZKQ804vFSwLPKMM7cMBFHdTFURu6oBO63QKbsA0f4At8CvY6MAI3sLixmTJlCmVmZtLZs2ebekV3J1BeXk6nT5+WWVxubi7t37+fDhw4IJ9xD4B34NjdBUA3bMAWbMI23wKPaMlsEL/lrRBAXl4TFxcnz/DYnnbv3i3P69euXfPpVgjc6upq2evQAV3QCd1875/LNhMdrUSc/JN2LN/JvSqurD4Uw7tQ7A6V0dHRrm7dutHQoUPlvo5FLiUlhebNmyeBZ5Th3hAc3AWiDupCB3Txl2uPs42IFsn+mvHBdQz/D49+jv++7Z/t+O9b3tf5ai2d8RaX4d0s5vblujG+fOgckpCEJCQh8UH+BT3/h2m7TUanAAAAAElFTkSuQmCC",
    "r": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAACQklEQVR42u2aMWsaYRjHPeugV7kuRYpubQeVODqU0C2baIdQcBMhCIFgCs1QiqvfwcGKQj5EtwwdrtFB/AIZRChSSCk0BQv2yfOENxDsXRJK3/fewv8Pv0mf+z/3g/NULhZDEARBEARBEOQvkmS8AJIh73eYhyEznnrN+Udd2lNkTpjTAD4yWwEzNeZTyMypeq0WMLeljhk0c6J2MZ59hkL4zewFzPRvmbmmHzC3p44ZNrMfhYCDO07kkHm0wfE9BBwHzB3eMXNgo4AL5tsGq3sIWAXMXfyPAkwCARBg/AtAMvm2Wq1So9GIFNlBdjEuIJfLHU2nU1osFpEiO8guxgWk0+nHpVKpXygUVvl8niLil+wgu0T1bfAB8475IddiIpGgVCqlFelQ1710vlc7RJ5d5mu32yXf97UiHdKlOq1Krdls/uz1eqQT6eCuVzb+MnzhOM55PB4nnUiHdFkpgDk3cM+HAAiAAAiAAAiAAAiAAAiAAAiAAAiwKC/L5fL3er1OOpEO6bJRwNFoNFovl0vSiXRIl20n/5Q5y2QyxP8Sa0U6pIt5ZsvJP8lmsx/a7fa60+mQCaRLOqXbBgGfi8Xiejab0Xw+N4J0Sad02yDg6tPZdV3yPM8I0nXjrmCHgAiBAAgwGJd5zby5ptVq0Xg8pslkYhTplO6bu6jdXJ0CtmMbz+tUKhUaDAY0HA6NIp3SHfvzuaRtnQJ2LHoqJIwdCIAACNCW54zPfLEUX+2oLY66zXiW4t7ytDmCIAiCbOQSrHqzyka1X58AAAAASUVORK5CYII=",
    "b": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAD70lEQVR42u2bXUgUURTHZ4sydUsWRFZIij62D0kQCV+WetCHLMQCsY+tJXvsgyj6ehB6ENFNtxA2H8LsYYNCe7GoXosl9Ulo62GzoiylIBAES0t2bufsnpVNbL5nuTPOH34wzN45954zd+6ce++sIDhy5MiRI0eOciwXsBE4TGygc8tCxcBdYB5gxDydK7a7827gAZDMcj4DnntIZWyrA8DsEs5n+AXst3MAQhLOZ+iwcwBuKwhAxM4BOAOIEs7jb6ftHIAtwHuJAIwBm+3+JjgETC/hPJ47aGfHVwNHgdcSPeAtcIzK2ko7gGfAbwWDIJZ5Cmy3S8obAMZlBr+lBsPP1GMsmyKvAs4DP1U4vpgZ4KIVHwls8BXK7JhOZsmWZYKwgrrujJRjLpeLeb3eFHisoCccIdvcqwKYkLuzbrebJRKJFHisoCdMkG2utQYYUNK1PR4PywiPFT4O/VSHZWd7egMwy/NscSXwSMqByspKFolEWG9vL4tGowsBwGM8h79hGZkgDFBd3Gkr8EWq8aFQiMkJy8gEYJzmFNypQS7T8/l8rKWlhbW1tbFwOLzgNB7jOfwNyyjIFBt4DMBlNe93jWNAhks8BiCsNgCiKKbQEIAuHgPQpcaJwsJCNjo6mgKPVQbgBo8BuKY2zS0oKEihIT2+ymMA8P08Z0DuryQXqOMxAGXAhxwEAJfU1vM69+9SOe9Xi0jPv4vnRc83JgYgboVF07rs2WB5eTnz+/2awGuznP8K7LPKekAN9oSSkhI2NTXFtAqvRRt052ustDyWB9zE93ssFmOTk5OawGspRwiTTcvohPDv9rde/gDHreJ8Ge3wGD0AjpFt7tVs0qsQbZ7k3vumpqZ77e3trLOz01DQZmNjY5R3/9fF4/FhZpLA9gjUsZbnAGyqra392N3dzXp6egwFbaJtrIP3ATBhYiaY4H0gxN2bQRMDMEhbblxrJzBigvPDZNsSws2LU8Arna/EJNlo5n1D5H/T43xgG3AOeAJ8oqxOKuPDMo+Bs3RtPm9OlQJ7hPS+/wWgFbglpL/uugP0AfeF9AbGc2CIFjG+C+lNzqTMHccy3+iaIbLRTzb7qI4I1dlKbQhQm0rNnDD5aDEiQd/ziDlY/VGTJU5T20K0SWPozA6fwXecOS0VjHfU5jwjnO/I0WKn0cxR23UFIZiDu2V2rwrqCUC9CQ1Eez+AF8B14iWdM6Ouer2PQZDm4iJ98BSjgSZAy1RVwK4s8CuO3UA1sJfwUzn89K1Ioq4iKlNF12SuryabFYvqqqI2BKhNMWpjktocNOrVh9/wewEPJSQ8rs25qG0eaqt7Of0LxZEjR44cadFfXwiRHWyLrA8AAAAASUVORK5CYII=",
    "n": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAGOElEQVR42u1aa0hlVRT2bZmajo1lDGpq5it8VjQaWqApWv6JFEzF0h8+MkFBA8VmCCWqEX/0AI0E07FCqFDUdBjEZmgkTFMTLXNE0vKZztV83tVah30OZ25XGe89D5Wz4APZ93juXt9+rLW+dS0sNNNMM80000wzzTQz2+5DRCGeQFge8Zw34j3EZcSDZ4mATxCriHnEJYSDkWeeRQwj9Ih9xIdnxXlrxO8IYNhhq2wteiYI8YvoGWCE2Z8FAsiJGQPnNhGvio7HN2zlwQDBZ2UH/GrEuT8RhYj3EVtGPieUIR5HPIy4/zST8OUhDt4L9qysrP6wtbXtsLS0vMTuigcQVqeJgHRyxFQSwsLCoLGxEcrKyuDixYsHNjY24yxSnD8tBNSa4Pgu/3dVVRWIbXZ2FmpqasDLy+sOfn4F8ehJdp4usgUTCDjg/05ISICWlhaYn58XSNDr9bC0tAQVFRV6FxcXijKvncSo4YzoPeSGPxbs7OzA29sbSkpKYHh4WCBib28Prl27Rsdkk+UbD50U5+mS+pRfSbzAIDg4GLKzs8Hf399kIug9Hh4eUF5eDouLiwIR4+PjEB8fv4eff4vPeajtPKW7L4ovvpiYGJicnOS2bl9fH5i7IwjR0dEwNDTEvZNsenoaYmNjifAOhKuaBFAeP8hP9Ny5czAwMHDXaklBAMHHxweuX78OBwcH3LsnJiYgKCiISPgMYavW6heKJ5mRkQG7u7vC5VVXVycZAQSMBjA4OCgQTDvMwcGB7p031MgXLiBuiyfY0NAgTG5hYQECAgIkJYAQHh4Oc3Nz3Hfs7+9DZWUlja8g/JVOe68YTq66uprbomtra5CWlia58zwyMzNhZ2eHI2Frawt8fX1pvF3JNPopxLLhxJycnCApKQlCQkIA01rZCMBtD21tbcJua21tBUyhKaFKUsJ5YrlNLueOkzYvLy9zBGxvb0NERASNdyIc5SYgGXFHbQKwToD6+nphF9D9g0mUDj+LkdN5Yvd7tZ3ngWEQdDodRwAlSxQqcfwjOSNC2hE1veLAc3/XXVBQUABMlXpMDudJ3/vxpDjPIzU1VSCgt7cXHB0dD0QqlOS1/vZJI8De3h5WVlY4AlZXVyEwMJDGm6R2nlLNn2Ry4ra572hqahJ2QU5ODo1NMXlNMnuJqbxSO/8bItHc95DTlBWSkZ6AOQhFqeelJOA7/susra25nNzNzc1c54cQkYjnzCWAUm4+GpCG4O7uTvXBm1I578mvPmV3pNdROXrr1i0IDQ0FExUgCqUB7P2F5hJAizIzMyOEQzavL6Qi4HX+i1xdXWFsbIyr9AiU+x9zsnSJNoqEDBs2UbOPU0dHB0cA1SIUGXBsXKoy+bJYrmpvb+fkqfX19eMWPFSxlRq0y86bqCP+D7W1tcJFyBaG3uslBQGV4i8imYouneTkZC4dvYfJ6dlqxBlkaKQn5El1oZIEJ74IcWwdES3pETAB+ywmG5Ot3BA/S0VAYmIibG5ucgTcvHmTNMVdlrmabU+aOKk1RM4ResI7UobUyMhILhHi5TKS53D8balU35FjTog6vq8cUZS8zLaoZAR4enpyKhQZKUZMkf5YykRo4x4n8y/iLYO2uNjoXE5LnVSRGEOdJDJqpERFRfEqkWTafwZLh9dZLN8x0gek8QbW1DRmTyNG5UipKReg/IRsY2MD4uLiaPwHqWsCd+bEC4hYxOcGPb6vEI8c8r/PsGggW2E0OjrKEUB6YUpKCl8TyGrk7LusVZXNWmTGLJLl/bJWhjdu3BAk+fT0dGC6pertdT85zrwxkB7AW25uLo39c8RxVMRcxJ0judHd3S0QkJ+fzydDbmo5b8eOhmLiSFdXl0BAcXExsMh1QS0C4pTWDzs7OwUCSktLganXfhYq/WLsqtLyGF8RklFbHcd0av0CLRDxt9IE9PT0GO4AIiBEDQIy1BBI+/v7BQKKiopU3QEfqEEAqVS85eXl8QQEqUHA12oQMDIyIhCQlZXFExCoBgHdahAwNTUlEMDUKp1Ie1TUSPqaY7KUIsA22QI2SxdRDVpsbm5eRH3gLxzvUysTJLHTidUGigAVa2c/Pz9n7Aw5o0zujC0y59P+u2PNNNNMM82UsP8A0T4OMstdjZUAAAAASUVORK5CYII=",
    "p": "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAACMklEQVR42u2ayy9DQRTGG49QOyEWdlg2XvHY6c6zKQ12RLBhhT+Bf4GVSFhhh43Ecye2YsOCDWm1pAkJ9Ui0nEnOJN0ot53emTPOl/ySm/R27v2+TmfO3LkeD4vFYrFYLBaLxXJRXsAH+IEOPPb+B+MlQB+wC9wBH8A7Hu8BQTzHSpUCC8Az8PUD4rN5PNc6zQJvGcxLxDkztpmvAcJ/MC8J43es0RyQdBBAEnuMNdp0YF6yYVMAB1kEsM89wLIZwMkY8GnbTBACXhwEIOqBflvMi3L3Nou/wA2WyaRVC8SyMC+JUa4HRDl7nIN5yRHV0njQ4cCXqSgKUVzubiswL9mi1guqgajCAKLYJhm1AimFAYi2WigF0KPQvKSbUgBdeQigk1IA9YpmgPSZwEcpgCrgWmEAV9gmGRUDKwoDWAaKqNUC7cCrAvOijTaKlaDoBUsKAljEtsguhh5yMH9PdTFUADTjQiaVYwF0CDRhm2TMi4cZEYWDYAR3jUiEMAw85aEQegSGKFSA8TyYl8RNrgjFgHeZR/OSC6DOxClvXfEKMNPAuG7a1Bj6ZddXNeJaAx6D9vxPXTQvOTHlXYIgvujgdgDixYqACQHsaDCf/qxQqyo0/frpvaBcZwDjGs1LxnSZLwTWDAhgFe/FdZUB5wYEcIb34roqgYQBASRwLHJdjQaYlzToCCBgUAC9OgIYNSiAER0BTBoUwISOAKYNCmDKo2kH2G8IpHaOWSwWi2WKvgEEqOXLfjnJkwAAAABJRU5ErkJggg==",
}


# ===========================================================================
# GUI theme: purple surfaces, electric cobalt blue, midnight black, acid lime
# ===========================================================================

SQ = 70
BOARD_PX = SQ * 8

BG = "#0b0915"            # midnight black page
HEADER = "#1a0e3d"        # deep purple bar
PANEL = "#141026"         # purple-tinted card
PANEL_2 = "#1e1736"       # raised surface / ghost button
BORDER = "#2c2452"
HOVER = "#2b2253"
PURPLE = "#7a3fe0"
PURPLE_HOVER = "#8d57ea"
COBALT = "#2f5bff"
COBALT_HOVER = "#4a72ff"
COBALT_SOFT = "#9db0ff"
LIME = "#c6ff00"
LIME_HOVER = "#d6ff4d"
TEXT = "#ece8fb"
MUTED = "#9a91c0"
DIM = "#5f5786"
RED = "#ff4d6d"
YELLOW = "#ffe14d"
SIDE_TEXT_BG = "#2b2510"
SIDE_ROW_BG = "#211c0c"

LIGHT, DARK = "#ddd3f8", "#7c5fd0"
LAST_LIGHT, LAST_DARK = "#e9fbab", "#a7cf3c"
SEL_COLOR = "#9fb2ff"
HINT_COLOR = COBALT
WRONG_COLOR = RED
ALT_COLOR = YELLOW
ARROW_LEARN = LIME
ARROW_FIX = RED
ARROW_SHOW = COBALT
SHAPE_COLORS = {"G": "#86e000", "R": RED, "Y": YELLOW, "B": COBALT}
LEVEL_COLORS = ["", "#5a2bbf", "#6c3fdc", "#5a52ee", "#3f62fb", "#2f7bff", "#3fb0e0", "#8fdc3a", LIME]

# kind -> (accent bar colour, text colour)
BANNER = {
    "neutral": (BORDER, TEXT),
    "info": (COBALT, TEXT),
    "learn": (LIME, TEXT),
    "good": (LIME, LIME),
    "bad": (RED, "#ffb3c1"),
    "side": (YELLOW, YELLOW),
}

OPPONENT_DELAY_MS = 450
DRILL_OPPONENT_DELAY_MS = 320
NEXT_LINE_DELAY_MS = 1200
FONT = "Segoe UI"
F = {}                    # font roles, filled by init_fonts()


def style_title_bar(win):
    """Paint the Windows title bar in the app's colours instead of the default white one.
    Uses DwmSetWindowAttribute: dark mode (Windows 10 20H1+) plus caption/text/border
    colours (Windows 11). Silently does nothing elsewhere."""
    if sys.platform != "win32":
        return
    try:
        import ctypes
        from ctypes import wintypes
        win.update_idletasks()
        hwnd = wintypes.HWND(ctypes.windll.user32.GetParent(win.winfo_id()))
        dwm = ctypes.windll.dwmapi

        def colorref(hex_color):                     # "#rrggbb" -> 0x00BBGGRR
            r, g, b = int(hex_color[1:3], 16), int(hex_color[3:5], 16), int(hex_color[5:7], 16)
            return r | (g << 8) | (b << 16)

        for attr, value in ((20, 1),                       # DWMWA_USE_IMMERSIVE_DARK_MODE
                            (35, colorref(HEADER)),        # DWMWA_CAPTION_COLOR
                            (36, colorref(TEXT)),          # DWMWA_TEXT_COLOR
                            (34, colorref(HEADER))):       # DWMWA_BORDER_COLOR
            v = ctypes.c_int(value)
            dwm.DwmSetWindowAttribute(hwnd, ctypes.c_uint(attr), ctypes.byref(v), ctypes.sizeof(v))
    except Exception:
        pass


def init_fonts(root):
    fams = set(tkfont.families(root))
    semi = "Segoe UI Semibold" if "Segoe UI Semibold" in fams else None

    def strong(size):
        return (semi, size) if semi else (FONT, size, "bold")
    F.update({
        "h1": strong(15), "h2": strong(13), "h3": strong(11), "num": strong(22),
        "body": (FONT, 10), "bodys": strong(10), "small": (FONT, 9), "smalls": strong(9),
        "italic": (FONT, 10, "italic"), "btn": strong(10), "coord": strong(8),
        "move": strong(11), "sidemove": (FONT, 10),
    })


GLYPHS = {"k": "♚", "q": "♛", "r": "♜", "b": "♝", "n": "♞", "p": "♟"}


class Session:
    def __init__(self, mode, lines, single=False):
        self.mode = mode                          # learn | review | drill
        self.queue = [(l, False) for l in lines]  # (line, is_retest)
        self.pos = 0
        self.single = single
        self.done = 0
        self.mistakes = 0


BUTTON_KINDS = {
    "primary": (LIME, BG, LIME_HOVER),
    "accent": (COBALT, "white", COBALT_HOVER),
    "purple": (PURPLE, "white", PURPLE_HOVER),
    "ghost": (PANEL_2, TEXT, HOVER),
    "danger": (PANEL_2, "#ff8aa1", "#3a1424"),
}


class FlatButton(tk.Button):
    """Flat button with hover feedback and a consistent size."""

    def __init__(self, parent, text, cmd, kind="ghost", font_role="btn", padx=16, pady=8, **kw):
        super().__init__(parent, text=text, command=cmd, relief="flat", bd=0, padx=padx, pady=pady,
                         font=F[font_role], cursor="hand2", highlightthickness=0,
                         disabledforeground=DIM, **kw)
        self.set_kind(kind)
        self.bind("<Enter>", lambda e: self.cget("state") != "disabled" and self.config(bg=self._hover))
        self.bind("<Leave>", lambda e: self.config(bg=self._bg))

    def set_kind(self, kind, enabled=True):
        bg, fg, hover = BUTTON_KINDS[kind] if enabled else (PANEL_2, DIM, PANEL_2)
        self._bg, self._hover = bg, hover
        self.config(bg=bg, fg=fg, activebackground=hover, activeforeground=fg,
                    state="normal" if enabled else "disabled")


def card(parent, **kw):
    return tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER, **kw)


class TrainerApp:
    def __init__(self, root):
        self.root = root
        init_fonts(root)
        self.piece_images = {}
        try:
            for sym, data in PIECE_PNGS.items():
                self.piece_images[sym] = tk.PhotoImage(data=data)
        except tk.TclError:
            self.piece_images = {}
        try:
            self.app_icon = tk.PhotoImage(data=APP_ICON_PNG)
            root.iconphoto(True, self.app_icon)
        except tk.TclError:
            pass
        root.title("Spamsly")
        root.configure(bg=BG)
        root.geometry("1180x820")
        root.minsize(1080, 740)

        self.course = None
        self.progress = None
        self.session = None
        self.statuses = []
        self.load_queue = queue.Queue()
        self.loading = False

        # board / line state
        self.board = chess.Board()
        self.line = None
        self.retest = False
        self.ply = 0
        self.gen = 0
        self.awaiting = False
        self.step_failed = False
        self.line_failed = False
        self.line_done = False
        self.learn_phase = False
        self.streak = 0
        self.reveal = False
        self.selected = None
        self.drag_from = None
        self.dragging = False
        self.press_was_selected = False
        self.hl = {}
        self.arrows = []
        self.shapes = []
        self.last_move = None
        self.filled_chapters = set()
        self.node_ranges = {}
        self.played_ids = set()
        self.rendered_chapter = None
        self._segs, self._pos = [], 0
        self.range_starts, self.range_ends, self.range_nodes = [], [], []
        self.preview = False
        self.screen = "library"
        self.course_cache = {}            # normcase(path) -> (Course, mtime)
        self.progress_cache = {}          # path -> Progress

        self.cfg = load_config()
        self.courses = self.cfg.get("courses")
        if self.courses is None:          # first run of the course library: import the last file
            self.courses = []
            last = self.cfg.get("last_pgn")
            if last and os.path.isfile(last):
                self.courses.append({"path": os.path.abspath(last),
                                     "name": os.path.splitext(os.path.basename(last))[0],
                                     "added": time.time()})
            self._save_cfg()

        self.color_var = tk.StringVar(value="white")
        self._setup_style()
        self._build_header()
        self.body = tk.Frame(root, bg=BG)
        self.body.pack(fill="both", expand=True)
        self._build_library()
        self._build_overview()
        self._build_study()
        self.show_library()
        style_title_bar(root)
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        for key, cmd in (("h", self.show_hint), ("s", self.reveal_move), ("r", self.restart_line),
                         ("n", self.skip_line), ("Escape", self.go_back)):
            root.bind(f"<KeyPress-{key}>", lambda e, c=cmd: c())
        root.bind("<Return>", lambda e: self.next_line() if self.screen == "study" else None)

    # ------------------------------------------------------------------ style
    def _setup_style(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("Treeview", rowheight=30, font=F["body"], background=PANEL,
                     fieldbackground=PANEL, foreground=TEXT, borderwidth=0,
                     bordercolor=PANEL, lightcolor=PANEL, darkcolor=PANEL)
        st.configure("Treeview.Heading", font=F["smalls"], background=PANEL, foreground=MUTED,
                     relief="flat", borderwidth=0, bordercolor=BORDER, lightcolor=PANEL, darkcolor=PANEL,
                     padding=(8, 6))
        st.map("Treeview.Heading", background=[("active", PANEL)])
        st.map("Treeview", background=[("selected", PURPLE)], foreground=[("selected", "white")])
        st.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        for orient in ("Vertical", "Horizontal"):
            st.configure(f"{orient}.TScrollbar", background=PANEL_2, troughcolor=PANEL,
                         bordercolor=PANEL, arrowcolor=MUTED, lightcolor=PANEL_2, darkcolor=PANEL_2,
                         gripcount=0, arrowsize=12)
            st.map(f"{orient}.TScrollbar", background=[("active", HOVER)])
        st.configure("Thin.Horizontal.TProgressbar", troughcolor=PANEL_2, background=LIME,
                     bordercolor=PANEL_2, lightcolor=LIME, darkcolor=LIME, thickness=4)

    # ----------------------------------------------------------------- header
    def _build_header(self):
        hdr = tk.Frame(self.root, bg=HEADER)
        hdr.pack(fill="x")
        tk.Frame(self.root, bg=LIME, height=2).pack(fill="x")

        mark = tk.Frame(hdr, bg=HEADER, cursor="hand2")
        mark.pack(side="left", padx=(24, 0), pady=12)
        a = tk.Label(mark, text="Spam", bg=HEADER, fg=TEXT, font=F["h1"], cursor="hand2", bd=0, padx=0)
        a.pack(side="left")
        b = tk.Label(mark, text="sly", bg=HEADER, fg=LIME, font=F["h1"], cursor="hand2", bd=0, padx=0)
        b.pack(side="left")
        for w in (mark, a, b):
            w.bind("<Button-1>", lambda e: self.show_library())
        self.course_label = tk.Label(hdr, text="", bg=HEADER, fg=MUTED, font=F["body"])
        self.course_label.pack(side="left", padx=(16, 0))

        right = tk.Frame(hdr, bg=HEADER)
        right.pack(side="right", padx=24, pady=12)
        seg = tk.Frame(right, bg=BORDER, padx=1, pady=1)          # segmented control
        seg.pack(side="left", padx=(0, 16))
        for text, val in (("White", "white"), ("Black", "black")):
            tk.Radiobutton(seg, text=text, value=val, variable=self.color_var, indicatoron=0,
                           command=self.on_color_change, bg=PANEL_2, fg=MUTED, selectcolor=COBALT,
                           activebackground=HOVER, activeforeground=TEXT, relief="flat", bd=0,
                           padx=14, pady=4, font=F["bodys"], cursor="hand2",
                           highlightthickness=0).pack(side="left")
        self.color_var.trace_add("write", lambda *a: self._style_color_toggle(seg))
        self._style_color_toggle(seg)
        self.courses_btn = FlatButton(right, "Courses", self.show_library, "ghost", pady=5)
        self.courses_btn.pack(side="left", padx=(0, 8))
        self.upload_btn = FlatButton(right, "Add PGN", self.upload_pgn, "primary", pady=5)
        self.upload_btn.pack(side="left")

    def _style_color_toggle(self, seg):
        for rb in seg.winfo_children():
            on = rb.cget("value") == self.color_var.get()
            rb.config(fg="white" if on else MUTED)

    # --------------------------------------------------------------- overview
    def _build_overview(self):
        ov = self.overview = tk.Frame(self.body, bg=BG)

        content = self.ov_content = tk.Frame(ov, bg=BG)
        content.pack(fill="both", expand=True)

        tiles = tk.Frame(content, bg=BG)
        tiles.pack(fill="x", padx=24, pady=(24, 16))
        self.tile_vars = {}
        for i, (key, caption, color) in enumerate((("new", "New lines", LIME),
                                                   ("due", "Due for review", COBALT_SOFT),
                                                   ("learned", "Lines learned", "#c4a6ff"),
                                                   ("moves", "Moves learned", TEXT))):
            f = card(tiles)
            f.grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 8, 0))
            tiles.columnconfigure(i, weight=1, uniform="tile")
            v = tk.Label(f, text="0", bg=PANEL, fg=color, font=F["num"])
            v.pack(anchor="w", padx=16, pady=(12, 0))
            tk.Label(f, text=caption, bg=PANEL, fg=MUTED, font=F["small"]).pack(anchor="w", padx=16, pady=(0, 12))
            self.tile_vars[key] = v

        actions = tk.Frame(content, bg=BG)
        actions.pack(fill="x", padx=24, pady=(0, 16))
        self.learn_btn = FlatButton(actions, "Learn", self.start_learn, "primary", padx=22, pady=10)
        self.learn_btn.pack(side="left")
        self.review_btn = FlatButton(actions, "Review", self.start_review, "accent", padx=22, pady=10)
        self.review_btn.pack(side="left", padx=8)
        self.drill_btn = FlatButton(actions, "Drill in order", self.start_drill, "ghost", padx=22, pady=10)
        self.drill_btn.pack(side="left")
        self.side_btn = FlatButton(actions, "Sidelines", self.toggle_sidelines, "ghost", padx=16, pady=10)
        self.side_btn.pack(side="left", padx=8)
        self.load_info = tk.Label(actions, text="", bg=BG, fg=MUTED, font=F["small"], justify="right")
        self.load_info.pack(side="right")

        lower = tk.Frame(content, bg=BG)
        lower.pack(fill="both", expand=True, padx=24, pady=(0, 24))

        left = card(lower)
        left.pack(side="left", fill="both", expand=True)
        top = tk.Frame(left, bg=PANEL)
        top.pack(fill="x", padx=16, pady=(14, 8))
        tk.Label(top, text="Course contents", bg=PANEL, fg=TEXT, font=F["h3"]).pack(side="left")
        FlatButton(top, "Reset selected line", self.reset_selected_lines, "danger", font_role="smalls",
                   padx=10, pady=4).pack(side="right")
        tk.Label(top, text="Double-click to open  |  right-click for more", bg=PANEL, fg=MUTED,
                 font=F["small"]).pack(side="right", padx=12)
        tk.Frame(left, bg=BORDER, height=1).pack(fill="x")
        tree_frame = tk.Frame(left, bg=PANEL)
        tree_frame.pack(fill="both", expand=True, padx=4, pady=4)
        self.tree = ttk.Treeview(tree_frame, columns=("status", "next"), show="tree headings")
        self.tree.heading("#0", text="CHAPTER / LINE", anchor="w")
        self.tree.heading("status", text="STATUS", anchor="w")
        self.tree.heading("next", text="NEXT REVIEW", anchor="w")
        self.tree.column("#0", width=420, stretch=True)
        self.tree.column("status", width=140, stretch=False)
        self.tree.column("next", width=140, stretch=False)
        ysb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ysb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        ysb.pack(side="right", fill="y")
        self.tree.tag_configure("chapter", font=F["bodys"])
        self.tree.tag_configure("side", background=SIDE_ROW_BG, foreground=YELLOW)
        self.tree.tag_configure("due", foreground=COBALT_SOFT)
        self.tree.tag_configure("empty", foreground=DIM)
        self.tree.bind("<<TreeviewOpen>>", self.on_tree_open)
        self.tree.bind("<Double-1>", self.on_tree_double)
        self.tree.bind("<Return>", lambda e: self.open_selected_line())
        self.tree.bind("<Button-3>", self.on_tree_right_click)
        self.tree_menu = tk.Menu(self.root, tearoff=0, bg=PANEL_2, fg=TEXT, activebackground=PURPLE,
                                 activeforeground="white", bd=0, font=F["body"])
        self.tree_menu.add_command(label="Open", command=self.open_selected_line)
        self.tree_menu.add_separator()
        self.tree_menu.add_command(label="Reset progress for this line", command=self.reset_selected_lines,
                                   foreground="#ff8aa1")

        right = card(lower, width=310)
        right.pack(side="right", fill="y", padx=(16, 0))
        right.pack_propagate(False)
        tk.Label(right, text="Memory levels", bg=PANEL, fg=TEXT, font=F["h3"]).pack(anchor="w", padx=16, pady=(14, 0))
        tk.Label(right, text="Your moves by review interval", bg=PANEL, fg=MUTED,
                 font=F["small"]).pack(anchor="w", padx=16)
        self.chart = tk.Canvas(right, width=278, height=150, bg=PANEL, highlightthickness=0)
        self.chart.pack(padx=16, pady=(12, 8))
        tk.Frame(right, bg=BORDER, height=1).pack(fill="x", padx=16, pady=8)
        tk.Label(right, text="Upcoming reviews", bg=PANEL, fg=TEXT, font=F["h3"]).pack(anchor="w", padx=16, pady=(4, 6))
        grid = tk.Frame(right, bg=PANEL)
        grid.pack(fill="x", padx=16)
        self.upcoming_vals = []
        for r, label in enumerate(("Due now", "Next 24 hours", "Next 7 days", "Hard moves (missed)")):
            tk.Label(grid, text=label, bg=PANEL, fg=MUTED, font=F["body"]).grid(row=r, column=0, sticky="w", pady=2)
            v = tk.Label(grid, text="0", bg=PANEL, fg=TEXT, font=F["bodys"])
            v.grid(row=r, column=1, sticky="e", pady=2)
            self.upcoming_vals.append(v)
        grid.columnconfigure(1, weight=1)
        reset = FlatButton(right, "Reset course progress", self.reset_current_course_progress, "danger", pady=6)
        reset.pack(side="bottom", fill="x", padx=16, pady=(4, 14), before=right.winfo_children()[0])
        self.chart.config(height=86)

    # ------------------------------------------------------------------ study
    def _build_study(self):
        st = self.study = tk.Frame(self.body, bg=BG)

        left = tk.Frame(st, bg=BG)
        left.pack(side="left", padx=(24, 16), pady=24, anchor="n")
        self.canvas = tk.Canvas(left, width=BOARD_PX, height=BOARD_PX, highlightthickness=0, bg=BG)
        self.canvas.pack()
        self.canvas.bind("<ButtonPress-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.session_bar = tk.Canvas(left, width=BOARD_PX, height=4, bg=PANEL_2, highlightthickness=0)
        self.session_bar.pack(pady=(16, 8))
        self.session_label = tk.Label(left, text="", bg=BG, fg=MUTED, font=F["small"])
        self.session_label.pack(anchor="w")

        right = card(st)
        right.pack(side="left", fill="both", expand=True, padx=(0, 24), pady=24)
        inner = tk.Frame(right, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=20, pady=18)

        head = tk.Frame(inner, bg=PANEL)
        head.pack(fill="x")
        self.mode_pill = tk.Label(head, text="LEARN", bg=LIME, fg=BG, font=F["smalls"], padx=8, pady=1)
        self.mode_pill.pack(side="left")
        self.chapter_label = tk.Label(head, text="", bg=PANEL, fg=MUTED, font=F["small"])
        self.chapter_label.pack(side="left", padx=10)
        FlatButton(head, "Back", self.show_overview, "ghost", font_role="smalls", padx=12, pady=4).pack(side="right")

        self.title_label = tk.Label(inner, text="", bg=PANEL, fg=TEXT, font=F["h2"],
                                    anchor="w", justify="left", wraplength=500)
        self.title_label.pack(fill="x", pady=(14, 4))
        self.line_label = tk.Label(inner, text="", bg=PANEL, fg=MUTED, font=F["bodys"], anchor="w", padx=0)
        self.line_label.pack(anchor="w")

        self.steps_frame = tk.Frame(inner, bg=PANEL)
        self.steps_frame.pack(fill="x", pady=(14, 0))
        self.steps = tk.Canvas(self.steps_frame, width=232, height=8, bg=PANEL, highlightthickness=0)
        self.steps.pack(side="left")
        self.steps_label = tk.Label(self.steps_frame, text="", bg=PANEL, fg=MUTED, font=F["small"])
        self.steps_label.pack(side="left", padx=12)

        bwrap = tk.Frame(inner, bg=PANEL_2)
        bwrap.pack(fill="x", pady=(14, 0))
        self.banner_bar = tk.Frame(bwrap, bg=BORDER, width=4)
        self.banner_bar.pack(side="left", fill="y")
        self.banner = tk.Label(bwrap, text="", bg=PANEL_2, fg=TEXT, font=F["bodys"], anchor="w",
                               justify="left", wraplength=480, padx=14, pady=12)
        self.banner.pack(side="left", fill="x", expand=True)

        # Shown when a line is finished (not packed until then).
        self.done_bar = tk.Frame(inner, bg=PANEL)
        row = tk.Frame(self.done_bar, bg=PANEL)
        row.pack(fill="x")
        self.done_next_btn = FlatButton(row, "Next line  (Enter)", self.next_line, "primary", takefocus=0)
        self.done_next_btn.pack(side="left")
        FlatButton(row, "Back to dashboard", self.show_overview, "ghost", takefocus=0).pack(side="left", padx=8)
        self.done_label = tk.Label(self.done_bar, text="", bg=PANEL, fg=MUTED, font=F["small"], anchor="w")
        self.done_label.pack(fill="x", pady=(6, 0))

        btns = tk.Frame(inner, bg=PANEL)
        btns.pack(side="bottom", fill="x", pady=(14, 0))
        for i, (text, cmd) in enumerate((("Hint", self.show_hint), ("Show move", self.reveal_move),
                                         ("Restart", self.restart_line), ("Skip line", self.skip_line))):
            FlatButton(btns, text, cmd, "ghost", padx=8).grid(row=0, column=i, sticky="ew",
                                                              padx=(0 if i == 0 else 8, 0))
            btns.columnconfigure(i, weight=1, uniform="b")
        tk.Label(inner, text="Keys: H hint  S show  R restart  N skip  Enter next  Esc back",
                 bg=PANEL, fg=DIM, font=F["small"], anchor="w").pack(side="bottom", fill="x", pady=(10, 0))

        nh = tk.Frame(inner, bg=PANEL)
        nh.pack(fill="x", pady=(18, 6))
        tk.Label(nh, text="NOTATION", bg=PANEL, fg=MUTED, font=F["smalls"]).pack(side="left")
        self.notation_hint = tk.Label(nh, text="", bg=PANEL, fg=DIM, font=F["small"])
        self.notation_hint.pack(side="right")
        nf = tk.Frame(inner, bg=BORDER, padx=1, pady=1)
        nf.pack(fill="both", expand=True)
        self.notation = tk.Text(nf, wrap="word", font=F["body"], bg=BG, fg=TEXT, relief="flat", bd=0,
                                padx=14, pady=12, highlightthickness=0, cursor="arrow", height=8,
                                spacing1=2, spacing3=2)
        nsb = ttk.Scrollbar(nf, orient="vertical", command=self.notation.yview)
        self.notation.configure(yscrollcommand=nsb.set, state="disabled")
        self.notation.bind("<Button-1>", self.on_notation_click)
        self.notation.bind("<Motion>", self.on_notation_motion)
        self.notation.pack(side="left", fill="both", expand=True)
        nsb.pack(side="right", fill="y")
        # Tag order sets priority: later = higher.
        t = self.notation
        t.tag_configure("main", font=F["move"], foreground=TEXT)
        t.tag_configure("side", background=SIDE_TEXT_BG, foreground=YELLOW, font=F["sidemove"])
        t.tag_configure("comment", foreground="#b3a9d9", font=F["italic"])
        t.tag_configure("sidecomment", foreground="#d8c674", font=F["italic"])
        t.tag_configure("varblock", lmargin1=16, lmargin2=16, spacing1=4, spacing3=4)
        t.tag_configure("path", foreground=COBALT_SOFT)
        t.tag_configure("sidepath", foreground="#fff6c2", underline=True)
        t.tag_configure("hidden", foreground=DIM)
        t.tag_configure("current", background=LIME, foreground=BG)

    # ------------------------------------------------------------- navigation
    def show_library(self):
        self.gen += 1
        self.session = None
        self.awaiting = False
        self.overview.pack_forget()
        self.study.pack_forget()
        self.library.pack(fill="both", expand=True)
        self.screen = "library"
        self.refresh_library()

    def show_overview(self):
        if not self.course:
            self.show_library()
            return
        self.gen += 1
        self.session = None
        self.awaiting = False
        self.study.pack_forget()
        self.library.pack_forget()
        self.overview.pack(fill="both", expand=True)
        self.screen = "overview"
        self.refresh_overview()

    def show_study(self):
        self.overview.pack_forget()
        self.library.pack_forget()
        self.study.pack(fill="both", expand=True)
        self.screen = "study"

    def go_back(self):
        if self.screen == "study":
            self.show_overview()
        elif self.screen == "overview":
            self.show_library()

    def on_close(self):
        if self.progress:
            self.progress.save()
        self.root.destroy()

    # ---------------------------------------------------------------- library
    def _build_library(self):
        lib = self.library = tk.Frame(self.body, bg=BG)
        wrap = tk.Frame(lib, bg=BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=24)
        top = tk.Frame(wrap, bg=BG)
        top.pack(fill="x")
        tk.Label(top, text="My courses", bg=BG, fg=TEXT, font=F["num"]).pack(side="left")
        self.lib_paste_btn = FlatButton(top, "Paste lines", self.paste_dialog, "ghost")
        self.lib_paste_btn.pack(side="right")
        self.lib_add_btn = FlatButton(top, "Add PGN course", self.upload_pgn, "primary")
        self.lib_add_btn.pack(side="right", padx=8)
        tk.Label(wrap, text="Every PGN you add (or set of pasted lines) is its own course with its own progress.",
                 bg=BG, fg=MUTED, font=F["body"]).pack(anchor="w", pady=(4, 12))
        self.loading_label = tk.Label(wrap, text="", bg=BG, fg=LIME, font=F["bodys"])
        self.loading_label.pack(anchor="w", pady=(0, 8))

        box = card(wrap)
        box.pack(fill="both", expand=True)
        tf = tk.Frame(box, bg=PANEL)
        tf.pack(fill="both", expand=True, padx=4, pady=4)
        self.lib_tree = ttk.Treeview(tf, columns=("lines", "learned", "due", "opened"),
                                     show="tree headings", selectmode="browse")
        for col, text, width in (("#0", "COURSE", 420), ("lines", "LINES", 110), ("learned", "LEARNED", 130),
                                 ("due", "DUE NOW", 130), ("opened", "LAST OPENED", 140)):
            self.lib_tree.heading(col, text=text, anchor="w")
            self.lib_tree.column(col, width=width, stretch=(col == "#0"))
        ysb = ttk.Scrollbar(tf, orient="vertical", command=self.lib_tree.yview)
        self.lib_tree.configure(yscrollcommand=ysb.set)
        self.lib_tree.pack(side="left", fill="both", expand=True)
        ysb.pack(side="right", fill="y")
        self.lib_tree.tag_configure("course", font=F["bodys"])
        self.lib_tree.tag_configure("missing", foreground=DIM)
        self.lib_tree.bind("<Double-1>", lambda e: (self.open_selected_course(), "break")[1])
        self.lib_tree.bind("<Return>", lambda e: self.open_selected_course())
        self.lib_empty = tk.Label(box, text="No courses yet. Add a PGN file or paste lines to create one.",
                                  bg=PANEL, fg=MUTED, font=F["body"])

        bottom = tk.Frame(wrap, bg=BG)
        bottom.pack(fill="x", pady=(16, 0))
        FlatButton(bottom, "Open course", self.open_selected_course, "accent").pack(side="left")
        FlatButton(bottom, "Rename", self.rename_selected_course, "ghost").pack(side="left", padx=(8, 0))
        FlatButton(bottom, "Remove from list", self.remove_selected_course, "ghost").pack(side="left", padx=8)
        self.lib_menu = tk.Menu(self.root, tearoff=0, bg=PANEL_2, fg=TEXT, activebackground=PURPLE,
                                activeforeground="white", bd=0, font=F["body"])
        self.lib_menu.add_command(label="Open", command=self.open_selected_course)
        self.lib_menu.add_command(label="Rename...", command=self.rename_selected_course)
        self.lib_menu.add_separator()
        self.lib_menu.add_command(label="Reset progress...", command=self.reset_selected_course_progress,
                                  foreground="#ff8aa1")
        self.lib_menu.add_command(label="Remove from list", command=self.remove_selected_course)
        self.lib_tree.bind("<Button-3>", self._lib_right_click)
        self.lib_tree.bind("<F2>", lambda e: self.rename_selected_course())
        FlatButton(bottom, "Delete all progress", self.reset_all_progress, "danger").pack(side="right")
        FlatButton(bottom, "Reset progress", self.reset_selected_course_progress, "danger").pack(side="right", padx=8)

    def _save_cfg(self):
        self.cfg["courses"] = self.courses
        save_config(self.cfg)

    def _course_entry(self, path):
        key = os.path.normcase(os.path.abspath(path))
        for e in self.courses:
            if os.path.normcase(os.path.abspath(e["path"])) == key:
                return e
        return None

    def _due_moves(self, path):
        prog = self.progress_cache.get(os.path.abspath(path))
        now = time.time()
        if prog is not None:
            cards = prog.cards.values()
        else:
            try:
                with open(progress_path_for(path), encoding="utf-8") as f:
                    cards = json.load(f).get("cards", {}).values()
            except Exception:
                return 0
        return sum(1 for c in cards if c[0] > 0 and c[1] <= now)

    def refresh_library(self):
        tree = self.lib_tree
        tree.delete(*tree.get_children())
        current = os.path.normcase(os.path.abspath(self.course.path)) if self.course else None
        select = None
        for i, e in enumerate(self.courses):
            exists = os.path.isfile(e["path"])
            st = e.get("stats") or {}
            lines, learned = st.get("lines"), st.get("learned")
            opened = e.get("opened")
            vals = ("-" if lines is None else str(lines),
                    "-" if lines is None else f"{learned} / {lines}",
                    plural(self._due_moves(e["path"]), "move") if exists else "File missing",
                    time.strftime("%b %d, %H:%M", time.localtime(opened)) if opened else "Never")
            iid = f"k{i}"
            tree.insert("", "end", iid=iid, text=f"  {e.get('name') or os.path.basename(e['path'])}",
                        values=vals, tags=("course",) if exists else ("course", "missing"))
            if current and os.path.normcase(os.path.abspath(e["path"])) == current:
                select = iid
        if self.courses:
            self.lib_empty.place_forget()
            target = select or "k0"
            tree.selection_set(target)
            tree.focus(target)
        else:
            self.lib_empty.place(relx=0.5, rely=0.4, anchor="center")

    def _selected_course_entry(self):
        sel = self.lib_tree.selection()
        if not sel:
            return None
        return self.courses[int(sel[0][1:])]

    def open_selected_course(self):
        e = self._selected_course_entry()
        if e is not None:
            self.open_course(e["path"])

    def open_course(self, path):
        if self.loading:
            return
        path = os.path.abspath(path)
        if not os.path.isfile(path):
            messagebox.showerror("File missing", f"This course's PGN file can't be found:\n{path}")
            return
        cached = self.course_cache.get(os.path.normcase(path))
        if cached and cached[1] == os.path.getmtime(path):
            self._activate_course(cached[0], announce=False)
        else:
            self.start_loading(path, announce=False)

    def _lib_right_click(self, event):
        iid = self.lib_tree.identify_row(event.y)
        if iid:
            self.lib_tree.selection_set(iid)
            self.lib_tree.focus(iid)
            self.lib_menu.tk_popup(event.x_root, event.y_root)

    def ask_text(self, title, prompt, initial=""):
        """Small dark text-input dialog. Returns the text, or None if cancelled."""
        top = tk.Toplevel(self.root, bg=BG)
        top.title(title)
        top.resizable(False, False)
        top.transient(self.root)
        style_title_bar(top)
        wrap = tk.Frame(top, bg=BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=20)
        tk.Label(wrap, text=prompt, bg=BG, fg=TEXT, font=F["bodys"]).pack(anchor="w")
        var = tk.StringVar(value=initial)
        ef = tk.Frame(wrap, bg=BORDER, padx=1, pady=1)
        ef.pack(fill="x", pady=(6, 16))
        entry = tk.Entry(ef, textvariable=var, bg=PANEL, fg=TEXT, insertbackground=LIME, relief="flat",
                         font=F["body"], bd=0, width=48)
        entry.pack(fill="x", ipady=7, ipadx=8)
        result = {"value": None}

        def ok(_e=None):
            result["value"] = var.get()
            top.destroy()

        btns = tk.Frame(wrap, bg=BG)
        btns.pack(fill="x")
        FlatButton(btns, "Save", ok, "primary").pack(side="right")
        FlatButton(btns, "Cancel", top.destroy, "ghost").pack(side="right", padx=8)
        entry.bind("<Return>", ok)
        entry.bind("<Escape>", lambda e: top.destroy())
        entry.focus_set()
        entry.select_range(0, "end")
        top.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - top.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - top.winfo_height()) // 3
        top.geometry(f"+{max(0, x)}+{max(0, y)}")
        top.grab_set()
        self.root.wait_window(top)
        return result["value"]

    def rename_selected_course(self):
        e = self._selected_course_entry()
        if e is None:
            return
        old = e.get("name") or os.path.splitext(os.path.basename(e["path"]))[0]
        new = self.ask_text("Rename course", "Course name", old)
        if new is None or not new.strip() or new.strip() == old:
            return
        e["name"] = new.strip()
        if self.course and os.path.normcase(os.path.abspath(self.course.path)) == \
                os.path.normcase(os.path.abspath(e["path"])):
            self.course.name = e["name"]
            self.course_label.config(text=self.course.name)
        self._save_cfg()
        self.refresh_library()

    def remove_selected_course(self):
        e = self._selected_course_entry()
        if e is None:
            return
        name = e.get("name") or os.path.basename(e["path"])
        if not messagebox.askyesno("Remove course", f"Remove \"{name}\" from your course list?\n\n"
                                                    "The PGN file and its progress file are not deleted."):
            return
        self.courses.remove(e)
        if self.course and os.path.normcase(os.path.abspath(self.course.path)) == \
                os.path.normcase(os.path.abspath(e["path"])):
            if self.progress:
                self.progress.save()
            self.course, self.progress = None, None
            self.course_label.config(text="")
        self._save_cfg()
        self.refresh_library()

    # ---------------------------------------------------------- reset progress
    def _reset_course_progress(self, path):
        """Forget every learned move and review date for one course. The course itself,
        its PGN file and its settings (colour, sidelines) are kept."""
        path = os.path.abspath(path)
        prog = self.progress_cache.get(path)
        if prog is None:
            if not os.path.isfile(progress_path_for(path)):
                return
            prog = Progress(path)
        prog.cards.clear()
        prog.save()
        entry = self._course_entry(path)
        if entry is not None and entry.get("stats"):
            entry["stats"]["learned"] = 0

    def _confirm_reset(self, what):
        return messagebox.askyesno(
            "Reset progress",
            f"Delete all progress for {what}?\n\n"
            "Every learned move and review date will be erased and all lines become new again. "
            "The course and its PGN file are kept.\n\nThis cannot be undone.",
            icon="warning", default="no")

    def reset_current_course_progress(self):
        if not self.course or not self._confirm_reset(f"\"{self.course.name}\""):
            return
        self._reset_course_progress(self.course.path)
        self._save_cfg()
        self.refresh_overview()

    def on_tree_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid or iid.endswith("_dummy"):
            return
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        multi = iid.startswith("c")
        self.tree_menu.entryconfig(2, label="Reset progress for all lines in this chapter" if multi
                                   else "Reset progress for this line")
        self.tree_menu.tk_popup(event.x_root, event.y_root)

    def reset_selected_lines(self):
        """Reset one line (or every line of a selected chapter) without touching the rest."""
        if not self.course:
            return
        sel = self.tree.selection()
        if not sel or sel[0].endswith("_dummy"):
            messagebox.showinfo("Reset line", "Select a line in the course contents first.")
            return
        iid = sel[0]
        if iid.startswith("c"):
            ch = self.course.chapters[int(iid[1:])]
            lines, what = list(ch.lines), f"all {plural(len(ch.lines), 'line')} in \"{short(ch.title(), 50)}\""
        else:
            line = self.course.lines[int(iid[1:])]
            lines = [line]
            what = f"\"{short(line.chapter.title(), 50)}\"" + ("" if line.is_main else f" ({line.label})")
        keys = {k for l in lines for k in l.keys}
        learned = {k for k in keys if self.progress.level(k) > 0}
        if not learned:
            messagebox.showinfo("Reset line", "This line has no progress to reset yet.")
            return
        # Progress is stored per move, and lines share moves (every 1.e4 line shares 1.e4).
        # Only reset moves that no other learned line uses, so the rest of the course is untouched.
        chosen = {id(l) for l in lines}
        now = time.time()
        protected, sharing = set(), 0
        for l in self.course.lines:
            if id(l) in chosen or self.progress.line_status(l, now)[0] == "new":
                continue
            common = learned.intersection(l.keys)
            if common:
                protected |= common
                sharing += 1
        unique = learned - protected
        if unique:
            kept = len(learned) - len(unique)
            note = (f"\n\n{plural(kept, 'move')} shared with other learned lines (like the opening moves) "
                    "stay learned, so the rest of your course is not affected." if kept else "")
            if not messagebox.askyesno("Reset line progress",
                                       f"Reset progress for {what}?\n\n{plural(len(unique), 'move')} of this line "
                                       f"will become new again and the line goes back to Learn.{note}\n\n"
                                       "This cannot be undone.", icon="warning", default="no"):
                return
            to_reset = unique
        else:
            if not messagebox.askyesno("Reset line progress",
                                       f"Every move of {what} is also part of "
                                       f"{plural(sharing, 'other learned line')}, so it can't be reset on its own."
                                       f"\n\nReset it anyway? Those {plural(sharing, 'line')} will need "
                                       "re-learning too.\n\nThis cannot be undone.", icon="warning", default="no"):
                return
            to_reset = learned
        for k in to_reset:
            self.progress.cards.pop(k, None)
        self.progress.save()
        self.refresh_overview()
        if self.tree.exists(iid):
            self.tree.selection_set(iid)
            self.tree.focus(iid)
            self.tree.see(iid)

    def reset_selected_course_progress(self):
        e = self._selected_course_entry()
        if e is None or not self._confirm_reset(f"\"{e.get('name') or os.path.basename(e['path'])}\""):
            return
        self._reset_course_progress(e["path"])
        self._save_cfg()
        self.refresh_library()

    def reset_all_progress(self):
        if not self.courses or not self._confirm_reset(f"ALL {plural(len(self.courses), 'course')}"):
            return
        for e in self.courses:
            self._reset_course_progress(e["path"])
        self._save_cfg()
        self.refresh_library()

    # ---------------------------------------------------------------- loading
    def _set_loading_buttons(self, enabled):
        for btn, kind in ((self.upload_btn, "primary"), (self.lib_add_btn, "primary"),
                          (self.lib_paste_btn, "ghost")):
            btn.set_kind(kind, enabled=enabled)

    def upload_pgn(self):
        if self.loading:
            return
        path = filedialog.askopenfilename(title="Open PGN file",
                                          filetypes=[("PGN files", "*.pgn *.PGN"), ("All files", "*.*")])
        if path:
            self.start_loading(path, announce=True)

    def paste_dialog(self):
        if self.loading:
            return
        top = tk.Toplevel(self.root, bg=BG)
        top.title("Paste lines")
        top.geometry("780x600")
        top.transient(self.root)
        style_title_bar(top)
        wrap = tk.Frame(top, bg=BG)
        wrap.pack(fill="both", expand=True, padx=24, pady=20)
        tk.Label(wrap, text="Paste lines", bg=BG, fg=TEXT, font=F["h2"]).pack(anchor="w")
        tk.Label(wrap, text="PGN or text copied from ChessBase. Comments, [variations], (variations), symbols "
                            "and [%cal] arrows are fine. Without PGN headers, each line starting with \"1.\" "
                            "becomes its own chapter.",
                 bg=BG, fg=MUTED, font=F["small"], justify="left", wraplength=720).pack(anchor="w", pady=(4, 14))
        tk.Label(wrap, text="Course name", bg=BG, fg=TEXT, font=F["bodys"]).pack(anchor="w")
        name_var = tk.StringVar(value=time.strftime("Pasted %Y-%m-%d %H%M"))
        ef = tk.Frame(wrap, bg=BORDER, padx=1, pady=1)
        ef.pack(fill="x", pady=(4, 14))
        tk.Entry(ef, textvariable=name_var, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="flat",
                 font=F["body"], bd=0).pack(fill="x", ipady=7, ipadx=8)
        tk.Label(wrap, text="Moves", bg=BG, fg=TEXT, font=F["bodys"]).pack(anchor="w")
        tf = tk.Frame(wrap, bg=BORDER, padx=1, pady=1)
        tf.pack(fill="both", expand=True, pady=(4, 0))
        txt = tk.Text(tf, bg=PANEL, fg=TEXT, insertbackground=LIME, relief="flat", bd=0,
                      font=("Consolas", 10), wrap="word", padx=10, pady=8, highlightthickness=0)
        txt.pack(fill="both", expand=True)
        txt.focus_set()
        btns = tk.Frame(wrap, bg=BG)
        btns.pack(fill="x", pady=(16, 0))

        def create():
            content = txt.get("1.0", "end").strip()
            if not content:
                messagebox.showwarning("Nothing pasted", "Paste some moves first.", parent=top)
                return
            name = re.sub(r'[\\/:*?"<>|]+', "_", name_var.get().strip()) or "Pasted lines"
            folder = os.path.join(APP_DIR, "pasted")
            try:
                os.makedirs(folder, exist_ok=True)
                path = os.path.join(folder, name + ".pgn")
                with open(path, "w", encoding="utf-8") as f:
                    f.write(prepare_pasted_text(content, name))
            except Exception as exc:
                messagebox.showerror("Error", f"Could not save the pasted lines:\n{exc}", parent=top)
                return
            top.destroy()
            self.start_loading(path, announce=True)

        FlatButton(btns, "Create course", create, "primary").pack(side="right")
        FlatButton(btns, "Cancel", top.destroy, "ghost").pack(side="right", padx=8)

    def start_loading(self, path, announce):
        self.loading = True
        self._set_loading_buttons(False)
        if self.progress:
            self.progress.save()
        self.show_library()
        self.loading_label.config(text=f"Loading {os.path.basename(path)} ...")

        def worker():
            try:
                course = load_course(path, progress=lambda i, t: self.load_queue.put(("progress", i, t)))
                self.load_queue.put(("done", course, announce))
            except Exception as exc:
                self.load_queue.put(("error", exc))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(100, self._poll_loader)

    def _poll_loader(self):
        try:
            while True:
                msg = self.load_queue.get_nowait()
                if msg[0] == "progress":
                    self.loading_label.config(text=f"Loading... {msg[1]} / {msg[2]} games")
                elif msg[0] in ("error", "done"):
                    self.loading = False
                    self._set_loading_buttons(True)
                    self.loading_label.config(text="")
                    if msg[0] == "error":
                        messagebox.showerror("Error", f"Could not read the PGN file:\n{msg[1]}")
                    else:
                        self._on_loaded(msg[1], msg[2])
                    return
        except queue.Empty:
            pass
        self.root.after(100, self._poll_loader)

    def _on_loaded(self, course, announce):
        if not course.all_chapters:
            messagebox.showwarning("No games", "No playable games were found.")
            self.refresh_library()
            return
        path = os.path.abspath(course.path)
        self.course_cache[os.path.normcase(path)] = (course, os.path.getmtime(path))
        self._activate_course(course, announce)

    def _activate_course(self, course, announce):
        if self.progress:
            self.progress.save()
        path = os.path.abspath(course.path)
        self.course = course
        self.progress = self.progress_cache.get(path) or Progress(path)
        self.progress_cache[path] = self.progress
        self.color_var.set(self.progress.color)
        course.color = self.user_color
        mode = self.progress.train_sidelines
        course.apply_sideline_mode((not course.is_chessable) if mode is None else mode)

        entry = self._course_entry(path)
        if entry is None:
            entry = {"path": path, "name": course.name, "added": time.time()}
            self.courses.append(entry)
        entry["opened"] = time.time()
        course.name = entry.get("name") or course.name     # a renamed course keeps its name
        self.cfg["last_pgn"] = path
        self._save_cfg()

        self.course_label.config(text=course.name)
        self.filled_chapters.clear()
        self.show_overview()
        if announce:
            n_side = sum(1 for ch in course.all_chapters for l in ch.all_lines if not l.is_main)
            msg = (f"{plural(len(course.lines), 'line')} to learn in {plural(len(course.chapters), 'chapter')}, "
                   f"from {plural(course.total_entries, 'game')}.")
            if n_side and not course.train_sidelines:
                msg += (f"\n\nThe games also contain {plural(n_side, 'sideline')} of commentary. They are shown "
                        f"in yellow in the notation but not trained. Use the Sidelines button to train them too.")
            if course.skipped:
                msg += f"\n\n{plural(course.skipped, 'game')} skipped because of illegal moves."
            messagebox.showinfo("Course added", msg)

    # --------------------------------------------------------------- overview
    def toggle_sidelines(self):
        if not self.course:
            return
        flag = not self.course.train_sidelines
        self.course.apply_sideline_mode(flag)
        self.progress.train_sidelines = flag
        self.progress.save()
        self.filled_chapters.clear()
        self.refresh_overview()

    def refresh_overview(self):
        if not self.course:
            return
        c, p, now = self.course, self.progress, time.time()
        self.statuses = [p.line_status(l, now) for l in c.lines]
        n_new = sum(1 for s in self.statuses if s[0] == "new")
        n_due = sum(1 for s in self.statuses if s[0] == "due")
        n_learned = sum(1 for s in self.statuses if s[0] in ("due", "learned"))

        levels = [0] * (MAX_LEVEL + 1)
        due_now = due_day = due_week = 0
        for k in c.user_keys:
            lvl, due = p.get(k)
            levels[lvl] += 1
            if lvl:
                if due <= now:
                    due_now += 1
                elif due <= now + DAY:
                    due_day += 1
                elif due <= now + 7 * DAY:
                    due_week += 1
        learned_moves = len(c.user_keys) - levels[0]

        self.tile_vars["new"].config(text=str(n_new))
        self.tile_vars["due"].config(text=str(n_due))
        self.tile_vars["learned"].config(text=f"{n_learned} / {n_learned + n_new}")
        self.tile_vars["moves"].config(text=f"{learned_moves} / {len(c.user_keys)}")
        self.learn_btn.config(text=f"Learn  {n_new} new")
        self.learn_btn.set_kind("primary", enabled=bool(n_new))
        self.review_btn.config(text=f"Review  {n_due} due")
        self.review_btn.set_kind("accent", enabled=bool(n_due))
        self.side_btn.config(text="Sidelines: trained as lines" if c.train_sidelines else "Sidelines: notes only")
        info = plural(c.total_entries, "game")
        if c.skipped:
            info += f"\n{c.skipped} skipped"
        self.load_info.config(text=info)
        hard = sum(1 for k in c.user_keys if p.lapses(k))
        for v, n in zip(self.upcoming_vals, (due_now, due_day, due_week, hard)):
            v.config(text=plural(n, "move"))
        self.draw_chart(levels)
        self.rebuild_tree()

        entry = self._course_entry(c.path)
        if entry is not None:
            entry["stats"] = {"lines": n_learned + n_new, "learned": n_learned}
            self._save_cfg()

    def draw_chart(self, levels):
        cv = self.chart
        cv.delete("all")
        w, h = int(cv["width"]), int(cv["height"])
        mx = max(max(levels[1:]), 1)
        bw = w / MAX_LEVEL
        base = h - 20
        for i in range(1, MAX_LEVEL + 1):
            x0 = (i - 1) * bw + 5
            x1 = x0 + bw - 10
            bh = max(2, (base - 20) * levels[i] / mx)
            cv.create_rectangle(x0, base - bh, x1, base, fill=LEVEL_COLORS[i] if levels[i] else BORDER, outline="")
            if levels[i]:
                cv.create_text((x0 + x1) / 2, base - bh - 8, text=str(levels[i]), font=F["coord"], fill=TEXT)
            cv.create_text((x0 + x1) / 2, h - 8, text=LEVEL_LABELS[i], font=F["coord"], fill=MUTED)

    def line_status_text(self, line):
        st, due, lvl = self.statuses[line.index]
        if st == "empty":
            return "No moves for you", "", "empty"
        if st == "new":
            return "New", "", "new"
        hard = "  - hard" if any(self.progress.lapses(k) for k in line.keys) else ""
        if st == "due":
            return f"Due  (level {lvl}){hard}", "now", "due"
        return f"Level {lvl}{hard}", fmt_delta(due - time.time()), "learned"

    def rebuild_tree(self):
        tree = self.tree
        open_ids = {iid for iid in tree.get_children() if tree.item(iid, "open")}
        tree.delete(*tree.get_children())
        self.filled_chapters.clear()
        now = time.time()
        for ci, ch in enumerate(self.course.chapters):
            if len(ch.lines) == 1:                     # one line: the row *is* the line
                line = ch.lines[0]
                status, nxt, tag = self.line_status_text(line)
                tree.insert("", "end", iid=f"l{line.index}", text=f"  {ch.number}.  {short(ch.title(), 44)}",
                            values=(status, nxt), tags=["chapter", tag])
                continue
            n_new = n_due = n_empty = 0
            soonest = None
            for l in ch.lines:
                st, due, _ = self.statuses[l.index]
                if st == "new":
                    n_new += 1
                elif st == "due":
                    n_due += 1
                elif st == "empty":
                    n_empty += 1
                if due is not None and (soonest is None or due < soonest):
                    soonest = due
            if n_new or n_due:
                summary = ", ".join(x for x in (f"{n_new} new" if n_new else "", f"{n_due} due" if n_due else "") if x)
            elif n_empty == len(ch.lines):
                summary = "-"
            else:
                summary = "Learned"
            tags = ["chapter"] + (["due"] if n_due else [])
            iid = f"c{ci}"
            tree.insert("", "end", iid=iid, text=f"  {ch.number}.  {short(ch.title(), 36)}   ({plural(len(ch.lines), 'line')})",
                        values=(summary, fmt_delta(soonest - now) if soonest else ""), tags=tags)
            tree.insert(iid, "end", iid=f"{iid}_dummy", text="")
            if iid in open_ids:
                self._fill_chapter(iid)
                tree.item(iid, open=True)

    def _fill_chapter(self, iid):
        if iid in self.filled_chapters:
            return
        self.filled_chapters.add(iid)
        if self.tree.exists(f"{iid}_dummy"):
            self.tree.delete(f"{iid}_dummy")
        ch = self.course.chapters[int(iid[1:])]
        for line in ch.lines:
            status, nxt, tag = self.line_status_text(line)
            tags = [tag] + ([] if line.is_main else ["side"])
            self.tree.insert(iid, "end", iid=f"l{line.index}", text=line.label, values=(status, nxt), tags=tags)

    def on_tree_open(self, _event):
        iid = self.tree.focus()
        if iid.startswith("c"):
            self._fill_chapter(iid)

    def _line_for_iid(self, iid):
        if iid.startswith("l"):
            return self.course.lines[int(iid[1:])]
        if iid.startswith("c") and "_" not in iid:
            ch = self.course.chapters[int(iid[1:])]
            return next((l for l in ch.lines if self.statuses[l.index][0] in ("new", "due")), ch.lines[0])
        return None

    def on_tree_double(self, event):
        line = self._line_for_iid(self.tree.identify_row(event.y))
        if line is not None:
            self.open_line(line)
        return "break"

    def open_selected_line(self):
        sel = self.tree.selection()
        line = self._line_for_iid(sel[0]) if sel else None
        if line is not None:
            self.open_line(line)

    def open_line(self, line):
        """Open one line: learn it if it is new, otherwise review it."""
        st = self.progress.line_status(line, time.time())[0]
        if st == "empty":
            messagebox.showinfo("Nothing to train", "This line has no moves for your side.")
            return
        self.start_session("learn" if st == "new" else "review", [line], single=True)

    def selected_line_index(self):
        sel = self.tree.selection()
        if not sel:
            return 0
        line = self._line_for_iid(sel[0])
        return line.index if line is not None else 0

    # --------------------------------------------------------------- sessions
    @property
    def user_color(self):
        return chess.WHITE if self.color_var.get() == "white" else chess.BLACK

    def start_learn(self):
        if self.course:
            self.start_session("learn", [l for l in self.course.lines if self.statuses[l.index][0] == "new"])

    def start_review(self):
        if self.course:
            self.start_session("review", [l for l in self.course.lines if self.statuses[l.index][0] == "due"])

    def start_drill(self):
        if self.course:
            self.start_session("drill", self.course.lines[self.selected_line_index():])

    def start_session(self, mode, lines, single=False):
        lines = [l for l in lines if l.keys]
        if not lines:
            messagebox.showinfo("Nothing to do", "There are no lines for this mode right now.")
            return
        self.session = Session(mode, lines, single)
        self.show_study()
        self.load_session_line()

    def _peek_queue(self):
        """Index of the next session line still worth playing (or None). Lines can stop
        being new/due mid-session because moves are shared between lines."""
        s = self.session
        if s is None:
            return None
        now = time.time()
        for i in range(s.pos, len(s.queue)):
            line, retest = s.queue[i]
            if retest or s.single or s.mode == "drill":
                return i
            st = self.progress.line_status(line, now)[0]
            if (s.mode == "learn" and st == "new") or (s.mode == "review" and st == "due"):
                return i
        return None

    def _next_course_line(self, line):
        """The next line after `line` in course order that has moves for you."""
        if self.course is None or line is None:
            return None
        for l in self.course.lines[line.index + 1:]:
            if l.keys:
                return l
        return None

    def load_session_line(self):
        s = self.session
        if s is None:
            return
        self.hide_done_bar()
        i = self._peek_queue()
        if i is None:
            s.pos = len(s.queue)
            self.session_complete()
            return
        s.pos = i

        line, retest = s.queue[s.pos]
        self.line, self.retest = line, retest
        self.learn_phase = (s.mode == "learn")
        self.streak = 0
        self.line_done = False

        mode_text, bg, fg = {"learn": ("LEARN", LIME, BG), "review": ("REVIEW", COBALT, "white"),
                             "drill": ("DRILL", PURPLE, "white")}[s.mode]
        if retest:
            mode_text, bg, fg = "RE-TEST", RED, "white"
        self.mode_pill.config(text=mode_text, bg=bg, fg=fg)
        ch = line.chapter
        self.chapter_label.config(text=f"Chapter {ch.number}")
        self.title_label.config(text=ch.title())
        self.line_label.config(text=line.label, bg=PANEL if line.is_main else SIDE_TEXT_BG,
                               fg=MUTED if line.is_main else YELLOW, padx=0 if line.is_main else 6)
        self.set_progress((100 * s.pos / len(s.queue)) / 100)
        self.begin_run()

    def begin_run(self):
        """Start (or restart) playing the current line from its first move."""
        s = self.session
        line = self.line
        self.gen += 1
        self.board = line.chapter.new_board()
        self.ply = 0
        self.line_failed = self.step_failed = False
        self.awaiting = False
        self.selected = None
        self.hl, self.arrows, self.shapes, self.last_move = {}, [], [], None
        self.preview = False
        self.reveal = s.mode == "learn" and self.learn_phase
        if self.reveal and line.chapter.root.shapes:
            self.shapes = line.chapter.root.shapes
        self.update_pips()
        self.update_session_label()
        self.draw_board()
        self.render_notation()
        if line.nodes[0].turn != self.user_color:
            self.set_banner("Watch the opponent's move...", "neutral")
        self.advance()

    def update_session_label(self):
        s = self.session
        self.session_label.config(text=f"Line {s.pos + 1} of {len(s.queue)}")

    def set_progress(self, frac):
        cv = self.session_bar
        cv.delete("all")
        cv.create_rectangle(0, 0, BOARD_PX * max(0.0, min(1.0, frac)), 4, fill=LIME, outline="")

    def update_pips(self):
        """Step indicator for Learn mode: [Learn][Drill 1][Drill 2][Drill 3] as thin segments."""
        s = self.session
        if not s or s.mode != "learn":
            self.steps_frame.pack_forget()
            self.notation_hint.config(text="")
            return
        self.steps_frame.pack(fill="x", pady=(14, 0), before=self.banner.master)
        cv = self.steps
        cv.delete("all")
        n = DRILL_REPS + 1
        seg_w, gap = 52, 8
        for i in range(n):
            if i == 0:
                state = "current" if self.learn_phase else "done"
            elif self.learn_phase:
                state = "todo"
            else:
                state = "done" if i <= self.streak else ("current" if i == self.streak + 1 else "todo")
            color = {"done": LIME, "current": COBALT, "todo": BORDER}[state]
            x = i * (seg_w + gap)
            cv.create_rectangle(x, 1, x + seg_w, 7, fill=color, outline="")
        self.notation_hint.config(text="Click any move to jump there" if self.learn_phase else "")
        if self.learn_phase:
            text = "Learn the line"
        elif self.streak >= DRILL_REPS:
            text = f"Learned: {DRILL_REPS} clean runs in a row"
        else:
            text = f"Drill {self.streak + 1} of {DRILL_REPS} in a row"
        self.steps_label.config(text=text)

    def advance(self):
        line = self.line
        if self.ply >= len(line.nodes):
            self.line_complete()
            return
        node = line.nodes[self.ply]
        if node.turn == self.user_color:
            self.awaiting = True
            self.step_failed = False
            mode = self.session.mode
            if mode == "learn" and self.learn_phase:
                prev = line.nodes[self.ply - 1] if self.ply else line.chapter.root
                notes = " ".join(x for x in (prev.comment, node.pre) if x)
                if self.progress.level(node.key) == 0:
                    self.arrows = [(node.move.from_square, node.move.to_square, ARROW_LEARN)]
                    msg = f"New move: play {move_label(node)}{node.suffix}"
                else:
                    msg = "You already know this move. Play it from memory."
                if notes:
                    msg += "\n\n" + notes[:420]
                self.set_banner(msg, "learn")
            elif mode == "learn":
                self.set_banner(f"Drill {self.streak + 1} of {DRILL_REPS}: your move.", "info")
            else:
                self.set_banner("Your move. What do you play here?", "info")
            self.draw_board()
        else:
            self.awaiting = False
            gen = self.gen
            delay = OPPONENT_DELAY_MS if self.reveal or self.session.mode != "learn" else DRILL_OPPONENT_DELAY_MS
            self.root.after(delay, lambda: self._play_opponent(gen))

    def _play_opponent(self, gen):
        if gen != self.gen:
            return
        self.push_node(self.line.nodes[self.ply])
        self.advance()

    def push_node(self, node):
        self.board.push(node.move)
        self.ply += 1
        self.last_move = node.move
        self.selected = None
        self.hl, self.arrows = {}, []
        self.shapes = (node.shapes or []) if self.reveal else []
        self.played_ids.add(id(node))
        self.draw_board()
        if self.reveal and self.rendered_chapter is self.line.chapter:
            r = self._range(node)
            if r:
                self.notation.tag_add("path" if node.is_main else "sidepath", *r)
            self.update_current_tag()
        else:
            self.render_notation()

    def register_failure(self, node):
        s = self.session
        if not self.step_failed:
            s.mistakes += 1
            if s.mode == "review" and not self.retest:
                self.progress.fail(node.key, time.time())
                self.progress.save()
            elif s.mode == "learn" and not self.learn_phase:
                self.progress.mark_lapse(node.key)   # missed in a drill: review it sooner later
                self.progress.save()
        self.step_failed = True
        self.line_failed = True

    def try_user_move(self, from_sq, to_sq):
        if not self.awaiting:
            return
        node = self.line.nodes[self.ply]
        exp = node.move
        s = self.session
        if from_sq == exp.from_square and to_sq == exp.to_square:
            self.awaiting = False
            if s.mode == "review" and not self.retest and not self.step_failed:
                self.progress.success(node.key, time.time())
            self.push_node(node)
            self.set_banner("Correct!", "good")
            gen = self.gen
            self.root.after(250, lambda: gen == self.gen and self.advance())
            return

        cands = [m for m in self.board.legal_moves if m.from_square == from_sq and m.to_square == to_sq]
        self.selected = None
        if not cands:
            self.set_banner("Illegal move. Try again.", "bad")
            self.flash({to_sq: WRONG_COLOR})
            return
        alts = self.course.alts.get(pos_key(self.board), ())
        if any(m.uci() in alts for m in cands):
            self.set_banner("That move is a sideline in your repertoire, but this line continues "
                            "with a different move. Try again.", "side")
            self.flash({from_sq: ALT_COLOR, to_sq: ALT_COLOR}, ms=1100)
            return

        self.register_failure(node)
        if s.mode == "learn" and self.learn_phase:
            self.arrows = [(exp.from_square, exp.to_square, ARROW_LEARN)]
            self.set_banner(f"Not quite. Play {move_label(node)} (follow the arrow).", "bad")
        else:
            self.arrows = [(exp.from_square, exp.to_square, ARROW_FIX)]
            self.set_banner(f"Incorrect. The move is {move_label(node)}{node.suffix}. Play it now.", "bad")
        self.flash({to_sq: WRONG_COLOR})

    def _schedule(self, ms, fn):
        gen = self.gen
        self.root.after(ms, lambda: gen == self.gen and fn())

    def line_complete(self):
        s = self.session
        self.awaiting = False
        now = time.time()

        if s.mode == "learn":
            if self.learn_phase:
                self.learn_phase = False
                self.update_pips()
                self.set_banner(f"Line learned. Now play it {DRILL_REPS} times in a row from memory.", "good")
                self._schedule(1600, self.begin_run)
                return
            if self.line_failed:
                self.streak = 0
                msg, kind = f"There was a mistake, so the streak is reset. Again: 0 of {DRILL_REPS} done.", "bad"
            else:
                self.streak += 1
                msg, kind = f"Clean run! {self.streak} of {DRILL_REPS} in a row.", "good"
            self.update_pips()
            if self.streak < DRILL_REPS:
                self.set_banner(msg, kind)
                self._schedule(1400, self.begin_run)
                return
            for k in self.line.keys:
                self.progress.learn(k, now)

        self.line_done = True
        msg = "Line Complete!"
        if s.mode == "learn":
            msg = f"Line Complete! {DRILL_REPS} clean runs in a row. Its moves are now on your review schedule."
        if s.mode == "review" and self.line_failed and not self.retest:
            s.queue.append((self.line, True))
            msg += "\nYou made a mistake, so this line will be re-tested at the end of this session."
        s.done += 1
        self.progress.save()
        self.set_banner(msg, "good")
        self.reveal = True
        self.render_notation()
        self.set_progress((100 * (s.pos + 1) / len(s.queue)) / 100)
        s.pos += 1
        self.show_done_bar()                       # stay here: Next line / Back to dashboard

    def session_complete(self):
        s = self.session
        self.awaiting = False
        self.line_done = True
        self.gen += 1
        self.set_progress(1.0)
        self.steps_frame.pack_forget()
        self.set_banner(f"Session complete. {plural(s.done, 'line')} trained, "
                        f"{plural(s.mistakes, 'mistake')}.", "good")
        self.show_done_bar()

    # ---- end-of-line choices ----
    def show_done_bar(self):
        i = self._peek_queue()
        if i is not None:
            nxt = self.session.queue[i][0]
            where = "Next in this session"
        else:
            nxt = self._next_course_line(self.line)
            where = "Next in the course"
        if nxt is not None:
            self.done_next_btn.set_kind("primary")
            self.done_label.config(text=f"{where}: {short(nxt.chapter.title(), 40)}"
                                        + ("" if nxt.is_main else f"  ({short(nxt.label, 30)})"))
        else:
            self.done_next_btn.set_kind("primary", enabled=False)
            self.done_label.config(text="That was the last line in this course.")
        self.done_bar.pack(fill="x", pady=(12, 0), after=self.banner.master)
        self.notation_hint.config(text="Click any move to view it")

    def hide_done_bar(self):
        self.done_bar.pack_forget()

    def next_line(self):
        """Go to the next line: the rest of this session first, then the course in order."""
        if self.session is None or not self.line_done:
            return
        if self._peek_queue() is not None:
            self.load_session_line()
            return
        nxt = self._next_course_line(self.line)
        if nxt is not None:
            self.open_line(nxt)

    # ---------------------------------------------------------------- buttons
    def show_hint(self):
        if not self.awaiting or not self.session:
            return
        node = self.line.nodes[self.ply]
        self.register_failure(node)
        self.hl = {node.move.from_square: HINT_COLOR}
        self.set_banner("Hint: move the highlighted piece.", "info")
        self.draw_board()

    def reveal_move(self):
        if not self.awaiting or not self.session:
            return
        node = self.line.nodes[self.ply]
        self.register_failure(node)
        self.arrows = [(node.move.from_square, node.move.to_square, ARROW_SHOW)]
        self.set_banner(f"The move is {move_label(node)}{node.suffix}. Play it on the board.", "info")
        self.draw_board()

    def restart_line(self):
        if not self.session or self.line is None:
            return
        if self.line_done:
            self.open_line(self.line)              # play the finished line again
        else:
            self.begin_run()

    def skip_line(self):
        if not self.session:
            return
        if self.line_done:
            self.next_line()
        else:
            self.session.pos += 1
            self.load_session_line()

    def on_color_change(self):
        if not self.course:
            self.draw_board()
            return
        self.progress.color = self.color_var.get()
        self.progress.save()
        self.course.set_color(self.user_color)
        self.show_overview()

    # --------------------------------------------------------------- notation
    # The notation is built as a list of (text, tags) segments in Python and sent to
    # the Text widget in ONE insert call; huge ChessBase trees render quickly this way.
    def render_notation(self):
        t = self.notation
        t.config(state="normal")
        t.delete("1.0", "end")
        self.node_ranges = {}
        self.range_starts, self.range_ends, self.range_nodes = [], [], []
        self.rendered_chapter = None
        self._segs, self._pos = [], 0
        if self.line is not None:
            played = self.line.nodes[:self.ply]
            self.played_ids = {id(n) for n in played}
            if self.reveal:
                root = self.line.chapter.root
                if root.comment:
                    self._add(root.comment + "\n", ("comment",))
                self._emit_tree(root, 0, True, ())
                self.rendered_chapter = self.line.chapter
            else:
                for i, n in enumerate(played):
                    self._emit_move(n, i == 0, (), with_comment=False)
                self._add("  ...", ("hidden",))
        args = []                          # merge neighbours with identical tags
        for text, tags in self._segs:
            if args and args[-1] == tags:
                args[-2] += text
            else:
                args.append(text)
                args.append(tags)
        if args:
            t.insert("end", *args)
        self._segs = []
        t.config(state="disabled")
        self.update_current_tag()

    def _add(self, text, tags):
        self._segs.append((text, tags))
        self._pos += len(text)

    def _range(self, node):
        r = self.node_ranges.get(id(node))
        return (f"1.0+{r[0]}c", f"1.0+{r[1]}c") if r else None

    def update_current_tag(self, node=None):
        t = self.notation
        t.tag_remove("current", "1.0", "end")
        if node is None and self.line is not None and self.ply:
            node = self.line.nodes[self.ply - 1]
        r = self._range(node) if node is not None else None
        if r:
            t.tag_add("current", *r)
            t.see(r[0])

    # ---- click a move in the notation to jump to that position (Learn step) ----
    def _can_jump(self):
        s = self.session
        if s is None or self.line is None or not self.reveal or self.rendered_chapter is not self.line.chapter:
            return False
        # while learning: jump and keep training; after a line is finished: look around freely
        return self.line_done or (s.mode == "learn" and self.learn_phase)

    def _node_at(self, event):
        t = self.notation
        idx = t.index(f"@{event.x},{event.y}")
        cnt = t.count("1.0", idx, "chars")
        off = cnt if isinstance(cnt, int) else (cnt[0] if cnt else 0)
        i = bisect.bisect_right(self.range_starts, off) - 1
        if i >= 0 and off < self.range_ends[i]:
            return self.range_nodes[i]
        return None

    def on_notation_click(self, event):
        if self._can_jump():
            node = self._node_at(event)
            if node is not None:
                self.jump_to_node(node)
        return "break"                             # no text selection in the notation

    def on_notation_motion(self, event):
        cursor = "hand2" if self._can_jump() and self._node_at(event) is not None else "arrow"
        if self.notation.cget("cursor") != cursor:
            self.notation.config(cursor=cursor)

    def _refresh_path_tags(self):
        t = self.notation
        t.tag_remove("path", "1.0", "end")
        t.tag_remove("sidepath", "1.0", "end")
        for n in self.line.nodes[:self.ply]:
            r = self._range(n)
            if r:
                t.tag_add("path" if n.is_main else "sidepath", *r)

    def jump_to_node(self, node):
        """Move the board to `node`. On the current line, training continues from there;
        on another branch the position is only previewed."""
        line = self.line
        self.gen += 1                              # cancel a pending opponent move
        self.awaiting = False
        self.selected = None
        self.hl, self.arrows = {}, []
        self.shapes = node.shapes or []
        self.last_move = node.move
        k = next((i + 1 for i, n in enumerate(line.nodes) if n is node), None)
        if self.line_done:                         # finished line: browse only
            path = []
            n = node
            while n.parent is not None:
                path.append(n)
                n = n.parent
            self.board = line.chapter.new_board()
            for n in reversed(path):
                self.board.push(n.move)
            self.update_current_tag(node)
            self.draw_board()
        elif k is not None:
            self.preview = False
            self.board = line.chapter.new_board()
            for n in line.nodes[:k]:
                self.board.push(n.move)
            self.ply = k
            self.played_ids = {id(n) for n in line.nodes[:k]}
            self._refresh_path_tags()
            self.update_current_tag()
            self.draw_board()
            self.advance()
        else:
            path = []
            n = node
            while n.parent is not None:
                path.append(n)
                n = n.parent
            self.board = line.chapter.new_board()
            for n in reversed(path):
                self.board.push(n.move)
            self.preview = True
            self.update_current_tag(node)
            self.draw_board()
            self.set_banner(f"Viewing the sideline after {move_label(node)}. "
                            "Click a move from your line to continue training.", "side")

    def _emit_move(self, node, need_num, extra, with_comment=True):
        base = ("main",) if node.is_main else ("side",)
        ctag = "comment" if node.is_main else "sidecomment"
        if with_comment and node.pre:
            self._add(node.pre + " ", base + extra + (ctag,))
            need_num = True
        if node.turn == chess.WHITE:
            num = f"{node.fullmove}."
        else:
            num = f"{node.fullmove}..." if need_num else ""
        tags = base + extra
        if id(node) in self.played_ids:
            tags += ("path",) if node.is_main else ("sidepath",)
        start = self._pos
        self._add(num + node.san + node.suffix, tags)
        self.node_ranges[id(node)] = (start, self._pos)
        self.range_starts.append(start)            # emitted in increasing order -> bisectable
        self.range_ends.append(self._pos)
        self.range_nodes.append(node)
        self._add(" ", base + extra)
        if with_comment and node.comment:
            self._add(node.comment + " ", base + extra + (ctag,))

    def _emit_tree(self, parent, depth, need_num, extra):
        segs = self._segs
        node = parent
        while node.children:
            main = node.children[0]
            self._emit_move(main, need_num, extra)
            need_num = bool(main.comment)
            for var in node.children[1:]:
                if depth == 0:
                    if segs and not segs[-1][0].endswith("\n"):
                        self._add("\n", ())
                    vextra = extra + ("varblock",)
                else:
                    vextra = extra
                self._add("(", ("side",) + vextra)
                self._emit_move(var, True, vextra)
                self._emit_tree(var, depth + 1, bool(var.comment), vextra)
                if segs and segs[-1][0].endswith(" "):
                    text, tags = segs[-1]
                    segs[-1] = (text[:-1], tags)
                    self._pos -= 1
                self._add(")", ("side",) + vextra)
                self._add("\n" if depth == 0 else " ", vextra)
                need_num = True
            node = main

    def set_banner(self, text, kind):
        accent, fg = BANNER[kind]
        self.banner_bar.config(bg=accent)
        self.banner.config(text=text, fg=fg)

    # ------------------------------------------------------------------ board
    @property
    def flipped(self):
        return self.user_color == chess.BLACK

    def square_to_xy(self, sq):
        f, r = chess.square_file(sq), chess.square_rank(sq)
        col, row = (7 - f, r) if self.flipped else (f, 7 - r)
        return col * SQ, row * SQ

    def xy_to_square(self, x, y):
        if not (0 <= x < BOARD_PX and 0 <= y < BOARD_PX):
            return None
        col, row = int(x // SQ), int(y // SQ)
        f, r = (7 - col, row) if self.flipped else (col, 7 - row)
        return chess.square(f, r)

    def flash(self, squares, ms=600):
        self.hl.update(squares)
        self.draw_board()
        gen = self.gen

        def clear():
            if gen != self.gen:
                return
            for sq, col in squares.items():
                if self.hl.get(sq) == col:
                    del self.hl[sq]
            self.draw_board()
        self.root.after(ms, clear)

    def draw_board(self):
        c = self.canvas
        c.delete("all")
        last = {self.last_move.from_square, self.last_move.to_square} if self.last_move else set()
        targets = set()
        if self.selected is not None:
            targets = {m.to_square for m in self.board.legal_moves if m.from_square == self.selected}

        for sq in chess.SQUARES:
            x, y = self.square_to_xy(sq)
            light = (chess.square_file(sq) + chess.square_rank(sq)) % 2 == 1
            color = LIGHT if light else DARK
            if sq in last:
                color = LAST_LIGHT if light else LAST_DARK
            if sq == self.selected:
                color = SEL_COLOR
            if sq in self.hl:
                color = self.hl[sq]
            c.create_rectangle(x, y, x + SQ, y + SQ, fill=color, outline="")

        for kind, col, a, b in self.shapes:
            if kind == "square":
                x, y = self.square_to_xy(a)
                c.create_rectangle(x + 3, y + 3, x + SQ - 3, y + SQ - 3,
                                   outline=SHAPE_COLORS.get(col, LIME), width=4)

        for i in range(8):
            file_char = "abcdefgh"[7 - i if self.flipped else i]
            rank_char = str(i + 1 if self.flipped else 8 - i)
            c.create_text(i * SQ + SQ - 4, BOARD_PX - 2, text=file_char, anchor="se",
                          font=F["coord"], fill=DARK if i % 2 == 0 else LIGHT)
            c.create_text(4, i * SQ + 2, text=rank_char, anchor="nw",
                          font=F["coord"], fill=DARK if i % 2 == 0 else LIGHT)

        for sq in targets:
            x, y = self.square_to_xy(sq)
            cx, cy = x + SQ / 2, y + SQ / 2
            if self.board.piece_at(sq) is None:
                r = SQ * 0.11
                c.create_oval(cx - r, cy - r, cx + r, cy + r, fill=COBALT, outline="")
            else:
                c.create_rectangle(x + 2, y + 2, x + SQ - 2, y + SQ - 2, outline=COBALT, width=3)

        for sq, piece in self.board.piece_map().items():
            if self.dragging and sq == self.drag_from:
                continue
            x, y = self.square_to_xy(sq)
            self._draw_piece(x + SQ / 2, y + SQ / 2, piece)

        for kind, col, a, b in self.shapes:
            if kind == "arrow":
                self._draw_arrow(a, b, SHAPE_COLORS.get(col, LIME), width=0.11)
        for fr, to, col in self.arrows:
            self._draw_arrow(fr, to, col)

    def _draw_arrow(self, fr, to, color, width=0.13):
        x1, y1 = self.square_to_xy(fr)
        x2, y2 = self.square_to_xy(to)
        x1, y1, x2, y2 = x1 + SQ / 2, y1 + SQ / 2, x2 + SQ / 2, y2 + SQ / 2
        self.canvas.create_line(x1, y1, x2, y2, width=SQ * width, fill=color, capstyle="butt",
                                arrow="last", arrowshape=(SQ * 0.34, SQ * 0.34, SQ * 0.16))

    def _draw_piece(self, cx, cy, piece, tag=None):
        """cburnett (lichess) piece images; Unicode glyphs if the images can't load."""
        tags = (tag,) if tag else ()
        img = self.piece_images.get(piece.symbol())
        if img is not None:
            self.canvas.create_image(cx, cy, image=img, tags=tags)
            return
        glyph = GLYPHS[piece.symbol().lower()]
        font = ("Segoe UI Symbol", int(SQ * 0.62))
        if piece.color == chess.WHITE:
            for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                self.canvas.create_text(cx + dx * 1.5, cy + dy * 1.5, text=glyph, font=font,
                                        fill=BG, tags=tags)
            self.canvas.create_text(cx, cy, text=glyph, font=font, fill="#ffffff", tags=tags)
        else:
            self.canvas.create_text(cx, cy, text=glyph, font=font, fill=BG, tags=tags)

    # ------------------------------------------------- mouse (click and drag)
    def on_press(self, event):
        if not self.awaiting:
            return
        sq = self.xy_to_square(event.x, event.y)
        if sq is None:
            return
        piece = self.board.piece_at(sq)
        own = piece is not None and piece.color == self.board.turn
        if self.selected is not None and not own:
            self.try_user_move(self.selected, sq)
            return
        if not own:
            return
        self.press_was_selected = (self.selected == sq)
        self.selected = sq
        self.drag_from = sq
        self.dragging = True
        self.draw_board()
        self._draw_piece(event.x, event.y, piece, tag="drag")
        self._drag_pos = (event.x, event.y)

    def on_motion(self, event):
        if not self.dragging:
            return
        px, py = self._drag_pos
        self.canvas.move("drag", event.x - px, event.y - py)
        self._drag_pos = (event.x, event.y)

    def on_release(self, event):
        if not self.dragging:
            return
        from_sq = self.drag_from
        self.dragging = False
        self.drag_from = None
        target = self.xy_to_square(event.x, event.y)
        if target is not None and target != from_sq:
            self.try_user_move(from_sq, target)
        elif self.press_was_selected:
            self.selected = None
        self.draw_board()


def main():
    root = tk.Tk()
    TrainerApp(root)
    root.mainloop()


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()   # required for parallel parsing inside a packaged .exe
    main()
