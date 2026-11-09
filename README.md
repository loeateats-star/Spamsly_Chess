# Spamsly

A spaced-repetition chess opening trainer. Load your repertoire as PGN files (ChessBase or Chessable exports, 1,000+ games), learn each line, drill it, and review moves on a schedule that brings back the ones you miss sooner.

## Download (Windows)

**[Download Spamsly.exe](../../releases/latest/download/Spamsly.exe)**

Double-click the file to run it; no install needed. Windows SmartScreen may warn about an unknown publisher the first time: click "More info", then "Run anyway".

All builds are on the [Releases page](../../releases).

## Run from source

```
pip install -r requirements.txt
python spamsly.py
```

## Features

- Courses: keep several PGN files, rename them, and track progress per course
- Learn mode: see the line, then play it from memory 3 times in a row
- Review mode: spaced repetition (4h, 1d, 3d, 1w, 2w, 1m, 3m, 6m), with shorter intervals for moves you get wrong
- Sidelines are kept and highlighted in yellow
- ChessBase comments, arrows and pasted text are understood
- Click any move in the notation to jump to it

Progress is saved next to each PGN as `<file>.pgn.progress.json`.

## Build the exe yourself

```
pip install pyinstaller
pyinstaller --noconfirm --onefile --windowed --name Spamsly --icon assets/app.ico spamsly.py
```

The exe lands in `dist/`. Pushing to `main` on GitHub does this automatically and publishes a new release (see `.github/workflows/release.yml`).
