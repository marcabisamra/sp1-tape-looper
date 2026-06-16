# SP-1 Tape Looper

**A four-track, tape-machine-style looper for the Teenage Engineering SP-1.**

Custom firmware that turns the SP-1 stem player into a hands-on loop sketchpad.
You feed audio in over USB-C (the SP-1 shows up on your computer as a USB sound
card / speaker), record loops by **holding** the four track buttons, and they
play back layered together out of the speaker or headphones. Nudge the rocker
and the whole mix speeds up or slows down like tape. Loops are saved to the
SP-1's internal flash, so they survive turning the device off — and even
re-flashing the firmware.

### Features
- 🎛️ **4 independent loop tracks**, each with its own fader for level.
- 🎙️ **Hold-to-record with auto-start** — hold a track button and recording
  begins on the *first sound it hears* (no clipped attacks). The first recording
  sets the base loop length; later ones overdub in time with it.
- 🔁 **Different-length loops** — keep *holding* an overdub past the end of the
  loop and it adds another bar, and another, in whole multiples of the base — so a
  2-bar melody can sit over a 1-bar drum loop, all locked in time.
- 🔇 **Tap to mute / unmute**, **double-tap to erase** a track.
- ▶️ **Streamed straight off the internal flash** — comes in **three builds**: a
  **24 kHz** default that handles a full multi-track jam, plus two **48 kHz**
  options for best fidelity. See *Which file to flash* below.
- 📼 **Tape-style tempo** — the FWD/RWD rocker changes playback speed *and* pitch
  together, one BPM per click.
- 🥁 **Tempo detection** — the first loop's rhythm is analysed to estimate its
  BPM, which drives the beat LEDs and the MIDI clock grid.
- 🎹 **MIDI clock + Pocket-Operator sync out** of the sync jack — start/stop +
  24-PPQN clock for MIDI gear, and a 2-PPQN pulse for Korg/Volca/PO sync. The MIDI
  bytes are clocked by a hardware timer, so syncing gear never disturbs the audio.
  (On the 24 kHz build; the 48 kHz build ships without MIDI.)
- 💾 **4 song slots**, each remembering its own tracks and tempo; loops persist
  across power-off *and* across re-flashing the firmware.
- 🎧 **Speaker and headphone output**, both clean — speaker auto-mutes when
  headphones are plugged in.
- 🔋 **Real power behaviour** — charge/standby on plug-in, hold to switch on/off,
  battery-friendly sleep.
- 🛟 **Self-correcting flash storage** (hardware CRC-checked with retry) plus a
  watchdog and a recovery key-combo, so the device can always be re-flashed.

---

## 1. What's in this folder

```
sp-1 looper/
├── README.md                     ← you are here
├── sp1_looper.bin                            ← MAIN — 24 kHz, MIDI (flash this one)
├── sp1_looper_48kHz_no_midi.bin              ← 48 kHz, no MIDI, different-length loops
├── sp1_looper_48kHz_no_midi_same_length.bin  ← 48 kHz, no MIDI, all-same-length (smoothest)
└── firmware/                     ← the full source code (for reading / rebuilding)
    ├── src/
    │   ├── main.c         the whole looper: audio engine, controls, power, USB
    │   ├── sp1_emmc.c     the flash-memory driver (stores/loads the loops)
    │   └── sp1_emmc.h
    ├── app.overlay       hardware pin map (ADC channels for buttons/faders)
    ├── prj.conf          Zephyr build configuration
    ├── CMakeLists.txt
    └── Kconfig
```

If you just want to **use** it, you only need one of the two `.bin` files
(Section 2–3). If you want to **read or change** how it works, start with
`firmware/src/main.c` — it opens with a full architecture overview.

### Which file to flash

**Most people want `sp1_looper.bin`** (the 24 kHz build). The full menu:

| Build | Rate | MIDI | Loop lengths | Best for |
|---|---|---|---|---|
| **`sp1_looper.bin`** *(main)* | 24 kHz | ✅ | mix & match | a full multi-track jam |
| `sp1_looper_48kHz_no_midi.bin` | 48 kHz | ❌ | mix & match | best fidelity + different-length loops |
| `sp1_looper_48kHz_no_midi_same_length.bin` | 48 kHz | ❌ | all the same | the smoothest 48 kHz multi-track |

**The rate (24 vs 48 kHz).** The SP-1's flash can only stream so many tracks at
once. **24 kHz halves the data per track, so it comfortably handles several
layered tracks *while* recording another** — that's why it's the default. The
trade is the top octave of "air" (cymbal sparkle); most people won't notice it on
the built-in speaker, and it gives 24 kHz a warm, classic-sampler character. The
**48 kHz** builds sound crisper but run the flash near its limit, so they're
happiest with fewer simultaneous tracks; MIDI is left out of them so all the
bandwidth goes to the audio.

**The two 48 kHz builds** differ only in the looping model:
- **`…_no_midi.bin`** lets tracks be **different lengths** — hold an overdub past
  the loop to extend it (see the controls below).
- **`…_no_midi_same_length.bin`** keeps it simplest: **the first loop sets one
  length and every track shares it.** That's the leanest the engine ever runs, so
  it's the smoothest 48 kHz option for stacking tracks — you just give up the
  different-length trick.

> Each build uses its **own save format**, so switching between any of them
> reformats the loop storage (saved loops are wiped). Pick one for a session.

The `firmware/` source builds the 24 kHz main; the 48 kHz builds are the same
project compiled at the higher rate with MIDI off (the *same-length* build also
uses the project's simpler fixed-length engine).

---

## 2. Flashing it onto the SP-1

The SP-1 is flashed with the **Solderless updater** (the same tool used for any
SP-1 custom firmware) — no soldering or opening the device required:

1. Go to the Solderless SP-1 update tool: <https://solderless.engineering>
2. Connect the SP-1 to your computer with a USB-C cable.
3. Put the SP-1 into firmware-loading mode and select **`sp1_looper.bin`**.
4. Flash, then unplug/replug.

> ⚠️ **A loop you record is safe across re-flashing the *same* build.** But
> flashing a *different* build (including the very first time you install this
> one) reformats the loop storage, so anything previously recorded is wiped.

---

## 3. How to use it (the controls)

### Turning it on and off
- The device boots into a quiet **charging/standby** state — plugging in USB or
  finishing a flash does **not** make it start playing.
- **Hold the FUNCTION button (·· , bottom) for ~0.6 s to turn it ON.**
- **Hold FUNCTION for ~2.5 s to turn it OFF** (the four center LEDs fill up as a
  countdown; let go early to cancel).

### The four track buttons — this is the heart of it
Each track button does three things depending on how you press it:

| Gesture | What it does |
|---|---|
| **Hold** (and keep holding) | **Records** into that track — capture begins on the **first sound** it hears (so a held breath or count-in doesn't get recorded). The very first recording sets the **base loop length**. For overdubs: **let go after one loop** for a same-length layer, or **keep holding** to extend the track to 2, 3… bars (whole multiples of the base) — so tracks can be *different lengths* yet stay locked in time. |
| **Quick tap** | **Mutes / unmutes** that track (its content is kept — tap again to bring it back). |
| **Double-tap** | **Deletes** that track. |

Only one track records at a time. Starting a new recording on a track replaces
whatever was there.

### Playback
- **PLAY button — tap:** play / stop (with a tape-style speed glide).
- **PLAY button — hold (~½ s):** jump to the **start** of the loop and play.

### Mixing & tempo
- **The four faders** set the **volume of each track** (fader 1 = track 1, etc.).
- **VOL +/− buttons** set the **overall (master) volume** — a smooth, gradual
  control that steps all the way down to fully muted. Hold to sweep quickly.
- **FWD / RWD buttons** change the **tempo / playback speed** — 1 BPM per press,
  hold to sweep faster. (It's a tape-style speed change: faster = higher pitch.)

### Songs
- There are **4 song slots.** The **four side LEDs** show which song you're on
  (LED 1 = song 1 … LED 4 = song 4).
- **Tap the FUNCTION button** to move to the next song. Each song remembers its
  own tracks and tempo.

### Headphones
- Plug headphones into the **headphone jack** (the one nearest the headphone
  symbol — **not** the second/sync jack). The **speaker mutes automatically**
  while headphones are plugged in, and comes back when you unplug.

### Sync & MIDI out (the second / sync jack)
- The **sync jack** sends clock to your other gear, locked to the looper's tempo:
  **MIDI clock** (Start / Stop + 24-PPQN) for MIDI instruments, and a **2-PPQN
  pulse** for Korg / Volca / Pocket-Operator–style sync.
- Use the appropriate **3.5 mm TRS adapter** for whatever you're driving (a
  TRS→MIDI-DIN adapter for MIDI, or a sync cable for PO/Volca).
- The MIDI byte timing is generated by a **hardware timer**, so driving external
  gear never glitches the audio. **MIDI is on the 24 kHz `sp1_looper.bin` build
  only** — the 48 kHz build leaves it out for headroom. If a MIDI device reads it
  inverted, it's a one-line firmware flag (`MIDI_INVERT`) to flip.

### If it ever locks up
- **Hold Track 1 + Track 4 together for ~1.2 s** to drop straight back into
  firmware-loading mode, so you can always re-flash.

---

## 4. Audio quality, honestly

- **Tracks are mono, 16-bit**, recorded and played at the build's sample rate —
  **24 kHz** on `sp1_looper.bin`, **48 kHz** on the no-MIDI backup. (Mono, rather
  than the stock player's stereo, is a storage-bandwidth choice.)
- **Why two rates?** Every playing track is a separate stream read off the flash
  in real time, *while* the track you're recording is written back. The flash has
  a hard ceiling on how many of those it can sustain at once. 48 kHz reaches that
  ceiling at just a few simultaneous tracks; **24 kHz halves the data per track,
  so it keeps a whole multi-track jam (several layers + recording) glitch-free.**
  That is the entire reason 24 kHz is the default.
- **What you give up at 24 kHz** is the top octave above ~12 kHz — cymbal "air"
  and sparkle. On the built-in speaker (which rolls off up there anyway) it's hard
  to hear at all; on headphones it reads as a slightly warmer, lo-fi tone — the
  sound classic samplers were built on. The 48 kHz backup keeps the full top end
  for when fidelity matters more than track count.
- The flash occasionally pauses for its own housekeeping; the firmware reads ahead
  to hide it, so even on a busy jam you'd at most rarely hear a tiny hiccup.
  Nothing is damaged and the loops on disk stay intact.

---

## 5. How it works (a short tour for the curious)

The audio path, end to end:

```
USB-C in ──► [USB ring buffer] ──► audio engine ──► I2S bus ──► speaker / headphones
                                       │   ▲
                               record  ▼   │  play
                                  [ flash memory: one region per track ]
```

**Clocking.** The SP-1's on-board 3.072 MHz oscillator drives the audio bus, and
the headphone codec (a Cirrus CS42L42) generates a true 48 kHz frame from it.
The main chip (an nRF52840) and the speaker amp (a TI TAS2505) follow as clock
*slaves*. Running the board exactly the way TE designed it is what makes both the
speaker and the headphones sound clean.

**Threads (in priority order):**
- **audio engine** — runs on every I2S block. It mixes the four playback tracks
  plus the live USB input *for the output only*, and (when recording) writes the
  live input into the one track being recorded. A soft limiter keeps stacked
  tracks from clipping.
- **streamer** — the only thing that touches the flash. It writes the
  in-progress recording out to flash and reads the playing tracks back into
  memory buffers, always staying ahead of the playhead.
- **main loop** — reads the buttons and faders, drives the LEDs, handles power,
  and prints a one-line status to the USB-serial console.

**Storage — tracks are independent, there is no mixdown.** Each track gets its
own fixed region on the flash (block 0 holds a small metadata header; then four
regions per song, four songs). Recording a track writes **only that track's**
audio to **its own** region; the other three are never rewritten — they're just
being *read* for monitoring. Mixing happens live in the audio engine and is
never stored. So an overdub is one region being written while three are read,
all independent — no read-modify-write of a combined file. Each track is mono
`int16` at the build's loop rate (24 kHz default, 48 kHz on the backup). Regions
are laid out so write bursts line up with the flash's
8 KB internal pages, and the flash is driven through the nRF's hardware SPI
engine at 16 MHz with a CRC check + retry on every block, so the bus is both
fast and self-correcting.

This is **not** the stock TE album/stem format — it's a simple purpose-built
layout for live looping. (The 8 KB page-alignment trick was borrowed from TE's
data-structure docs; the rest is its own thing.)

**The status line.** If you open the SP-1's USB-serial port you'll see a line
like:

```
LOOPER 24000Hz song=1 PLAY hp=1 usb=1 chg=1 batt=2230 bpm=80 vol=48 trk[PLY PLY --- ---] rec=-1 ovr=0 rerr=0 werr=0
```

The healthy signs are `ovr=0` (no recording-buffer overflow) and `rerr=0
werr=0` (the flash bus is error-free).

---

## 6. Rebuilding from source

The firmware is a [Zephyr](https://www.zephyrproject.org/) application built on
the "marisko" SP-1 board support. With a Zephyr workspace and the nRF SDK set
up, point a `west build` at the `firmware/` folder, then convert the resulting
ELF to the bootloader-friendly `.bin` (the app is linked to load at `0x20000`).

The single most important rule when modifying it: **the SP-1 has no hardware
reset, so the firmware must always keep the watchdog fed and must always offer a
way back to the bootloader** (here: hold FUNCTION to power off, or the Track 1+4
recovery combo). Don't remove those.

---

## ⚠️ Disclaimer

This is **unofficial, community-made firmware**, not affiliated with or endorsed
by Teenage Engineering. Flashing custom firmware is at your own risk. It has been
tested on my own SP-1 and works well, but no warranty is implied — if in doubt,
make sure you understand the [Solderless](https://solderless.engineering) update
process and the recovery options above before flashing. The Track 1 + Track 4
combo always drops the device back into firmware-loading mode.

## Credits & licence

- Built on the SP-1 hardware reverse-engineering and board support documented in
  Tim Knapen's excellent [**SP-1-dev**](https://github.com/timknapen/SP-1-dev)
  project — the pin map, the codec/clock notes, and the eMMC protocol all came
  from there. Huge thanks.
- Flashing is made possible by the [Solderless](https://solderless.engineering)
  SP-1 updater.
- Runs on the [Zephyr RTOS](https://www.zephyrproject.org/).

Released under the **MIT License** (see `LICENSE`). Do whatever you like with it;
contributions and forks welcome.
