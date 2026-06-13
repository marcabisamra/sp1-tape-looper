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
- 🎙️ **Hold-to-record** — hold a track button to lay down a loop; the first
  recording sets the loop length, later ones overdub in time with it.
- 🔇 **Tap to mute / unmute**, **double-tap to erase** a track.
- ▶️ **Full 48 kHz playback** streamed straight off the internal flash.
- 📼 **Tape-style tempo** — the FWD/RWD rocker changes playback speed *and* pitch
  together, one BPM per click.
- 💾 **4 song slots**, each remembering its own tracks and tempo; loops persist
  across power-off *and* across re-flashing the firmware.
- 🎧 **Speaker and headphone output**, both clean.
- 🔋 **Real power behaviour** — charge/standby on plug-in, hold to switch on/off,
  battery-friendly sleep.
- 🛟 **Self-correcting flash storage** (hardware CRC-checked with retry) plus a
  watchdog and a recovery key-combo, so the device can always be re-flashed.

---

## 1. What's in this folder

```
sp-1 looper/
├── README.md          ← you are here
├── sp1_looper.bin     ← the firmware to flash onto the SP-1
└── firmware/          ← the full source code (for reading / rebuilding)
    ├── src/
    │   ├── main.c         the whole looper: audio engine, controls, power, USB
    │   ├── sp1_emmc.c     the flash-memory driver (stores/loads the loops)
    │   └── sp1_emmc.h
    ├── app.overlay       hardware pin map (ADC channels for buttons/faders)
    ├── prj.conf          Zephyr build configuration
    ├── CMakeLists.txt
    └── Kconfig
```

If you just want to **use** it, you only need `sp1_looper.bin` (Section 2–3).
If you want to **read or change** how it works, start with `firmware/src/main.c`
— it opens with a full architecture overview (Section 5 summarizes it).

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
| **Hold** (and keep holding) | **Records** into that track. The very first recording you make sets the loop length; release to stop. While other tracks play, a new recording overdubs in time with them. |
| **Quick tap** | **Mutes / unmutes** that track (its content is kept — tap again to bring it back). |
| **Double-tap** | **Deletes** that track. |

Only one track records at a time. Starting a new recording on a track replaces
whatever was there.

### Playback
- **PLAY button — tap:** play / stop (with a tape-style speed glide).
- **PLAY button — hold (~½ s):** jump to the **start** of the loop and play.

### Mixing & tempo
- **The four faders** set the **volume of each track** (fader 1 = track 1, etc.).
- **VOL +/− buttons** set the **overall (master) volume.**
- **FWD / RWD buttons** change the **tempo / playback speed** — 1 BPM per press,
  hold to sweep faster. (It's a tape-style speed change: faster = higher pitch.)

### Songs
- There are **4 song slots.** The **four side LEDs** show which song you're on
  (LED 1 = song 1 … LED 4 = song 4).
- **Tap the FUNCTION button** to move to the next song. Each song remembers its
  own tracks and tempo.

### Headphones
- Plug headphones into the **headphone jack** (the one nearest the headphone
  symbol — **not** the second/sync jack). The speaker stays on as well.

### If it ever locks up
- **Hold Track 1 + Track 4 together for ~1.2 s** to drop straight back into
  firmware-loading mode, so you can always re-flash.

---

## 4. Audio quality, honestly

- **Playback is full 48 kHz.** When you stack loops and play them back, they
  play at full fidelity.
- **Recording is mono and lo-fi-by-design.** The bottleneck is how fast the
  SP-1's flash can be *written* while everything else is running, so the
  recorder reduces the sample rate to stay reliable. It's plenty for sketching
  ideas, layering parts, looping a podcast or a riff — think 4-track-cassette
  character, not studio multitrack.
- The flash occasionally pauses for its own internal housekeeping; the firmware
  buffers ahead to hide this, so on a busy 4-track jam you may very rarely hear
  a tiny hiccup. It is not damaging anything and the loops on disk are intact.

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
  plus the live USB input, and (when recording) decimates the live input into
  the track being recorded. A soft limiter keeps stacked tracks from clipping.
- **streamer** — the only thing that touches the flash. It writes the
  in-progress recording out to flash and reads the playing tracks back into
  memory buffers, always staying ahead of the playhead.
- **main loop** — reads the buttons and faders, drives the LEDs, handles power,
  and prints a one-line status to the USB-serial console.

**Storage.** Loops live on the 4 GB flash, one region per track, laid out so
writes line up with the flash's internal pages (much faster). The flash is
driven through the nRF's hardware SPI engine at 16 MHz with a CRC check on every
block — if a transfer is ever corrupted it's detected and retried automatically.

**The status line.** If you open the SP-1's USB-serial port you'll see a line
like:

```
LOOPER 48000Hz song=1 PLAY hp=1 usb=1 chg=1 batt=2230 bpm=80 vol=48 trk[PLY PLY --- ---] rec=-1 ovr=0 rerr=0 werr=0
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
