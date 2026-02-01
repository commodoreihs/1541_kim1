# FranKIMstein_kernal

A mashup of the KIM-1 monitor code and Commodore's DOS 2.6 code glued together
and modified to run on a stock Commodore 1541 disk drive, thereby turning the
1541 disk drive into a standalone computer.

The KIM-1 code has been modified so its input and output routines (GETCH, 
and OUTCH, respectively) do serial TTY communication over the native
Commodore disk serial bus. This allows you to use any standard terminal
or terminal emulator connected to the stock IEC serial connectors on the
back of the 1541 as an I/O device.

The KIM-1 monitor code behaves exactly as it does on a real KIM-1 computer in
TTY mode, so you can use the KIM-1 user manual for instructions.

Three new commands have been added to the KIM-1 monitor to support disk
operations:

'L' - Loads a Commodore prg file from disk.
'S' - Saves a Commodore prg file to disk.
'I' - Initializes (formats) a disk using standard, 35-track 1541 disk format.

This code can be assembled using the 64tass assembler and burned to
a 2764 EPROM, then inserted in UB4 to replace the stock Commodore 901229-05
2364 mask ROM. You will need to use a 2764 to 2364 adapter. This code 
fills the 8K from $E000-$FFFF in the 1541's memory map, and includes the
vectors from $FFFA - $FFFF which allow the 6502 to boot.

This code can be run completely standalone in a Commodore 1541 disk drive,
or you can optionally burn a second 2764 EPROM containing the FranKIMstein
BASIC code (separate repo) and run Commodore BASIC on the disk drive from UB3
($C000). The BASIC code relies on the FranKIMstein kernal code. 

