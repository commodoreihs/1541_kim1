; =============================================================================
; FranKIMstein - implementing the KIM-1 monitor to run on a Commodore 
;                1541 disk drive.
; 
; This is a mashup of the original KIM-1 kernal code glued together with the
; original Commodore DOS 2.6 code that ran on the Commodore 1541 disk drive.
;
; It allows the KIM-1 monitor to run natively on a Commodore 1541 disk drive
; with the I/O routines GETCH and OUTCH modified to do serial RS232 over the
; Commodore IEC serial bus, and it implements new KIM-1 monitor commands as 
; follows:
;
; I - Initialize a disk. Really, this is the Commodore Format routine, but I
;                        couldn't use 'F' as a command for format, since 'F'
;                        is a hex character recognized by the KIM-1's parser.
;
; L - Load a file.       This loads a file from a Commodore 1541 formatted 
;                        disk.
;
; S - Save a file.       This saves a file to a Commodore 1541 formatted disk.
;
; I tried to keep as much of the original code intact as possible, with major
; changes noted in comments.
;
; The KIM-1 monitor source code was obtained from Vern Graner's kim-1.com
; site at https://kim-1.com/files/user-manual.txt
; 
; The Commodore DOS 2.6 source code was obtained from Michael Steil's github
; at https://github.com/mist64/dos1541
; =============================================================================

; =============================================================================
; I/O DEFINITIONS - from lccio.src
; =============================================================================
;    .page   'lcc.i/o'
;
;     defs for low cost controller
;
;     written by glenn stark
;     4/1/80
;
;   (c) commodore business machines
;
timer1   =$1805         ;  timer 1 counter
;
;   mos 6522
;   address $1c00

dskcnt   = $1c00        ;  port b
; disk i/o control lines
; bit 0: step in
; bit 1: step out
; bit 2: -motor on
; bit 3: act led
; bit 4: write protect sense
; bit 5: density select 0
; bit 6: density select 1
; bit 7: sync detect
;
data2    = $1c01        ;  port a - gcr data
ddrb2    = $1c02        ;  data direction control
ddra2    = $1c03        ;  data direction control
t1lc2    = $1c04        ;  timer 1 low counter
t1hc2    = $1c05        ;  timer 1 hi countr
t1ll2    = $1c06        ;  timer 1 low latch
t1hl2    = $1c07        ;  timer 1 hi latch
t2ll2    = $1c08        ;  timer two low latch
t2lh2    = $1c09        ;  timer two hi latch
sr2      = $1c0a        ;  shift register
acr2     = $1c0b
pcr2     = $1c0c
ifr2     = $1c0d
ier2     = $1c0e

; VIA1 registers for serial/ATN (from iodefsf.src)
pb       = $1800        ;  serial port
pa1      = $1801        ; unused port
ddrb1    = $1802        ;  serial data dir
ddra1    = $1803        ; unused ddra
t1lc1    = $1804        ;  timer 1 low counter
t1hc1    = $1805        ;  timer 1 hi counter
t1ll1    = $1806        ;  timer 1 low latch
t1hl1    = $1807        ;  timer 1 hi latch
t2lc1    = $1808        ;  timer 2 low counter
t2hc1    = $1809        ;  timer 2 hi counter
sr1      = $180a        ;  shift reg
acr1     = $180b        ;  aux control reg
pcr1     = $180c        ;
ifr1     = $180d        ;
ier1     = $180e        ;

; LED control
led0     = 8            ;  act led
ledprt   = $1c00        ;  on pb of $1c00

; =============================================================================
; ZERO PAGE VARIABLES - from lccvar.src
; CHANGE: Reorganized to avoid conflict with KIM-1 monitor
; =============================================================================

; Job queue and headers
; CHANGE: Moved to start of zero page for KIM-1 compatibility
jobs     = $00          ; 6 job slots
hdrs     = $06          ; 12 bytes - header table (track/sector pairs)

; Drive state - CHANGE: single byte not array (single drive)
drvst    = $12          ; drive status
drvtrk   = $13          ; drive track

; GCR work area
stab     = $14          ; 10 bytes for GCR header

; Pointers
savpnt   = $1e          ; 2 bytes
bufpnt   = $20          ; 2 bytes
hdrpnt   = $22          ; 2 bytes - CHANGE: +1 always 0 for zero page

; Variables
gcrpnt   = $24
gcrerr   = $25          ;  indicates gcr decode error
bytcnt   = $26
bitcnt   = $27
bid      = $28
hbid     = $29
chksum   = $2a
hinib    = $2b
byte     = $2c
drive    = $2d
cdrive   = $2e
jobn     = $2f
tracc    = $30
nxtjob   = $31
nxtrk    = $32
sectr    = $33
work     = $34
job      = $35
ctrack   = $36
dbid     = $37          ;  data block id
acltim   = $38          ;  acel time delay
savsp    = $39          ;  save stack pointer
steps    = $3a          ;  steps to desired track
tmp      = $3b
csect    = $3c
nexts    = $3d
nxtbf    = $3e          ;  pointer at next gcr source buffer
nxtpnt   = $3f          ;  and next gcr byte location in buffer
gcrflg   = $40          ;  buffer in gcr image
ftnum    = $41          ;  current format track
btab     = $42          ; 4 bytes
gtab     = $46          ; 8 bytes
;
as       = $4e          ;  # of steps to acel
af       = $4f          ;  acel. factor
aclstp   = $50          ;  steps to go
rsteps   = $51          ;  # of run steps
nxtst    = $52          ; 2 bytes - next stepper state
minstp   = $54          ;  min reqired to acel
;
lwpt     = $55          ; last write protect state
wpsw     = $56          ; write protect switch
phase    = $57          ; phase offset
;
header   = $58          ; 5 bytes for decoded header
;
dskid    = $5d          ; 2 bytes - disk id

; KIM-1 monitor variables (from v5)
CNTL30   = $5f          ; Baud rate timing low
CNTH30   = $60          ; Baud rate timing high
TIMH     = $61          ; Timer high byte
INL      = $F8          ; Input buffer low
INH      = $F9          ; Input buffer high
POINTL   = $FA          ; Address pointer low
POINTH   = $FB          ; Address pointer high
TMPX     = $FD          ; Saved X register
CHAR     = $FE          ; Character buffer

; Additional VIA1 definitions for serial I/O
VIA1_PB  = $1800        ; VIA1 Port B (serial I/O)
VIA1_PA  = $1801        ; VIA1 Port A
VIA1_DDRB = $1802       ; VIA1 Data Direction B
VIA1_IFR = $180D        ; VIA1 Interrupt Flag Register

; =============================================================================
; CONSTANTS - from lccvar.src
; =============================================================================
; CHANGE: ovrbuf moved from $0100 to $0200 to prevent stack corruption
ovrbuf   = $0200        ;  CHANGED: was $0100 (stack area)
numjob   = 6            ;  number of jobs
jmpc     = $50          ;  jump command
bumpc    = $40          ;  bump command
execd    = $60          ;  execute command
fmtcmd   = $f0          ;  ADDED: format command code
jread    = $80          ;  read command (from equatesf.src)
jwrite   = $90          ;  write command (from equatesf.src)
jseek    = $B0          ;  seek command (from equatesf.src)
bufs     = $0300        ;  start of buffers
buff0    = bufs
buff1    = bufs+$100
buff2    = bufs+$200
tolong   = $2           ;  format errors
tomany   = $3
tobig    = $4
tosmal   = $5
notfnd   = $6
skip2    = $2c          ;  bit abs
toprd    = 69           ;  top of read overflo buffer on a read
topwrt   = 69           ;  top of write overflo buffer on a write
numsyn   = 5            ;  gcr byte count for size of sync area
gap1     = 11           ;  gap after header to clear erase in gcr bytes
gap2     = 4            ;  gap after data block min size
rdmax    = 6            ;  sector distance wait
wrtmin   = 9
wrtmax   = 12
tim      = 58           ;  irq rate for 15 ms

; =============================================================================
; FORMAT VARIABLES - from lccfmt1.src
; =============================================================================
fmtvar   = $620         ;  put format vars in jump buffer
cnt      = fmtvar
num      = fmtvar+1
trys     = fmtvar+3
tral     = fmtvar+4
dtrck    = fmtvar+6
remdr    = fmtvar+7
sect     = fmtvar+8
dskname  = $630         ; 16 bytes for disk name
savename = $640         ; 16 bytes for save/load filename
sal      = $650         ; start address low
sah      = $651         ; start address high
eal      = $652         ; end address low
eah      = $653         ; end address high
ftrack   = $654         ; first track of file (for dir entry)
fsector  = $655         ; first sector of file
curtk    = $656         ; current track being written
cursec   = $657         ; current sector being written
sbytesl  = $658         ; save bytes remaining low
sbytesh  = $659         ; save bytes remaining high
blkcnt   = $65a         ; block count for directory
secptr   = $65b         ; pointer within sector (0-255)

; =============================================================================
; DOS RAM VARIABLES - based on ramvarsf.src layout
; Starting at $62 to avoid conflict with KIM serial ($5F-$61)
; =============================================================================
; Note: Original DOS uses *=*+ allocation from zp2. We assign fixed addresses
; that don't conflict with controller ($24-$5E) or KIM serial ($5F-$61).

secinc   = $62          ; sector inc for seq files (1 byte)
bmpnt    = $63          ; 2 bytes - bit map pointer
temp     = $65          ; 6 bytes - temp work space
; t0-t4 are aliases into temp, matching original DOS
t0       = temp
t1       = temp+1
t2       = temp+2
t3       = temp+3
t4       = temp+4
ip       = $6b          ; 2 bytes - indirect ptr variable
drvnum   = $6d          ; 1 byte - current drive #
track    = $6e          ; 1 byte - current track
sector   = $6f          ; 1 byte - current sector
lindx    = $70          ; 1 byte - logical index
sa       = $71          ; 1 byte - secondary address
data     = $72          ; 1 byte - temp data byte
jobnum   = $73          ; 1 byte - current job number
wbam     = $74          ; 1 byte - don't-write-bam flag
lstsec   = $75          ; 1 byte - last sector count
cmd      = $76          ; 1 byte - temp job command
dirbuf   = $77          ; 2 bytes - directory buffer pointer
index    = $79          ; 1 byte - current index in buffer
filtrk   = $7a          ; 1 byte - file first track
filsec   = $7b          ; 1 byte - file first sector
nbkl     = $7c          ; 1 byte - number of blocks low
nbkh     = $7d          ; 1 byte - number of blocks high
type     = $7e          ; 1 byte - file type
delind   = $7f          ; 1 byte - deleted entry index

; BAM working buffer - MUST NOT overlap with other variables
; Variables at $620-$65F, so use $0700
bam_work = $0700        ; 256 bytes for working copy of BAM

; =============================================================================
; ROM START
; =============================================================================
    * = $E000

; =============================================================================
; KIM-1 MONITOR RESET VECTOR
; =============================================================================
RESET:
    ; Disable interrupts during initialization
    sei                   ; 78
 
    ; Initialize stack pointer
    ldx  #$FF             ; A2 FF
    txs                   ; 9A
    
    ; Initialize VIA1 for FranKIMstein serial I/O (bit-banged RS-232)
    lda  #$08             ; A9 08
    sta  VIA1_PA          ; 8D 01 18
    lda  #$0A             ; A9 0A - bits 1,3 as outputs
    sta  VIA1_DDRB        ; 8D 02 18
    lda  VIA1_DDRB        ; AD 02 18
    ora  #$10             ; 09 10 - bit 4 as output
    sta  VIA1_DDRB        ; 8D 02 18
    lda  VIA1_PB          ; AD 00 18
    and  #$EF             ; 29 EF - clear bit 4
    sta  VIA1_PB          ; 8D 00 18
    
    ; Commodore DOS 2.6 Sync routine uses timer1 (T1) for timeout detection
    lda  #$00
    sta  acr1             ; One-shot timer mode (bit 6 = 0)
    sta  t1ll1            ; Timer 1 low latch = 0
    lda  #$FF
    sta  t1hl1            ; Timer 1 high latch = $FF (for max timeout range)
    
    ; VIA2 initialization (disk controller)
    lda  #$00
    sta  dskcnt           ; motor off, LED off
    sta  ddra2            ; Port A input (read mode)
    lda  #$6F             ; bits 4,7 input (sync, write protect)
    sta  ddrb2
    lda  #$EE             ; CA1 neg, CA2 high, CB1 neg, CB2 high (read mode)
    sta  pcr2
    
    ; Initialize controller variables same as Commodore DOS 2.6
    lda  #$FF
    sta  cdrive           ; no active drive
    lda  #0
    sta  drvst            ; drive inactive
    sta  drvtrk           ; track unknown
    sta  drive
    sta  phase
    sta  lwpt
    sta  wpsw
    
    ; Clear job queue
    ldx  #numjob-1
    lda  #0
clrjob:
    sta  jobs,x
    dex
    bpl  clrjob
    
    ; Init stepper state
    lda  #<inact
    sta  nxtst
    lda  #>inact
    sta  nxtst+1
    lda  #200
    sta  minstp
    lda  #4
    sta  as
    sta  af
    
    ; Init block IDs
    lda  #$08
    sta  hbid
    lda  #$07
    sta  dbid
    
    ; Timer setup for ~8ms IRQ (VIA2)
    lda  #$41              ; continuous, latch
    sta  acr2
    lda  #0
    sta  t1ll2
    lda  #tim
    sta  t1hl2
    sta  t1hc2
    
    ; Enable timer IRQ
    lda  #$7F
    sta  ier2              ; disable all first
    lda  #$C0
    sta  ier2              ; enable timer
    
    cli                   ; enable interrupts
    jmp  START            ; go to KIM monitor

; =============================================================================
; START - KIM-1 Startup (KIM-1 line 145)
; =============================================================================
START:
    jsr  DETCPS           ; detect baud rate (WAITS FOR KEYPRESS!)
    ldx  #$0A             ; print banner
    jsr  PRTST
    jmp  SHOW1

; =============================================================================
; CLEAR - Clear input buffer (KIM-1 line 156)
; =============================================================================
CLEAR:
    lda  #$00
    sta  INL
    sta  INH

; =============================================================================
; READ - Main input loop (KIM-1 line 163)
; =============================================================================
READ:
    jsr  GETCH
    pha
    jsr  OUTCH
    pla
    jsr  PACK
    jmp  SCAN

; =============================================================================
; SCAN - Analyze character (KIM-1 line 170)
; =============================================================================
SCAN:
    cmp  #$20             ; space = open address
    beq  SPACE
    cmp  #$7F             ; DEL = restart
    beq  START
    cmp  #$0D             ; CR = next address
    beq  RTRN
    cmp  #$0A             ; LF = previous address
    beq  FEED
    cmp  #'.'             ; period = modify
    beq  MODIFY
    cmp  #'G'             ; G = go execute
    beq  GOEXEC
    cmp  #'I'             ; I = format (Init disk)
    beq  GO_FMT_CMD
    cmp  #'S'             ; S = save to disk
    beq  GO_SAVE_CMD
    cmp  #'L'             ; L = load from disk
    beq  GO_LOAD_CMD
    jmp  READ

GO_FMT_CMD:
    jmp  CMD_FORMAT

GO_SAVE_CMD:
    jmp  CMD_SAVE

GO_LOAD_CMD:
    jmp  CMD_LOAD

; =============================================================================
; SPACE - Open new cell (KIM-1 line 200)
; =============================================================================
SPACE:
    jsr  OPEN

; SHOW - display address and contents
SHOW:
    jsr  CRLF

SHOW1:
    jsr  PRTPNT
    jsr  OUTSP
    ldy  #$00
    lda  (POINTL),Y
    jsr  PRTBYT
    jsr  OUTSP
    jmp  CLEAR

; =============================================================================
; RTRN - Increment to next address (KIM-1 line 218)
; =============================================================================
RTRN:
    jsr  INCPT
    jmp  SHOW

; =============================================================================
; FEED - Decrement to previous address (KIM-1 line 223)
; =============================================================================
FEED:
    jsr  DECPT
    jmp  SHOW

; =============================================================================
; MODIFY - Modify cell (KIM-1 line 228)
; =============================================================================
MODIFY:
    ldy  #$00
    lda  INL
    sta  (POINTL),Y
    jmp  RTRN

; =============================================================================
; GOEXEC - Execute program (KIM-1 line 237)
; =============================================================================
GOEXEC:
    jsr  OPEN
    jmp  (POINTL)

; =============================================================================
; OPEN - Move INL/INH to POINTL/POINTH (KIM-1 line 243)
; =============================================================================
OPEN:
    lda  INH
    sta  POINTH
    lda  INL
    sta  POINTL
    rts

; =============================================================================
; INCPT - Increment pointer (KIM-1 line 251)
; =============================================================================
INCPT:
    inc  POINTL
    bne  INCPT1
    inc  POINTH
INCPT1:
    rts

; =============================================================================
; DECPT - Decrement pointer (KIM-1 line 259)
; =============================================================================
DECPT:
    lda  POINTL
    bne  DECPT1
    dec  POINTH
DECPT1:
    dec  POINTL
    rts

; =============================================================================
; DETCPS - Detect baud rate (KIM-1 line 753)
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
; Restructured to 13-cycle loop to match DELAY's 13-cycle loop
; =============================================================================
DETCPS:
    lda  #$FF
    sta  CNTH30
DETCPS1:
    lda  VIA1_PB
    and  #$04
    bne  DETCPS1
DETCPS2:
    lda  VIA1_PB
    and  #$04
    beq  DETCPS2
    ldx  #$FC
DETCPS3:
    lda  VIA1_PB
    and  #$04
    beq  DETCPS4
    inx
    bne  DETCPS3
    inc  CNTH30
    jmp  DETCPS3
DETCPS4:
    stx  CNTL30
    ldx  #$08
    jsr  GET5
    rts

; =============================================================================
; GET5 - Read 8 data bits (KIM-1 GET5, line 860)
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
; Use ROR with carry to shift bit into position 7
; Invert polarity because 74LS14 inverts the input
; VIA HIGH = RS-232 LOW = 0 bit
; VIA LOW = RS-232 HIGH = 1 bit
; =============================================================================
GET5:
    jsr  DEHALF
GET5A:
    lda  VIA1_PB
    and  #$04
    sec
    beq  GET5B
    clc
GET5B:
    ror  CHAR
    jsr  DELAY
    dex
    bne  GET5A
    jsr  DEHALF
    rts

; =============================================================================
; GETCH - Get character from serial (KIM-1 GETCH, line 842)
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
; =============================================================================
GETCH:
    stx  TMPX
GETCH1:
    lda  VIA1_PB
    and  #$04
    bne  GETCH1
GETCH2:
    lda  VIA1_PB
    and  #$04
    beq  GETCH1+2 
    ldx  #$08
    jsr  DELAY
    jsr  GET5
    ldx  TMPX
    lda  CHAR
    rol
    lsr
    rts

; =============================================================================
; OUTCH - Output character (KIM-1 OUTCH, line 895)
; Use VIA Port B bit 1 instead of KIM-1 6530 Port B bit 0
; =============================================================================
OUTSP:
    lda  #$20
OUTCH:
    php                   ; save I flag
    sei                   ; protect timing
    sta  CHAR
    stx  TMPX
    jsr  DELAY
    ; Send start bit
    ; Idle is LOW, so start bit must be HIGH (opposite of idle)
    lda  VIA1_PB
    ora  #$02
    sta  VIA1_PB
    jsr  DELAY
    ; Send 8 data bits
    ; Data polarity: VIA must output OPPOSITE of desired RS-232 level
    ; because 7406 inverts. So: 1 bit is VIA LOW, 0 bit is VIA HIGH
    ldx  #$08
OUTCH1:
    lda  VIA1_PB          ; Read Port B
    ora  #$02             ; Default bit 1 HIGH (becomes LOW after 7406 = 0 bit)
    lsr  CHAR             ; Shift byte, bit 0 into carry
    bcc  OUTCH2           ; If carry clear (0 bit), keep HIGH
    and  #$FD             ; If carry set (1 bit), clear to LOW (becomes HIGH after 7406)
OUTCH2:
    sta  VIA1_PB          ; Output the bit
    jsr  DELAY
    dex
    bne  OUTCH1
    ; Send stop bit
    ; Stop bit must return to idle (LOW)
    lda  VIA1_PB
    and  #$FD
    sta  VIA1_PB
    jsr  DELAY
    ldx  TMPX
    plp                   ; restore I flag
    rts

; =============================================================================
; DELAY - Delay one bit time (KIM-1 DELAY, line 921)
; Loop: sec(2) + sbc(2) + bcs(3) + ldy(3) + bpl(3) = 13 cycles
; Matches DETCPS's 13-cycle measurement loop
; =============================================================================
DELAY:
    lda  CNTH30
    sta  TIMH
    lda  CNTL30
DELAY1:
    sec
DELAY2:
    sbc  #$01
    bcs  DELAY3
    dec  TIMH
DELAY3:
    ldy  TIMH
    bpl  DELAY1
    rts

; =============================================================================
; DEHALF - Delay half bit time (KIM-1 DEHALF, line 935) ===
; Uses DELAY's loop (DE2/DE4) with halved count
; =============================================================================
DEHALF:
    lda  CNTH30
    sta  TIMH
    lda  CNTL30
    lsr
    lsr  TIMH
    bcc  DELAY1
    ora  #$80
    bcs  DELAY2

; =============================================================================
; CRLF - Print CR and LF (KIM-1 CRLF, line 817)
; =============================================================================
CRLF:
    ldx  #$07

; =============================================================================
; PRTST - print string from TOP
; =============================================================================
PRTST:
    lda  TOP,X
    jsr  OUTCH
    dex
    bpl  PRTST
    rts

; =============================================================================
; PRTPNT - Print address (KIM-1 PRTPNT, line 800)
; =============================================================================
PRTPNT:
    lda  POINTH
    jsr  PRTBYT
    lda  POINTL

; PRTBYT - print byte as hex
PRTBYT:
    pha
    lsr
    lsr
    lsr
    lsr
    jsr  HEXTA
    pla
    and  #$0F

; HEXTA - print hex digit
HEXTA:
    and  #$0F
    cmp  #$0A
    clc
    bmi  HEXTA1
    adc  #$07
HEXTA1:
    adc  #$30
    jmp  OUTCH

; =============================================================================
; PACK - Pack hex ASCII into binary (KIM-1 PACK, line 828)
; =============================================================================
PACK:
    cmp  #'0'
    bmi  PACK3
    cmp  #'G'
    bpl  PACK3
    cmp  #'A'
    bmi  PACK1
    clc
    adc  #$09
PACK1:
    rol
    rol
    rol
    rol
    ldy  #$04
PACK2:
    rol
    rol  INL
    rol  INH
    dey
    bne  PACK2
    lda  #$00
PACK3:
    rts

; =============================================================================
; TOP - Banner text (KIM-1 TOP, line 1111)
; =============================================================================
TOP:
    .byte $00, $00, $00, $00, $00, $00, $0A, $0D
    .text "MIK"

; =============================================================================
; FORMAT COMMAND - I key from monitor
; =============================================================================
CMD_FORMAT:
    ; Prompt for disk name
    jsr  CRLF
    lda  #'N'
    jsr  OUTCH
    lda  #'A'
    jsr  OUTCH
    lda  #'M'
    jsr  OUTCH
    lda  #'E'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Read disk name (up to 16 chars)
    ldx  #0
fmt_name_loop:
    jsr  GETCH            ; get character
    cmp  #$0D             ; RETURN?
    beq  fmt_name_done
    cpx  #16              ; max 16 chars
    bcs  fmt_name_loop    ; ignore if too many
    sta  dskname,x
    jsr  OUTCH            ; echo
    inx
    bne  fmt_name_loop    ; always branches

fmt_name_done:
    ; Pad rest with $A0 (shifted space)
    lda  #$A0
fmt_name_pad:
    cpx  #16
    bcs  fmt_id_prompt
    sta  dskname,x
    inx
    bne  fmt_name_pad

fmt_id_prompt:
    ; Prompt for disk ID
    jsr  CRLF
    lda  #'I'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Read 2 char ID
    jsr  GETCH
    sta  dskid
    jsr  OUTCH
    jsr  GETCH
    sta  dskid+1
    jsr  OUTCH

    jsr  CRLF
    lda  #'F'
    jsr  OUTCH
    lda  #'M'
    jsr  OUTCH
    lda  #'T'
    jsr  OUTCH
    jsr  CRLF
    
    ; Init format variables
    lda  #$FF
    sta  ftnum             ; trigger bump on first formt call
    lda  #10
    sta  cnt               ; retry count
    
    ; Post format job to job queue slot 0
    lda  #fmtcmd           ; format command ($F0) - MSB set = job waiting
    sta  jobs
    
    ; Set target track in header
    lda  #1
    sta  hdrs              ; track 1
    lda  #0
    sta  hdrs+1            ; sector 0 (unused)

    ; Wait for job to complete (MSB clear = done)
fmt_wait:
    lda  jobs
    bmi  fmt_wait          ; still running
    
    ; Job done - check result
    cmp  #2                ; result < 2 = success
    bcs  fmt_error
    
    ; Success
    lda  #'O'
    jsr  OUTCH
    lda  #'K'
    jsr  OUTCH
    jmp  fmt_done
    
fmt_error:
    lda  #'E'
    jsr  OUTCH
    lda  #'R'
    jsr  OUTCH
    lda  #'R'
    jsr  OUTCH
    
fmt_done:
    jsr  CRLF
    jmp  CLEAR

; =============================================================================
; IRQ HANDLER - from irq.src
; =============================================================================
;    .page   'irq'
sysirq:
    pha                   ;  save .a,.x,.y
    txa
    pha
    tya
    pha

    lda  ifr1             ;  test if atn
    and  #2
    beq  irq10            ;  not atn

    ; ATN handling would go here - not implemented for KIM-1

irq10:
    lda  ifr2             ;  test if timer
    asl  a
    bpl  irq20            ;  not timer

    jsr  lcc              ;  goto controller

irq20:
    pla                   ;  restore .y,.x,.a
    tay
    pla
    tax
    pla
    rti

; =============================================================================
; CONTROLLER INITIALIZATION - from lccinit.src
; =============================================================================
;    .page   'lcc.init'
cntint:
    lda  #%01101111       ;  data direction
    sta  ddrb2
    and  #$ff-$08-$04-$03 ;  turn motor off,set phase a, led off
    sta  dskcnt

    lda  pcr2             ;  set edge and latch mode
    and  #$ff-$01         ;  neg edge please
;  ca2: soe output hi disable s.o. into 6502
    ora  #$0e
; cb1 input only
; cb2 mode control r/w
    ora  #$e0
    sta  pcr2

    lda  #$41             ;  cont irq, latch mode
    sta  acr2

    lda  #0
    sta  t1ll2
    lda  #tim             ;  ms/irq
    sta  t1hl2
    sta  t1hc2            ;  get 6522's attention

    lda  #$7f             ;  clear all irq sources
    sta  ier2

    lda  #$80+$40
    sta  ifr2             ;  clear bit
    sta  ier2             ;  enable irq

    lda  #$ff             ;  no current drive
    sta  cdrive
    sta  ftnum            ;  init format flag

    lda  #$08             ;  header block id
    sta  hbid

    lda  #$07             ;  data block id
    sta  dbid

    lda  #<inact
    sta  nxtst
    lda  #>inact
    sta  nxtst+1

    lda  #200
    sta  minstp

    lda  #4
    sta  as

    lda  #$4
    sta  af

    rts

; =============================================================================
; MAIN CONTROLLER LOOP - from lcccntrl.src
; =============================================================================
;    .page   'lcc.cntrl'
;
;    *contrl
;
;    main controller loop
;
;    scans job que for jobs
;
;   finds job on current track
;   if it exists
;
lcc:
    tsx                   ;  save current stack pointer
    stx  savsp

    lda  t1lc2            ; reset irq flag

    lda  pcr2             ;  enable s.o. to 6502
    ora  #$0e             ;  hi output
    sta  pcr2

lcc_top:
    ldy  #numjob-1        ;  pointer into job que

cont10:
    lda  jobs,y           ;  find a job (msb set)
    bpl  cont20           ;  not one here

    cmp  #jmpc            ;  test if its a jump command
    bne  cont30

    tya                   ;  put job num in .a
    jmp  ex2

cont30:
    and  #1               ;  get drive #
    beq  cont35

    sty  jobn
    lda  #$0f             ; bad drive # error
    jmp  errr

cont35:
    tax
    sta  drive

    cmp  cdrive           ;  test if current drive
    beq  cont40

    jsr  turnon           ;  turn on drive
    lda  drive
    sta  cdrive
    jmp  end              ;  go clean up

cont40:
    lda  drvst            ;  test if motor up to speed
    bmi  cont50

    asl  a                ;  test if stepping
    bpl  que              ;  not stepping

cont50:
    jmp  end

cont20:
    dey
    bpl  cont10

    jmp  end

que:
    lda  #$20             ;  status=running
    sta  drvst

    ldy  #numjob-1
    sty  jobn

que10:
    jsr  setjb
    bmi  que20

que05:
    dec  jobn
    bpl  que10

    ldy  nxtjob
    jsr  setjb1

    lda  nxtrk
    sta  steps
    asl  steps            ;  steps*2

    lda  #$60             ;  set status=stepping
    sta  drvst

    lda  (hdrpnt),y       ;  get dest track #
    sta  drvtrk
fin:
    jmp  end

que20:
    and  #1               ;  test if same drive
    cmp  drive
    bne  que05

    lda  drvtrk
    beq  gotu             ;  uninit. track #

    sec                   ;  calc distance to track
    sbc  (hdrpnt),y
    beq  gotu             ;  on track

    eor  #$ff             ;  2's comp
    sta  nxtrk
    inc  nxtrk

    lda  jobn             ;  save job# and dist to track
    sta  nxtjob

    jmp  que05

gotu:
    ldx  #4               ;  set track and sectr
    lda  (hdrpnt),y
    sta  tracc

gotu10:
    cmp  trknum-1,x

    dex
    bcs  gotu10

    lda  numsec,x
    sta  sectr

    txa                   ;  set density
    asl  a
    asl  a
    asl  a
    asl  a
    asl  a
    sta  work

    lda  dskcnt
    and  #$9f             ;  clear density bits
    ora  work
    sta  dskcnt

    ldx  drive            ;  drive num in .x

    lda  job              ;  yes, go do the job
    cmp  #bumpc           ;  test for bump
    beq  bmp

exe:
    cmp  #execd           ;  test if execute
    beq  ex

    ; CHANGE: Original 1541 DOS 2.6 used execute command ($E0) with JMP in buffer.
    ; For KIM-1 integration, we add direct format dispatch instead.
    cmp  #fmtcmd & $78    ;  test if format ($F0 masked = $70)
    beq  exfmt

    jmp  seak             ;  do a sector seek

exfmt:
    jmp  formt            ;  CHANGE: direct dispatch to format ROM code

ex:
    lda  jobn             ;  jump to buffer
ex2:
    clc
    adc  #>bufs
    sta  bufpnt+1
    lda  #0
    sta  bufpnt
ex3:
    jmp  (bufpnt)

bmp:
    lda  #$60             ;  set status=stepping
    sta  drvst

    lda  dskcnt
    and  #$ff-$03         ;  set phase a
    sta  dskcnt

    lda  #256-92          ;  step back 45 traks
    sta  steps

    lda  #1               ;  drvtrk now 1
    sta  drvtrk

    jmp  errr             ;  job done return 1

setjb:
    ldy  jobn
setjb1:
    lda  jobs,y
    pha
    bpl  setj10           ;  no job here

    and  #$78
    sta  job
    tya
    asl  a
    adc  #<hdrs
    sta  hdrpnt
    lda  #0               ; CHANGE: original relied on zero page being cleared at init
    sta  hdrpnt+1         ; hdrs is in zero page so high byte must be 0
    tya                   ;  point at buffer
    clc
    adc  #>bufs
    sta  bufpnt+1

setj10:
    ldy  #0
    sty  bufpnt

    pla
    rts

; =============================================================================
; END ROUTINE - from lccend.src
; Motor and stepper control
; =============================================================================
;.page  'lcc.end'
;
;   motor and stepper control
;
;   irq into controller every  8 ms
end:
    lda  t1hl2            ; set irq timer
    sta  t1hc2

    lda  dskcnt

end001:
    and  #$10             ;  test write proctect
    cmp  lwpt
    sta  lwpt             ;  change ?
    beq  end002           ;  no

    lda  #1               ;  yes, set flag
    sta  wpsw

end002:
    lda  phase            ;  test for phase offset
    beq  end40

    cmp  #2
    bne  end003

    lda  #0               ; phase <-- 0
    sta  phase
    beq  end40

end003:
    sta  steps
    lda  #2               ; phase <-- 2
    sta  phase
    jmp  dostep

end40:
    ldx  cdrive           ;  work on active drive only
    bmi  end33x           ;  no active drive

    lda  drvst            ;  test if motor on
    tay
    cmp  #$20             ;  test if anything to do
    bne  end10            ;  something here

end33x:
    jmp  end33            ;  motor just running

end10:
    dec  acltim           ;  dec timer
    bne  end30

    tya                   ;  test if acel
    bpl  end20

    and  #$7f             ;  over, clear acel bit
    sta  drvst

end20:
    and  #$10             ;  test if time out state
    beq  end30

    lda  dskcnt
    and  #$ff-$04         ;  turnoff motor
    sta  dskcnt

    lda  #$ff             ;  no active drive now
    sta  cdrive

    lda  #0               ;  drive inactive
    sta  drvst            ;  clear on bit and timout
    beq  end33x

end30:
    tya                   ;  test if step needed
    and  #$40
    bne  end30x           ;  stepping

    jmp  end33

end30x:
    jmp  (nxtst)          ; goto proper stepper state

inact:
    lda  steps            ;  get abs(steps)
    bpl  inac10

    eor  #$ff
    clc
    adc  #1

inac10:
    cmp  minstp           ;  test if we can accel
    bcs  inac20           ;  too small

    lda  #<short          ; short step mode
    sta  nxtst
    lda  #>short
    sta  nxtst+1
    bne  dostep

inac20:                   ;  calc the # of run steps
    sbc  as
    sbc  as
    sta  rsteps

    lda  as
    sta  aclstp           ;  set  # of accel steps
    lda  #<ssacl
    sta  nxtst
    lda  #>ssacl
    sta  nxtst+1

dostep:
    lda  steps
    bpl  stpin
stpout:
    inc  steps
    ldx  dskcnt
    dex
    jmp  stp

short:
    lda  steps            ; step end ?
    bne  dostep           ; no

    lda  #<setle          ; settle
    sta  nxtst
    lda  #>setle
    sta  nxtst+1
    lda  #5               ;  settle time (5*8=40ms)
    sta  aclstp
    jmp  end33

setle:
    dec  aclstp           ;  settle end ?
    bne  end33            ;  no

    lda  drvst
    and  #$ff-$40
    sta  drvst

    lda  #<inact
    sta  nxtst
    lda  #>inact
    sta  nxtst+1
    jmp  end33

stpin:
    dec  steps
    ldx  dskcnt
    inx

stp:
    txa
    and  #3
    sta  tmp
    lda  dskcnt
    and  #$ff-$03         ;  mask out old
    ora  tmp
    sta  dskcnt
    jmp  end33

ssacl:                    ;  sub acel factor
    sec
    lda  t1hl2
    sbc  af
    sta  t1hc2

    dec  aclstp
    bne  ssa10

    lda  as
    sta  aclstp

    lda  #<ssrun
    sta  nxtst
    lda  #>ssrun
    sta  nxtst+1

ssa10:
    jmp  dostep

ssrun:
    dec  rsteps
    bne  ssa10

    lda  #<ssdec
    sta  nxtst
    lda  #>ssdec
    sta  nxtst+1
    bne  ssa10

ssdec:                    ;  decel
    lda  t1hl2
    clc
    adc  af
    sta  t1hc2

    dec  aclstp
    bne  ssa10

    lda  #<setle          ;  goto settle mode
    sta  nxtst
    lda  #>setle
    sta  nxtst+1

    lda  #5
    sta  aclstp           ;  settle timer

end33:
    lda  pcr2             ;  disable s.o. to 6502
    and  #$ff-$02
    sta  pcr2

    rts

; =============================================================================
; UTILITY ROUTINES - from lccutil.src
; =============================================================================
;    .page 'lcc.util'
;
;  * utility routines
;
errr:
    ldy  jobn             ;  return  job code
    sta  jobs,y

    lda  gcrflg           ;  test if buffer left gcr
    beq  errr10           ;  no

    jsr  wtobin           ;  convert back to binary

errr10:
    jsr  trnoff           ;  start timeout on drive

    ldx  savsp
    txs                   ;  reset stack pointer

    jmp  lcc_top              ;  back to the top

turnon:
    lda  #$a0             ;  turn on drive
; drvst=acel and on
    sta  drvst

    lda  dskcnt           ;  turn motor on and select drive
    ora  #$04             ;  turn motor on
    sta  dskcnt

    lda  #60              ;  delay  1.5 sec
    sta  acltim

    rts

trnoff:
    ldx  cdrive           ;  start time out of current drive
    lda  drvst            ; status=timeout
    ora  #$10
    sta  drvst

    lda  #255             ;  255*.025s time out
    sta  acltim

    rts

; =============================================================================
; FORMAT ROUTINES - from lccfmt1.src
; =============================================================================
;    .page   'lcc.fmt1'
;
;*  format routine for lcc
;
formt:
    lda  ftnum            ;  test if formatting begun
    bpl  l213             ;  yes, positive = normal track format

    ; CHANGE: Check for BAM write phase ($80)
    ; Original DOS wrote BAM/directory in higher-level code we don't have
    cmp  #$80
    beq  do_bam_phase

    ; ftnum=$FF - first call, setup bump
    ldx  drive            ;  no,start up by bumping
    lda  #$60             ;  status=stepping
    sta  drvst            ; CHANGE: was drvst,x - single drive, no indexing needed

    lda  #1               ;  drive track =1
    sta  drvtrk           ; CHANGE: was drvtrk,x - single drive, no indexing needed
    sta  ftnum            ;  start on track 1

    lda  #256-92          ;  bump back 45 steps
    sta  steps

    lda  dskcnt           ; set phase a
    and  #$ff-$03
    sta  dskcnt

    lda  #10              ;  10 errors allowed
    sta  cnt

    lda  #<4000           ;  first guess at track size
    sta  num
    lda  #>4000
    sta  num+1

    jmp  end              ;  back to controller

; CHANGE: BAM write phase dispatch
do_bam_phase:
    jmp  write_bam

l213:
    ldy  #0               ;  test if on right track number
    cmp  (hdrpnt),y
    beq  l214

    sta  (hdrpnt),y       ;  goto right track
    jmp  end

l214:
    lda  dskcnt           ;  test for write protect
    and  #$10
    bne  topp             ;  its ok

    lda  #8               ;  write protect error
    jmp  fmterr

topp:
    jsr  synclr           ;  erase track with sync

    jsr  wrtnum           ;  write out num syncs

    lda  #$55             ;  write out num non sync
    sta  data2

    jsr  wrtnum

    jsr  kill             ;  kill write

    jsr  sync             ;  find sync

    lda  #$40             ;  set timer mode
    ora  acr1
    sta  acr1

    lda  #100-2           ;  set up 100us timer
    sta  t1ll1            ;  cont mode timer
    lda  #0
    sta  t1hl1            ;  hi latch
    sta  t1hc1            ;  get attention of '22

    ldy  #0               ;  time the sync and nonsync segments
    ldx  #0

fwait:
    bit  dskcnt           ;  wait for sync
    bmi  fwait

fwait2:
    bit  dskcnt           ;  wait for no sync
    bpl  fwait2

f000:
    lda  t1lc1            ;  reset ifr

f001:
    bit  dskcnt           ;  time nonsync area
    bpl  f005             ;  time until sync found

    lda  ifr1             ;  test for time out
    asl  a
    bpl  f001             ;  not yet

    inx                   ;  .x is lsb
    bne  f000
    iny                   ;  .y is msb
    bne  f000

    lda  #tolong          ;  cant find sync
    jmp  fmterr

f005:
    stx  t2               ;  save time
    sty  t2+1

    ldx  #0               ;  time sync area
    ldy  #0

f006:
    lda  t1lc1            ;  reset ifr

f007:
    bit  dskcnt           ;  test for  no sync
    bmi  f009

    lda  ifr1             ;  test for time out
    asl  a
    bpl  f007

    inx                   ;  count up another 100us
    bne  f006
    iny                   ;  msb
    bne  f006

    lda  #tolong          ;  cant be this long
    jmp  fmterr

;* now calc the difference between
;* sync and nonsync and adjust
;* num accordingly

f009:
    sec                   ;  t1-t2
    txa
    sbc  t2
    tax
    sta  t1

    tya
    sbc  t2+1
    tay
    sta  t1+1

    bpl  f013             ;  get abs(t1-t2)

    eor  #$ff             ;  make +
    tay
    txa
    eor  #$ff
    tax
    inx
    bne  f013
    iny

f013:
    tya                   ;  test if abs(t1-t2)<4, that is close enough
    bne  f014             ;  msb must be 0

    cpx  #4               ;  test lsb < 4
    bcc  count            ;  its there

f014:
    asl  t1               ;  num=num+(diff/2)
    rol  t1+1

    clc
    lda  t1
    adc  num
    sta  num

    lda  t1+1
    adc  num+1
    sta  num+1

    jmp  topp             ;  try again sam

count:
    ldx  #0               ;  now count #bytes in data segment
    ldy  #0
    clv

cnt10:
    lda  dskcnt           ;  test for sync
    bpl  cnt20            ;  found sync
    bvc  cnt10            ;  test if byte time

    clv                   ;  yes, count it
    inx
    bne  cnt10            ;  keep counting
    iny
    bne  cnt10            ;  to many ?

    lda  #tomany          ;  tomany counts
    jmp  fmterr

cnt20:
    txa                   ;  #bytes=count*2
    asl  a
    sta  tral+1

    tya
    rol  a
    sta  tral

    lda  #$ff-$40         ;  clear cont mode
    and  acr1
    sta  acr1

; =============================================================================
; FORMAT ROUTINES PART 2 - from lccfmt2.src
; =============================================================================
;    .page   'lcc.fmt2'

ds08:
    lda  #$66             ;  min block size 282*5/4 -256=85
    sta  dtrck

    ldx  sectr            ;  total bytes= min*#secors
    ldy  #0
    tya

ds10:
    clc                   ;  min*#sectors
    adc  dtrck
    bcc  ds14

    iny                   ;

ds14:
    iny
    dex
    bne  ds10

    eor  #$ff             ;  get 2s comp
    sec
    adc  #0

    clc
    adc  tral+1
    bcs  ds15

    dec  tral

ds15:
    tax
    tya
    eor  #$ff
    sec
    adc  #0
    clc
    adc  tral

    bpl  ds17

    lda  #tobig           ;  not enough space
    jmp  fmterr

ds17:
    tay
    txa
    ldx  #0

ds20:
    sec
    sbc  sectr
    bcs  ds22

    dey
    bmi  ds30

ds22:
    inx
    bne  ds20

ds30:
    stx  dtrck
    cpx  #gap2            ;  test for min size
    bcs  ds32

    lda  #tosmal          ;  gap2 to small
    jmp  fmterr

ds32:
    clc
    adc  sectr
    sta  remdr            ;  get remaider size

;  create header images

    lda  #0
    sta  sect

    ldy  #0
    ldx  drive

mak10:
    lda  hbid             ;  hbid cs s t id id 0f 0f
    sta  buff0,y
    iny

    iny                   ;  skip checksum

    lda  sect             ;  store sector #
    sta  buff0,y
    iny

    lda  ftnum            ;  store track #
    sta  buff0,y
    iny

    lda  dskid+1          ;  store id low - CHANGE: was dskid+1,x - single drive
    sta  buff0,y
    iny

    lda  dskid            ;  store id hi - CHANGE: was dskid,x - single drive
    sta  buff0,y
    iny

    lda  #$0f             ;  store gap1 bytes
    sta  buff0,y
    iny
    sta  buff0,y
    iny

    lda  #0               ; create checksum
    eor  buff0-6,y
    eor  buff0-5,y
    eor  buff0-4,y
    eor  buff0-3,y

    sta  buff0-7,y        ;  store checksum

    inc  sect             ;  goto next sector

    lda  sect             ;  test if done yet
    cmp  sectr
    bcc  mak10            ;  more to do

    tya                   ;  save block size
    pha

;   create data block of zero

    inx                   ;  .x=0
    txa

crtdat:
    sta  buff2,x
    inx
    bne  crtdat

;  convert header block to gcr

    lda  #>buff0
    sta  bufpnt+1         ;  point at buffer

    jsr  fbtog            ;  convert to gcr with no bid char

    pla                   ;   restore block size
    tay                   ;  move buffer up 79 bytes
    dey                   ;  for i=n-1 to 0:mem{i+69}:=mem{i}:next
    jsr  movup            ; move buf0 up 69 bytes

    jsr  movovr           ;  move ovrbuf up to buffer

;   convert data block to gcr
;   write image
;   leave it in ovrbuf and buffer

    lda  #>buff2          ;  point at buffer
    sta  bufpnt+1

    jsr  chkblk           ;  get block checksum
    sta  chksum
    jsr  bingcr

;   start the format now
;   write out sync header gap1
;   data block

    lda  #0               ;  init counter
    sta  hdrpnt

    jsr  clr_track

wrtsyn:
    lda  #$ff             ;  write sync
    sta  data2

    ldx  #numsyn          ;  write 4  sync

wrts10:
    bvc  *
    clv

    dex
    bne  wrts10

    ldx  #10              ;  write out header
    ldy  hdrpnt

wrts20:
    bvc  *
    clv

    lda  buff0,y          ;  get header data
    sta  data2

    iny
    dex
    bne  wrts20

; * write out gap1

    ldx  #gap1-2          ;  write  gcr bytes

wrts30:
    bvc  *
    clv

    lda  #$55
    sta  data2

    dex
    bne  wrts30

; * write out data block

    lda  #$ff             ;  write data block sync

    ldx  #numsyn

dbsync:
    bvc  *
    clv

    sta  data2

    dex
    bne  dbsync

    ldx  #256-topwrt      ;  write out ovrbuf

wrts40:
    bvc  *
    clv

    lda  ovrbuf,x
    sta  data2

    inx
    bne  wrts40

    ldy  #0

wrts50:
    bvc  *
    clv

    lda  (bufpnt),y
    sta  data2

    iny
    bne  wrts50

    lda  #$55             ;  write gap2(dtrck)
    ldx  dtrck

wgp2:
    bvc  *
    clv

    sta  data2
    dex
    bne  wgp2

    lda  hdrpnt           ;  advance header pointer
    clc
    adc  #10
    sta  hdrpnt

;  done writing sector

    dec  sect             ;  go to next on
    bne  wrtsyn           ;  more to do

    bvc  *                ;  wait for last one to write
    clv

    bvc  *
    clv

    jsr  kill             ;  goto read mode

; =============================================================================
; FORMAT ROUTINES PART 3 - from lccfmt3.src
; Verification
; =============================================================================
;    .page   'lcc.fmt3'
;
;*   format done, now verify it
;
    lda  #200             ;  look at 200 syncs
    sta  trys

comp:
    lda  #0               ;  pointer into headers
    sta  bufpnt

    lda  #>buff0          ;
    sta  bufpnt+1

    lda  sectr            ;  sector counter
    sta  sect

cmpr10:
    jsr  sync             ;  find sync

    ldx  #10
    ldy  #0

cmpr15:
    bvc  *                ;  get header byte
    clv

    lda  data2
    cmp  (bufpnt),y       ;  compare gcr

    bne  cmpr20           ; error

    iny
    dex
    bne  cmpr15           ;  test all bytes

    clc                   ;  update headr pointer
    lda  bufpnt
    adc  #10
    sta  bufpnt

    jmp  tstdat           ;  now test data

cmpr20:
    dec  trys             ;  test if too many errors
    bne  comp

    lda  #notfnd          ;  too many error
    jmp  fmterr

tstdat:
    jsr  sync             ;  find data sync

    ldy  #256-topwrt      ;

tst05:
    bvc  *
    clv

    lda  data2            ;  compare gcr
    cmp  ovrbuf,y

    bne  cmpr20           ;  error

    iny
    bne  tst05            ;  do all ovrbuf

    ldx  #255-3           ;  now do buffer, dont test off bytes

tst10:
    bvc  *
    clv

    lda  data2
    cmp  buff2,y
    bne  cmpr20

    iny
    dex
    bne  tst10

    dec  sect             ;  more sectors to test?
    bne  cmpr10           ;  yes

;  all sectors done ok

    inc  ftnum            ;  goto next track
    lda  ftnum
    cmp  #36              ;  #tracks max
    bcs  fmtend

    jmp  end              ;  more to do

; CHANGE: Modified fmtend to set up BAM/directory write phase
; Original DOS wrote BAM/directory in higher-level code we don't have
fmtend:
    ; All 35 tracks formatted - now write BAM and directory on track 18
    ; Set up to seek to track 18
    ; CHANGE: Write directly to hdrs, not (hdrpnt) which points elsewhere
    lda  #18
    sta  hdrs             ; target track 18
    lda  #0
    sta  hdrs+1           ; sector 0 (for BAM)

    ; Set ftnum to special value to indicate BAM phase
    lda  #$80             ; $80 = write BAM phase
    sta  ftnum

    ; Return to controller - it will step to track 18
    jmp  end

; =============================================================================
; CHANGE: BAM AND DIRECTORY WRITING ROUTINES
; These are NOT part of original Commodore DOS lccfmt code.
; Original DOS wrote BAM/directory in higher-level code (newss.src etc.)
; We add them here since we don't have the full DOS in FranKIMstein
; =============================================================================

; Called when we're on track 18 ready to write BAM
write_bam:
    ; === WRITE BAM TO SECTOR 0 ===
    ; Build BAM in buff2
    jsr  build_bam

    ; Convert to GCR using original DOS routines
    lda  #>buff2
    sta  bufpnt+1
    lda  #0
    sta  bufpnt
    jsr  chkblk           ; original DOS checksum
    sta  chksum
    jsr  bingcr           ; original DOS binary to GCR

    ; Set up header for sector 0 (same as original srch does)
    lda  dskid
    sta  header
    lda  dskid+1
    sta  header+1
    lda  #18              ; track 18
    sta  header+2
    lda  #0               ; sector 0
    sta  header+3
    ; Calculate checksum (same as original srch)
    lda  header
    eor  header+1
    eor  header+2
    eor  header+3
    sta  header+4

    jsr  conhdr           ; original DOS header to GCR in stab

    ldx  #90              ; search 90 sync chars (same as original srch)
    jsr  srch20           ; original DOS find sector - will errr if not found

    ; Write sector - code taken verbatim from wrt (lccwrt.src)
    ldx  #gap1-2          ; wait for gap after header
bam_wrt05:
    bvc  *
    clv
    dex
    bne  bam_wrt05

    ; Enable write - MUST set ddra2 BEFORE pcr2 (original order)
    lda  #$ff             ; make output $ff
    sta  ddra2

    lda  pcr2             ; set write mode
    and  #$ff-$e0
    ora  #$c0
    sta  pcr2

    lda  #$ff             ; write sync
    ldx  #numsyn
    sta  data2
    clv
bam_wrt10:
    bvc  *
    clv
    dex
    bne  bam_wrt10

    ldy  #256-topwrt      ; write from overflow buffer
bam_wrt50:
    lda  ovrbuf,y
    bvc  *
    clv
    sta  data2
    iny
    bne  bam_wrt50

    ldy  #0               ; write rest of gcr from buffer (256 bytes)
bam_wrt60:
    lda  (bufpnt),y
    bvc  *
    clv
    sta  data2
    iny
    bne  bam_wrt60        ; loop until Y wraps to 0

    bvc  *                ; wait for last char to write out

    lda  pcr2             ; goto read mode
    ora  #$e0
    sta  pcr2

    lda  #0               ; make port input
    sta  ddra2

    ; === WRITE DIRECTORY TO SECTOR 1 ===
    ; Build directory in buff2
    jsr  build_dir

    ; Convert to GCR - MUST reset bufpnt (bingcr changed it to ovrbuf)
    lda  #>buff2
    sta  bufpnt+1
    lda  #0
    sta  bufpnt
    jsr  chkblk
    sta  chksum
    jsr  bingcr

    ; Set up header for sector 1
    lda  #1               ; sector 1
    sta  header+3
    lda  header
    eor  header+1
    eor  header+2
    eor  header+3
    sta  header+4

    jsr  conhdr

    ldx  #90
    jsr  srch20           ; find sector 1 - will errr if not found

    ; Write sector - same code as above from wrt
    ldx  #gap1-2
dir_wrt05:
    bvc  *
    clv
    dex
    bne  dir_wrt05

    ; Enable write - MUST set ddra2 BEFORE pcr2 (original order)
    lda  #$ff
    sta  ddra2

    lda  pcr2
    and  #$ff-$e0
    ora  #$c0
    sta  pcr2

    lda  #$ff
    ldx  #numsyn
    sta  data2
    clv
dir_wrt10:
    bvc  *
    clv
    dex
    bne  dir_wrt10

    ldy  #256-topwrt
dir_wrt50:
    lda  ovrbuf,y
    bvc  *
    clv
    sta  data2
    iny
    bne  dir_wrt50

    ldy  #0
dir_wrt60:
    lda  (bufpnt),y
    bvc  *
    clv
    sta  data2
    iny
    bne  dir_wrt60        ; loop until Y wraps to 0

    bvc  *                ; wait for last char to write out

    lda  pcr2             ; goto read mode
    ora  #$e0
    sta  pcr2

    lda  #0               ; make port input
    sta  ddra2

    ; All done - return success via original errr
    lda  #$ff
    sta  ftnum
    lda  #0
    sta  gcrflg
    lda  #1               ; success code
    jmp  errr             ; original DOS error return

; Build BAM structure in buff2
build_bam:
    ; Clear buffer first
    ldx  #0
    txa
bam_clr:
    sta  buff2,x
    inx
    bne  bam_clr

    ; Byte 0: track of first directory sector
    lda  #18
    sta  buff2
    ; Byte 1: sector of first directory sector
    lda  #1
    sta  buff2+1
    ; Byte 2: DOS format type 'A'
    lda  #$41
    sta  buff2+2
    ; Byte 3: reserved (double-sided flag)
    lda  #0
    sta  buff2+3

    ; Bytes 4-143: BAM entries (4 bytes per track)
    ; Each entry: free count, then 3 bytes bitmap
    ldx  #4               ; start at byte 4
    ldy  #1               ; track counter

bam_loop:
    ; Determine sectors for this track
    cpy  #18
    beq  bam_t18          ; track 18 special
    cpy  #18
    bcc  bam_z0           ; tracks 1-17
    cpy  #25
    bcc  bam_z1           ; tracks 19-24
    cpy  #31
    bcc  bam_z2           ; tracks 25-30
    ; Zone 3: tracks 31-35 = 17 sectors
    lda  #17
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 0-7 free
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 8-15 free
    sta  buff2,x
    inx
    lda  #$01             ; sector 16 free, bits 1-7 = 0 (no sectors 17-23)
    sta  buff2,x
    inx
    jmp  bam_next
bam_z2:
    ; Zone 2: tracks 25-30 = 18 sectors
    lda  #18
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 0-7 free
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 8-15 free
    sta  buff2,x
    inx
    lda  #$03             ; sectors 16-17 free, bits 2-7 = 0 (no sectors 18-23)
    sta  buff2,x
    inx
    jmp  bam_next
bam_z1:
    ; Zone 1: tracks 19-24 = 19 sectors
    lda  #19
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 0-7 free
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 8-15 free
    sta  buff2,x
    inx
    lda  #$07             ; sectors 16-18 free, bits 3-7 = 0 (no sectors 19-23)
    sta  buff2,x
    inx
    jmp  bam_next
bam_z0:
    ; Zone 0: tracks 1-17 = 21 sectors
    lda  #21
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 0-7 free
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 8-15 free
    sta  buff2,x
    inx
    lda  #$1F             ; sectors 16-20 free, bits 5-7 = 0 (no sectors 21-23)
    sta  buff2,x
    inx
    jmp  bam_next
bam_t18:
    ; Track 18: 19 sectors - 2 used (BAM + dir) = 17 free
    lda  #17
    sta  buff2,x
    inx
    lda  #$FC             ; sectors 2-7 free, 0-1 used
    sta  buff2,x
    inx
    lda  #$FF             ; sectors 8-15 free
    sta  buff2,x
    inx
    lda  #$07             ; sectors 16-18 free, bits 3-7 = 0 (no sectors 19-23)
    sta  buff2,x
    inx

bam_next:
    iny
    cpy  #36
    bcs  bam_name_start
    jmp  bam_loop

bam_name_start:
    ; Bytes 144-159: Disk name (16 chars from dskname buffer)
    ldx  #144
    ldy  #0
bam_name:
    lda  dskname,y
    sta  buff2,x
    inx
    iny
    cpy  #16
    bcc  bam_name

    ; Bytes 160-161: $A0 padding
    lda  #$A0
    sta  buff2+160
    sta  buff2+161

    ; Bytes 162-163: Disk ID
    lda  dskid
    sta  buff2+162
    lda  dskid+1
    sta  buff2+163

    ; Byte 164: $A0
    lda  #$A0
    sta  buff2+164

    ; Bytes 165-166: DOS type "2A"
    lda  #$32             ; '2'
    sta  buff2+165
    lda  #$41             ; 'A'
    sta  buff2+166

    ; Bytes 167-170: $A0 padding
    lda  #$A0
    sta  buff2+167
    sta  buff2+168
    sta  buff2+169
    sta  buff2+170

    rts

; Build empty directory sector in buff2
build_dir:
    ; Clear buffer
    ldx  #0
    txa
dir_clr:
    sta  buff2,x
    inx
    bne  dir_clr

    ; Byte 0: next track (0 = no more)
    lda  #0
    sta  buff2
    ; Byte 1: next sector ($FF = end marker)
    lda  #$FF
    sta  buff2+1
    ; Rest is already 0 (empty directory entries)

    rts

; =============================================================================
; END OF BAM/DIRECTORY CHANGE
; =============================================================================

; =============================================================================
; FORMAT ROUTINES PART 4 - from lccfmt4.src
; =============================================================================
;    .page   'lcc.fmt4'

synclr:
    lda  pcr2             ;  write entire track with sync
    and  #$ff-$e0
    ora  #$c0
    sta  pcr2

    lda  #$ff             ;  output mode ddr
    sta  ddra2

    sta  data2            ;  sync char

    ldx  #$28             ;  $28*256 bytes
    ldy  #0

syc10:
    bvc  *
    clv

    dey
    bne  syc10

    dex
    bne  syc10

    rts                   ;  leave write on

wrtnum:
    ldx  num              ;  write out num bytes
    ldy  num+1

wrtn10:
    bvc  *
    clv

    dex
    bne  wrtn10

    dey
    bpl  wrtn10

    rts

fmterr:
    dec  cnt              ;  test for retry
    beq  fmte10

    jmp  end

fmte10:
    ldy  #$ff
    sty  ftnum            ;  clear format

    iny
    sty  gcrflg

    jmp  errr

movup:
    lda  buff0,y          ;   move up 69 bytes
    sta  buff0+69,y       ;  move from top down
    dey
    bne  movup

    lda  buff0            ;  do last byte
    sta  buff0+69
    rts

movovr:
    ldy  #68              ;  move ovrbuf into (buffer)

movo10:
    lda  ovrbuf+256-topwrt,y
    sta  (bufpnt),y

    dey
    bpl  movo10

    rts

kill:
    lda  pcr2             ;  disable write
    ora  #$e0
    sta  pcr2
    lda  #$00             ;  make port input now
    sta  ddra2

    rts

clr_track:
    lda  pcr2             ;  enable write
    and  #$ff-$e0
    ora  #$c0
    sta  pcr2

    lda  #$ff             ;  make port an output
    sta  ddra2

    lda  #$55             ;  write a 1f pattern
    sta  data2

    ldx  #$28             ;  $28*256 chars
    ldy  #00
cler10:
    bvc  *
    clv
    dey
    bne  cler10

    dex
    bne  cler10

    rts

;*****************************
;*
;*     fbtog
;*     format binary to gcr conversion
;*
;*     converts buffer to gcr with out hbid
;*
;***************************

fbtog:
    lda  #0               ;  point at buffer
    sta  bufpnt
    sta  savpnt
    sta  bytcnt

    lda  #256-topwrt      ;  put gcr in ovrflow buffer
    sta  gcrpnt

    lda  bufpnt+1         ;  save buffer pointer
    sta  savpnt+1

    lda  #>ovrbuf
    sta  bufpnt+1         ;  store in overbuf

fbg10:
    ldy  bytcnt           ;  get pointer

    lda  (savpnt),y
    sta  btab
    iny

    lda  (savpnt),y
    sta  btab+1
    iny

    lda  (savpnt),y
    sta  btab+2
    iny

    lda  (savpnt),y
    sta  btab+3
    iny
    beq  fbg15            ;  test if done

    sty  bytcnt           ;  save pointer

    jsr  put4bg           ;  convert and store

    jmp  fbg10

fbg15:
    jmp  put4bg           ;  done, return

; =============================================================================
; BINARY TO GCR CONVERSION - from lccbingcr.src
; =============================================================================
;    .page   'lcc.bingcr  -  fast'
;   fast binary to gcr

put4bg:
    lda  #0               ;  clear table
    sta  gtab+1
    sta  gtab+4

    ldy  gcrpnt

    lda  btab
    and  #$f0
    lsr  a
    lsr  a
    lsr  a
    lsr  a
    tax
    lda  bgtab,x

    asl  a
    asl  a
    asl  a
    sta  gtab

    lda  btab
    and  #$0f
    tax
    lda  bgtab,x

    ror  a
    ror  gtab+1
    ror  a
    ror  gtab+1

    and  #$07
    ora  gtab
    sta  (bufpnt),y

    iny

    lda  btab+1
    and  #$f0
    lsr  a
    lsr  a
    lsr  a
    lsr  a
    tax
    lda  bgtab,x

    asl  a
    ora  gtab+1
    sta  gtab+1

    lda  btab+1
    and  #$0f
    tax
    lda  bgtab,x

    rol  a
    rol  a
    rol  a
    rol  a
    sta  gtab+2

    rol  a
    and  #1
    ora  gtab+1
    sta  (bufpnt),y

    iny

    lda  btab+2
    and  #$f0
    lsr  a
    lsr  a
    lsr  a
    lsr  a
    tax
    lda  bgtab,x

    clc
    ror  a
    ora  gtab+2
    sta  (bufpnt),y
    iny

    ror  a
    and  #$80
    sta  gtab+3

    lda  btab+2
    and  #$0f
    tax
    lda  bgtab,x
    asl  a
    asl  a
    and  #$7c
    ora  gtab+3
    sta  gtab+3

    lda  btab+3
    and  #$f0
    lsr  a
    lsr  a
    lsr  a
    lsr  a
    tax
    lda  bgtab,x

    ror  a
    ror  gtab+4
    ror  a
    ror  gtab+4
    ror  a
    ror  gtab+4

    and  #$03
    ora  gtab+3
    sta  (bufpnt),y
    iny
    bne  bing35

    lda  savpnt+1
    sta  bufpnt+1

bing35:
    lda  btab+3
    and  #$0f
    tax
    lda  bgtab,x
    ora  gtab+4
    sta  (bufpnt),y
    iny
    sty  gcrpnt
    rts

bgtab:
    .byte $0a
    .byte $0b
    .byte $12
    .byte $13
    .byte $0e
    .byte $0f
    .byte $16
    .byte $17
    .byte $09
    .byte $19
    .byte $1a
    .byte $1b
    .byte $0d
    .byte $1d
    .byte $1e
    .byte $15

;******************************
;*
;*       binary to gcr conversion
;*
;*   does inplace conversion of
;*   buffer to gcr using overflow
;*   block
;*
;*   creates write image
;*
;*     1 block id char
;*   256 data bytes
;*     1 check sum
;*     2 off bytes
;*   ---
;*   260 binary bytes
;*
;*  260 binary bytes >> 325 gcr
;*
;*  325 = 256 + 69 overflow
;*
;********************************

bingcr:
    lda  #0               ;  init pointers
    sta  bufpnt
    sta  savpnt
    sta  bytcnt

    lda  #256-topwrt
    sta  gcrpnt           ;  start saving gcr here

    sta  gcrflg           ;  buffer converted flag

    lda  bufpnt+1         ;  save buffer pointer
    sta  savpnt+1

    lda  #>ovrbuf         ;  point at overflow
    sta  bufpnt+1

    lda  dbid             ;  store data block id
    sta  btab             ;  and next 3 data bytes

    ldy  bytcnt

    lda  (savpnt),y
    sta  btab+1
    iny

    lda  (savpnt),y
    sta  btab+2
    iny

    lda  (savpnt),y
    sta  btab+3
    iny

bing07:
    sty  bytcnt           ;  next byte to get

    jsr  put4bg           ;  convert and store

    ldy  bytcnt

    lda  (savpnt),y
    sta  btab
    iny
    beq  bing20

    lda  (savpnt),y
    sta  btab+1
    iny

    lda  (savpnt),y
    sta  btab+2
    iny

    lda  (savpnt),y
    sta  btab+3
    iny

    bne  bing07           ;  jmp

bing20:
    lda  chksum           ;  store chksum
    sta  btab+1

    lda  #0               ;  store 0 off byte
    sta  btab+2
    sta  btab+3

    jmp  put4bg           ;  convert and store and return

; =============================================================================
; GCR TO BINARY CONVERSION - from lccgcrbin.src
; =============================================================================
;    .page   'gcrbin.fast'
mask1   = $f8
mask2   = $07
mask2x  = $c0
mask3   = $3e
mask4   = $01
mask4x  = $f0
mask5   = $0f
mask5x  = $80
mask6   = $7c
mask7   = $03
mask7x  = $e0
mask8   = $1f

; fast gcr to binary conversion

get4gb:
    ldy  gcrpnt

    lda  (bufpnt),y
    and  #mask1
    lsr  a
    lsr  a
    lsr  a
    sta  gtab             ;  hi nibble

    lda  (bufpnt),y
    and  #mask2
    asl  a
    asl  a
    sta  gtab+1

    iny                   ;  next byte
    bne  xx05             ;  test for next buffer
    lda  nxtbf
    sta  bufpnt+1
    ldy  nxtpnt

xx05:
    lda  (bufpnt),y
    and  #mask2x
    rol  a
    rol  a
    rol  a
    ora  gtab+1
    sta  gtab+1

    lda  (bufpnt),y
    and  #mask3
    lsr  a
    sta  gtab+2

    lda  (bufpnt),y
    and  #mask4
    asl  a
    asl  a
    asl  a
    asl  a
    sta  gtab+3

    iny                   ;  next

    lda  (bufpnt),y
    and  #mask4x
    lsr  a
    lsr  a
    lsr  a
    lsr  a
    ora  gtab+3
    sta  gtab+3

    lda  (bufpnt),y
    and  #mask5
    asl  a
    sta  gtab+4

    iny                   ;  next byte

    lda  (bufpnt),y
    and  #mask5x
    clc
    rol  a
    rol  a
    and  #1
    ora  gtab+4
    sta  gtab+4

    lda  (bufpnt),y
    and  #mask6
    lsr  a
    lsr  a
    sta  gtab+5

    lda  (bufpnt),y
    and  #mask7
    asl  a
    asl  a
    asl  a
    sta  gtab+6

    iny
; test for overflow during write to binary conversion
    bne  xx06
    lda  nxtbf
    sta  bufpnt+1
    ldy  nxtpnt

xx06:
    lda  (bufpnt),y
    and  #mask7x
    rol  a
    rol  a
    rol  a
    rol  a
    ora  gtab+6
    sta  gtab+6

    lda  (bufpnt),y
    and  #mask8
    sta  gtab+7
    iny

    sty  gcrpnt

    ldx  gtab
    lda  gcrhi,x
    ldx  gtab+1
    ora  gcrlo,x
    sta  btab

    ldx  gtab+2
    lda  gcrhi,x
    ldx  gtab+3
    ora  gcrlo,x
    sta  btab+1

    ldx  gtab+4
    lda  gcrhi,x
    ldx  gtab+5
    ora  gcrlo,x
    sta  btab+2

    ldx  gtab+6
    lda  gcrhi,x
    ldx  gtab+7
    ora  gcrlo,x
    sta  btab+3

    rts

gcrhi:
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $80
    .byte $00
    .byte $10
    .byte $ff             ; error
    .byte $c0
    .byte $40
    .byte $50
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $20
    .byte $30
    .byte $ff             ; error
    .byte $f0
    .byte $60
    .byte $70
    .byte $ff             ; error
    .byte $90
    .byte $a0
    .byte $b0
    .byte $ff             ; error
    .byte $d0
    .byte $e0
    .byte $ff             ; error

gcrlo:
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte $ff             ; error
    .byte 8
    .byte $00
    .byte 1
    .byte $ff             ; error
    .byte $c
    .byte 4
    .byte 5
    .byte $ff             ; error
    .byte $ff             ; error
    .byte 2
    .byte 3
    .byte $ff             ; error
    .byte $f
    .byte 6
    .byte 7
    .byte $ff             ; error
    .byte 9
    .byte $a
    .byte $b
    .byte $ff             ; error
    .byte $d
    .byte $e
    .byte $ff             ; error

gcrbin:
    lda  #0               ;  setup pointers
    sta  gcrpnt
    sta  savpnt
    sta  bytcnt

    lda  #>ovrbuf
    sta  nxtbf

    lda  #255-toprd
    sta  nxtpnt

    lda  bufpnt+1
    sta  savpnt+1

    jsr  get4gb

    lda  btab
    sta  bid              ;  get header id

    ldy  bytcnt
    lda  btab+1
    sta  (savpnt),y
    iny

    lda  btab+2
    sta  (savpnt),y
    iny

    lda  btab+3
    sta  (savpnt),y
    iny

gcrb10:
    sty  bytcnt

    jsr  get4gb

    ldy  bytcnt

    lda  btab
    sta  (savpnt),y
    iny
    beq  gcrb20           ;  test if done yet

    lda  btab+1
    sta  (savpnt),y
    iny

    lda  btab+2
    sta  (savpnt),y
    iny

    lda  btab+3
    sta  (savpnt),y
    iny

    bne  gcrb10           ;  jmp

gcrb20:
    lda  btab+1
    sta  chksum
    lda  savpnt+1         ; restore buffer pointer
    sta  bufpnt+1

    rts

; =============================================================================
; READ ROUTINES - from lccread.src
; =============================================================================
;    .page   'lcc.read'

reed:
    cmp  #0               ;  test if read job
    beq  read01           ;  go test if write
    jmp  wright

read01:
    jsr  dstrt            ;  find header and start reading data

read11:
    bvc  *                ;  wait for byte
    clv

    lda  data2            ;  store away data
    sta  (bufpnt),y       ;  in data buffer
    iny
    bne  read11

    ldy  #255-toprd       ;  store rest in overflow buffer

read20:
    bvc  *
    clv

    lda  data2
    sta  ovrbuf,y
    iny
    bne  read20

    jsr  gcrbin           ;  convert buffer to binary

    lda  bid              ;  test if its a data block
    cmp  dbid
    beq  read28

    lda  #4               ;  not a data block
    jmp  errr

read28:
    jsr  chkblk           ;  calc checksum

    cmp  chksum
    beq  read40

    lda  #5               ;  data block checksum error
    .byte skip2

read40:
    lda  #1               ;  read data block ok
    jmp  errr

dstrt:
    jsr  srch             ;  find header
    jmp  sync             ;  and then data block sync

srch:
    lda  drive            ;  create header image
    asl  a
    tax

    lda  dskid             ;  get master id for the drive - CHANGE: was dskid,x - single drive
    sta  header
    lda  dskid+1           ; CHANGE: was dskid+1,x - single drive
    sta  header+1

    ldy  #0               ;  get track,sector
    lda  (hdrpnt),y
    sta  header+2
    iny
    lda  (hdrpnt),y
    sta  header+3

    lda  #0
;create header checksum
    eor  header
    eor  header+1
    eor  header+2
    eor  header+3

    sta  header+4         ;  store the checksum

    jsr  conhdr           ;  convert header to gcr

    ldx  #90              ;  search 90 sync chars

srch20:
    jsr  sync             ;  find sync

    ldy  #0               ;  test 8 gcr bytes

srch25:
    bvc  *
    clv                   ;  wait for byte

    lda  data2
    cmp  stab,y           ;  test if the same
    bne  srch30           ;  nope

    iny
    cpy  #8
    bne  srch25

    rts

srch30:
    dex                   ; try again
    bne  srch20

    lda  #2               ;  cant find this header
err:
    jmp  errr

sync:
    lda  #$80+80          ;  wait 20 ms for sync max
    sta  timer1

    lda  #3               ;  error code for no sync

sync10:
    bit  timer1           ;  test for time out
    bpl  err
    bit  dskcnt           ;  test for sync
    bmi  sync10

    lda  data2            ;  reset pa latch
    clv
    ldy  #0               ;  clear pointer
    rts

; =============================================================================
; WRITE ROUTINES - from lccwrt.src
; =============================================================================
;    .page   'lcc.wrt'
;
;    * write job
;
;    write out data buffer

wright:
    cmp  #$10             ;  test if write
    beq  wrt05

    jmp  vrfy

wrt05:
    jsr  chkblk           ;  get block checksum
    sta  chksum

    lda  dskcnt           ;  test for write protect
    and  #$10
    bne  wrt10            ;  not  protected

    lda  #8               ;  write protect error
    jmp  errr

wrt10:
    jsr  bingcr           ;  convert buffer to write image

    jsr  srch             ;  find header

    ldx  #gap1-2          ;  wait out header gap

wrt20:
    bvc  *
    clv

    dex                   ;  test if done yet
    bne  wrt20

    lda  #$ff             ;  make output $ff
    sta  ddra2

    lda  pcr2             ;  set write mode
    and  #$ff-$e0
    ora  #$c0
    sta  pcr2

    lda  #$ff             ;  write 5 gcr sync
    ldx  #numsyn          ;
    sta  data2
    clv

wrtsnc:
    bvc  *

    clv
    dex
    bne  wrtsnc

    ldy  #256-topwrt      ;  write out overflow buffer

wrt30:
    lda  ovrbuf,y         ;  get a char
    bvc  *                ;  wait until ready
    clv

    sta  data2            ;  stuff it
    iny
    bne  wrt30            ;  do next char

; write rest of buffer

wrt40:
    lda  (bufpnt),y       ;  now do buffer
    bvc  *                ;  wait until ready
    clv

    sta  data2            ;  stuff it again
    iny
; test if done
    bne  wrt40            ;  do the whole thing

    bvc  *                ;  wait for last char to write out

    lda  pcr2             ;  goto read mode
    ora  #$e0
    sta  pcr2

    lda  #0               ;  make data2 input $00
    sta  ddra2

    jsr  wtobin           ;  convert write image to binary

    ldy  jobn             ;  make job a verify
    lda  jobs,y
    eor  #$30
    sta  jobs,y

    jmp  seak             ;  scan job que

chkblk:
    lda  #0               ;  get eor checksum
    tay

chkb10:
    eor  (bufpnt),y
    iny
    bne  chkb10

    rts                   ;  return checksum in .a

;    * wtobin
;    convert write image back to binary data

wtobin:
    lda  #0               ;  init pointer
    sta  savpnt
    sta  bufpnt           ;  lsb
    sta  nxtpnt

    lda  bufpnt+1         ; goto buffer next
    sta  nxtbf

    lda  #>ovrbuf         ;  use overflow first
    sta  bufpnt+1
    sta  savpnt+1

    lda  #256-topwrt
    sta  gcrpnt           ;  get here first
    sta  bytcnt           ;  store here

    jsr  get4gb           ;  get first four- id and 3 data

    lda  btab             ;  save bid
    sta  bid

    ldy  bytcnt

    lda  btab+1
    sta  (savpnt),y
    iny

    lda  btab+2
    sta  (savpnt),y
    iny

    lda  btab+3
    sta  (savpnt),y
    iny

    sty  bytcnt

wtob14:
    jsr  get4gb           ; do rest of overflow buffer

    ldy  bytcnt

    lda  btab
    sta  (savpnt),y
    iny

    lda  btab+1
    sta  (savpnt),y
    iny
    beq  wtob50

    lda  btab+2
    sta  (savpnt),y
    iny

    lda  btab+3
    sta  (savpnt),y
    iny

    sty  bytcnt
    bne  wtob14           ;  jmp

wtob50:
    lda  btab+2
    sta  (bufpnt),y
    iny

    lda  btab+3
    sta  (bufpnt),y
    iny

    sty  bytcnt

wtob53:
    jsr  get4gb

    ldy  bytcnt

    lda  btab
    sta  (bufpnt),y
    iny

    lda  btab+1
    sta  (bufpnt),y
    iny

    lda  btab+2
    sta  (bufpnt),y
    iny

    lda  btab+3
    sta  (bufpnt),y
    iny

    sty  bytcnt
    cpy  #187
    bcc  wtob53

wtob52:
    lda  #69              ;  move buffer up
    sta  savpnt

    lda  bufpnt+1
    sta  savpnt+1

    ldy  #256-topwrt-1

wtob55:
    lda  (bufpnt),y
    sta  (savpnt),y

    dey
    bne  wtob55

    lda  (bufpnt),y
    sta  (savpnt),y

    ldx  #256-topwrt      ;  move overflow over to buffer

wtob57:
    lda  ovrbuf,x
    sta  (bufpnt),y

    iny
    inx
    bne  wtob57

    stx  gcrflg           ;  clear buffer gcr flag

    rts

;    * verify data block
;   convert to gcr verify image
;   test against data block
;   convert back to binary

vrfy:
    cmp  #$20             ;  test if verify
    beq  vrf10

    jmp  sectsk

vrf10:
    jsr  chkblk           ;  get block checksum
    sta  chksum

    jsr  bingcr           ;  convert to verify image

    jsr  dstrt

    ldy  #256-topwrt
vrf15:
    lda  ovrbuf,y         ;  get char
    bvc  *
    clv

    eor  data2            ;  test if same
    bne  vrf20            ; verify error

    iny
    bne  vrf15            ;  next byte

vrf30:
    lda  (bufpnt),y       ;  now do buffer

    bvc  *
    clv                   ;  wait for char

    eor  data2            ;  test if same
    bne  vrf20            ;  error

    iny
    cpy  #$fd             ;  dont test off bytes
    bne  vrf30

    jmp  done             ;  verify ok

vrf20:
    lda  #7               ;  verify error
    jmp  errr

sectsk:
    jsr  srch             ;  sector seek
    jmp  done

; =============================================================================
; SEEK ROUTINES - from lccseek.src
; =============================================================================
;    .page   'lcc.seek'

seak:
    ldx  #90              ;  search 90 headers
    stx  tmp

    ldx  #0               ; read in 8 gcr bytes

    lda  #$52             ;  header block id
    sta  stab

seek10:
    jsr  sync             ;  find sync char

    bvc  *                ;  wait for block id
    clv

    lda  data2
    cmp  stab             ;  test if header block
    bne  seek20           ;  not header

seek15:
    bvc  *
    clv                   ;  read in gcr header

    lda  data2
    sta  stab+1,x

    inx
    cpx  #7
    bne  seek15

    jsr  cnvbin           ;  convert header in stab to binary in header

    ldy  #4               ;  compute checksum
    lda  #0

seek30:
    eor  header,y
    dey
    bpl  seek30

    cmp  #0               ;  test if ok
    bne  cserr            ;  nope, checksum error in header

    ldx  cdrive           ;  update drive track#
    lda  header+2
    sta  drvtrk            ; CHANGE: was drvtrk,x - single drive

    lda  job              ;  test if a seek job
    cmp  #$30
    beq  eseek

    lda  cdrive
    asl  a                ;  test if correct id
    tay
    lda  dskid             ; CHANGE: was dskid,y - single drive
    cmp  header
    bne  badid
    lda  dskid+1           ; CHANGE: was dskid+1,y - single drive
    cmp  header+1
    bne  badid

    jmp  wsect            ;  find best sector to service

seek20:
    dec  tmp              ;  search more?
    bne  seek10           ; yes

    lda  #2               ;  cant find a sector
    jsr  errr

eseek:
    lda  header           ; harris fix....
    sta  dskid            ; ....
    lda  header+1         ; ....
    sta  dskid+1          ; ....

done:
    lda  #1               ;  return ok code
    .byte skip2

badid:
    lda  #11              ;  disk id mismatch
    .byte skip2

cserr:
    lda  #9               ;  checksum error in header
    jmp  errr

wsect:
    lda  #$7f             ;  find best job
    sta  csect

    lda  header+3         ;  get upcoming sector #
    clc
    adc  #2
    cmp  sectr
    bcc  l460

    sbc  sectr            ; wrap around

l460:
    sta  nexts            ;  next sector

    ldx  #numjob-1
    stx  jobn

    ldx  #$ff

l480:
    jsr  setjb
    bpl  l470

    sta  work
    and  #1
    cmp  cdrive           ;  test if same drive
    bne  l470             ;  nope

    ldy  #0               ;  test if same track
    lda  (hdrpnt),y
    cmp  tracc
    bne  l470

    lda  job              ;  test if execute job
    cmp  #execd
    beq  l465

    ldy  #1
    sec
    lda  (hdrpnt),y
    sbc  nexts
    bpl  l465

    clc
    adc  sectr

l465:
    cmp  csect
    bcs  l470

    pha                   ;  save it
    lda  job
    beq  tstrdj           ;  must be a read

    pla
    cmp  #wrtmin          ;  {if(csect<9)return;
    bcc  l470             ;  {if(csect>12)return;

    cmp  #wrtmax
    bcs  l470

doitt:
    sta  csect            ; its better
    lda  jobn
    tax
    adc  #>bufs
    sta  bufpnt+1

    bne  l470

tstrdj:
    pla
    cmp  #rdmax           ;  if(csect>6)return;
    bcc  doitt

l470:
    dec  jobn
    bpl  l480

    txa                   ;  test if a job to do
    bpl  l490

    jmp  end              ;  no job found

l490:
    stx  jobn
    jsr  setjb
    lda  job
    jmp  reed

cnvbin:
    lda  bufpnt
    pha
    lda  bufpnt+1
    pha                   ;  save buffer pntr

    lda  #<stab
    sta  bufpnt           ;  point at gcr code
    lda  #>stab
    sta  bufpnt+1

    lda  #0
    sta  gcrpnt

    jsr  get4gb           ;  convert 4 bytes

    lda  btab+3
    sta  header+2

    lda  btab+2
    sta  header+3

    lda  btab+1
    sta  header+4

    jsr  get4gb           ;  get 2 more

    lda  btab             ;  get id
    sta  header+1
    lda  btab+1
    sta  header

    pla
    sta  bufpnt+1         ; restore pointer
    pla
    sta  bufpnt

    rts

; =============================================================================
; HEADER CONVERSION - from lccconhdr.src
; =============================================================================
;    .page   'lcc.conhdr'
;
;    *conhdr
;
;    convert header
;    into gcr search image
;    and place in stab
;
;   image contains :
;
;   00 id id tr sc cs hbid

conhdr:
    lda  bufpnt+1         ; save buffer pointer
    sta  savpnt+1

    lda  #>stab
    sta  bufpnt+1

    lda  #<stab
    sta  gcrpnt

    lda  hbid
    sta  btab

    lda  header+4
    sta  btab+1

    lda  header+3
    sta  btab+2

    lda  header+2
    sta  btab+3

    jsr  put4bg

    lda  header+1
    sta  btab

    lda  header
    sta  btab+1

    lda  #0
    sta  btab+2
    sta  btab+3

    jsr  put4bg

    lda  savpnt+1         ; restore buffer pointer
    sta  bufpnt+1

    rts

; =============================================================================
; SAVE COMMAND - Save memory to disk
; =============================================================================
CMD_SAVE:
    jsr  CRLF
    ; Prompt for filename
    lda  #'F'
    jsr  OUTCH
    lda  #'I'
    jsr  OUTCH
    lda  #'L'
    jsr  OUTCH
    lda  #'E'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Read filename (up to 16 chars)
    ldx  #0
save_name_loop:
    jsr  GETCH
    cmp  #$0D             ; RETURN?
    beq  save_name_done
    cpx  #16
    bcs  save_name_loop   ; ignore if too many
    sta  savename,x
    jsr  OUTCH
    inx
    bne  save_name_loop

save_name_done:
    ; Pad rest with $A0
    lda  #$A0
save_name_pad:
    cpx  #16
    bcs  save_get_sa
    sta  savename,x
    inx
    bne  save_name_pad

save_get_sa:
    ; Prompt for start address
    jsr  CRLF
    lda  #'S'
    jsr  OUTCH
    lda  #'A'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Clear input buffer
    lda  #0
    sta  INL
    sta  INH

    ; Get 4 hex digits
    jsr  get_hex_addr
    lda  INL
    sta  sal
    lda  INH
    sta  sah

save_get_ea:
    ; Prompt for end address
    jsr  CRLF
    lda  #'E'
    jsr  OUTCH
    lda  #'A'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Clear input buffer
    lda  #0
    sta  INL
    sta  INH

    ; Get 4 hex digits
    jsr  get_hex_addr
    lda  INL
    sta  eal
    lda  INH
    sta  eah

    ; Set up source pointer IMMEDIATELY after getting addresses
    ; CHANGE: Moved earlier to prevent corruption by disk routines
    lda  sal
    sta  POINTL
    lda  sah
    sta  POINTH

; =============================================================================
; SAVE COMMAND - main logic
; Uses original 1541 DOS 2.6 routines where possible
; =============================================================================

    ; Initialize byte count = EA - SA + 1 + 2 (for load addr)
    sec
    lda  eal
    sbc  sal
    sta  sbytesl
    lda  eah
    sbc  sah
    sta  sbytesh
    clc
    lda  sbytesl
    adc  #3               ; +1 for inclusive, +2 for load address
    sta  sbytesl
    lda  sbytesh
    adc  #0
    sta  sbytesh

    ; Print SAVING message
    jsr  CRLF
    lda  #'S'
    jsr  OUTCH
    lda  #'A'
    jsr  OUTCH
    lda  #'V'
    jsr  OUTCH
    lda  #'I'
    jsr  OUTCH
    lda  #'N'
    jsr  OUTCH
    lda  #'G'
    jsr  OUTCH
    jsr  CRLF

    ; Initialize drive
    lda  #0
    sta  drvnum
    sta  cdrive
    sta  drive
    sta  jobnum           ; use job 0
    lda  #10
    sta  secinc           ; sector interleave
    jsr  turnon           ; turn on motor

    ; Read BAM from track 18 sector 0 using job 0
    lda  dirtrk
    sta  track
    sta  hdrs             ; job 0 track
    lda  #0
    sta  sector
    sta  hdrs+1           ; job 0 sector
    lda  #jread
    sta  jobs             ; post read job
    jsr  simpwait
    beq  bam1ok
    jmp  saverr
bam1ok:

    ; Copy disk ID from BAM to dskid so controller can verify headers
    ; CHANGE: Added to fix ID mismatch errors on writes
    lda  buff0+$A2
    sta  dskid
    lda  buff0+$A3
    sta  dskid+1

    ; Copy BAM from buff0 to bam_work ($0600)
    ; CHANGE: Original DOS 2.6 code uses complex bam cache, we use simple copy
    ldx  #0
cpbam1:
    lda  buff0,x
    sta  bam_work,x
    inx
    bne  cpbam1

    ; Find first free sector using nxtts algorithm from tstfnd.src
    lda  dirtrk
    sec
    sbc  #1
    sta  track            ; start at track 17
    lda  #0
    sta  sector
    jsr  nxtts            ; find free sector
    bcc  sec1ok
    jmp  savfull          ; disk full
sec1ok:

    ; Mark sector as used
    jsr  usedts

    ; Save first track/sector for directory entry
    lda  track
    sta  ftrack
    sta  curtk
    lda  sector
    sta  fsector
    sta  cursec

    ; Initialize block counter
    lda  #0
    sta  blkcnt

    ; POINTL/POINTH already set up above, before disk operations
    ; First sector: data starts at byte 4 (after link + load addr)
    lda  #4
    sta  secptr

    ; Clear buff0 for building sector
    ldx  #0
    txa
clrbuf:
    sta  buff0,x
    inx
    bne  clrbuf

    ; Store load address in first sector
    lda  sal
    sta  buff0+2
    lda  sah
    sta  buff0+3

; Main data write loop
wrtloop:
    ; Check if we're done
    lda  sbytesh
    bne  wrtcopy          ; high byte not zero, keep copying
    lda  sbytesl
    cmp  #3               ; 3 means done (we added +3)
    bcc  wrtlast          ; done, write last sector

wrtcopy:
    ; Copy one byte from user memory to buffer
    ldy  #0
    lda  (POINTL),y
    ldy  secptr
    sta  buff0,y
    inc  secptr
    inc  POINTL
    bne  wrtdec
    inc  POINTH

wrtdec:
    ; Decrement byte counter
    lda  sbytesl
    bne  wrtdec2
    dec  sbytesh
wrtdec2:
    dec  sbytesl

    ; Check if buffer full
    lda  secptr
    bne  wrtloop          ; not full yet

    ; Buffer full - find next sector
    jsr  nxtts            ; find next free sector
    bcc  wrt2ok
    jmp  savfull
wrt2ok:
    jsr  usedts           ; mark it used

    ; Store link to next sector
    lda  track
    sta  buff0            ; next track
    lda  sector
    sta  buff0+1          ; next sector

    ; Write current sector using job 0
    lda  curtk
    sta  hdrs
    lda  cursec
    sta  hdrs+1
    lda  #jwrite
    sta  jobs
    jsr  simpwait
    beq  wrt3ok
    jmp  saverr
wrt3ok:
    inc  blkcnt

    ; Move to next sector
    lda  track
    sta  curtk
    lda  sector
    sta  cursec

    ; Clear buffer for next sector
    ldx  #0
    txa
clrbuf2:
    sta  buff0,x
    inx
    bne  clrbuf2

    ; Data starts at byte 2 in continuation sectors
    lda  #2
    sta  secptr
    jmp  wrtloop

; Write last (partial) sector
wrtlast:
    lda  #0
    sta  buff0            ; next track = 0 (end of file)
    lda  secptr
    sec
    sbc  #1               ; CHANGE: secptr points to NEXT byte, we need LAST byte
    sta  buff0+1          ; last valid byte position

    ; Write last sector
    lda  curtk
    sta  hdrs
    lda  cursec
    sta  hdrs+1
    lda  #jwrite
    sta  jobs
    jsr  simpwait
    beq  wrt4ok
    jmp  saverr
wrt4ok:
    inc  blkcnt

    ; Update directory
    ; Read directory sector (track 18, sector 1)
    lda  dirtrk
    sta  hdrs
    lda  #1
    sta  hdrs+1
    lda  #jread
    sta  jobs
    jsr  simpwait
    beq  dir1ok
    jmp  saverr
dir1ok:
    ; Find empty entry (file type = 0)
    ldx  #0
fnddent:
    lda  buff0+2,x        ; file type at offset 2 in entry
    beq  fndent           ; found empty
    txa
    clc
    adc  #32              ; next entry
    tax
    bne  fnddent          ; check all 8
    jmp  savfull          ; directory full

fndent:
    ; X = offset to empty entry
    ; Fill in directory entry
    lda  #$82             ; PRG file, closed
    sta  buff0+2,x        ; file type
    lda  ftrack
    sta  buff0+3,x        ; first track
    lda  fsector
    sta  buff0+4,x        ; first sector

    ; Copy filename (16 bytes at offset 5)
    stx  t0               ; save entry offset
    txa
    clc
    adc  #5
    tax                   ; X = offset to filename
    ldy  #0
cpname:
    lda  savename,y
    sta  buff0,x
    inx
    iny
    cpy  #16
    bcc  cpname

    ; Store block count at entry offset 28-29
    ; Entry offset 28 = sector offset 30 (entries start at byte 2)
    ldx  t0
    lda  blkcnt
    sta  buff0+30,x       ; blocks low
    lda  #0
    sta  buff0+31,x       ; blocks high

    ; Write directory sector
    lda  dirtrk
    sta  hdrs
    lda  #1
    sta  hdrs+1
    lda  #jwrite
    sta  jobs
    jsr  simpwait
    beq  dir2ok
    jmp  saverr
dir2ok:

    ; Write updated BAM
    ; Copy bam_work back to buff0
    ldx  #0
cpbam2:
    lda  bam_work,x
    sta  buff0,x
    inx
    bne  cpbam2

    ; Write BAM to track 18 sector 0
    lda  dirtrk
    sta  hdrs
    lda  #0
    sta  hdrs+1
    lda  #jwrite
    sta  jobs
    jsr  simpwait
    bne  saverr

    ; Success!
    lda  #'O'
    jsr  OUTCH
    lda  #'K'
    jsr  OUTCH
    jmp  savedone

saverr:
    lda  #'E'
    jsr  OUTCH
    lda  #'R'
    jsr  OUTCH
    jmp  savedone

savfull:
    lda  #'F'
    jsr  OUTCH
    lda  #'U'
    jsr  OUTCH
    lda  #'L'
    jsr  OUTCH
    lda  #'L'
    jsr  OUTCH

savedone:
    jsr  CRLF
    jmp  CLEAR

; =============================================================================
; Simple job wait (no error recovery)
; Returns Z=1 if success (A=1)
; =============================================================================
simpwait:
    lda  jobs
    bmi  simpwait         ; wait while MSB set
    cmp  #1               ; success?
    rts

; =============================================================================
; DOS ROUTINES - from original 1541 Commodore 2.6 DOS source
; Adapted to use bam_work instead of complex BAM cache
; =============================================================================


; next track & sector - from tstfnd.src
;  returns next available track & sector
;  given current t & s
;
;  allocation is from track 18
;  towards 1 & 35, by full tracks
;
; CHANGE: Uses bam_work instead of setbam cache
; CHANGE: Returns carry set if disk full instead of calling cmderr
nxtts:
        lda  #3
        sta  temp
        lda  #1         ; set no write bam
        ora  wbam
        sta  wbam
nxt1:
        lda  temp
        pha     ; save temp
        jsr  setbam     ; CHANGE: our simplified setbam
        pla
        sta  temp       ; restore temp
        lda  (bmpnt),y
        bne  fndnxt
        lda  track
        cmp  dirtrk
        beq  nxterr
        bcc  nxt2
        inc  track
        lda  track
        cmp  maxtrk
        bcc  nxt1       ; CHANGE: was bne, but maxtrk is a byte now
        ldx  dirtrk
        dex
        stx  track
        lda  #0
        sta  sector
        dec  temp
        bne  nxt1
nxterr:
        sec             ; CHANGE: return carry set instead of cmderr
        rts
nxt2:
        dec  track
        bne  nxt1       ; track > 0, keep going
        ldx  dirtrk
        inx
        stx  track
        lda  #0
        sta  sector
        dec  temp
        bne  nxt1
        beq  nxterr

; find the next optimum sector - from tstfnd.src
; next sector=current sector+n
fndnxt:
        lda  sector
        clc
        adc  secinc
        sta  sector
        lda  track
        jsr  maxsec     ; get max sectors for track
        sta  lstsec
        sta  cmd
        cmp  sector
        bcs  fndn0

        sec
        lda  sector
        sbc  lstsec
        sta  sector
        beq  fndn0

        dec  sector
fndn0:
        jsr  getsec
        beq  fndn2
fndn1:
        clc             ; CHANGE: return carry clear = found
        rts             ; CHANGE: was jmp wused, we call usedts separately
fndn2:
        lda  #0
        sta  sector
        jsr  getsec
        bne  fndn1
        jmp  nxterr     ; CHANGE: was jmp derr

; set bam and find available sector - from tstfnd.src
; starting at sector
getsec:
        jsr  setbam
        tya
        pha     ; save .y
        jsr  avck       ; check bits & count

        lda  track
        jsr  maxsec
        sta  lstsec     ; save max sector #
        pla
        sta  temp       ; temp:= old .y for freus3
gs10:
        lda  sector
        cmp  lstsec
        bcs  gs20

        jsr  freus3
        bne  gs30

        inc  sector
        bne  gs10       ; bra
gs20:
        lda  #0
gs30:
        rts     ; (z=1): used

; bit map validity check - from tstfnd.src
avck:
        lda  temp
        pha     ; save temp
        lda  #0
        sta  temp       ; temp:=0
; for .y:=bamsiz to 1 do;
        ldy  bamsiz
        dey
ac10:           ; for .x:=7 to 0 do;
        ldx  #7         ; count the bits
ac20:           ; if @b{.y} & bmask{x}
;  then temp:=temp+1
        lda  (bmpnt),y
        and  bmask,x
        beq  ac30
        inc  temp
ac30:           ; end .x
        dex
        bpl  ac20
; end .y
        dey
        bne  ac10
; if @b{.y} <> temp
;  then cmder2(direrr);
        lda  (bmpnt),y
        cmp  temp
        bne  ac40       ; counts do not match

        pla
        sta  temp       ; restore temp
        rts
ac40:
        ; CHANGE: silently ignore BAM count mismatch instead of error
        pla
        sta  temp
        rts

; .a=track # ,returns #sectors on this track - from tstfnd.src
maxsec:
        ldx  nzones
max1:
        cmp  trknum-1,x
        dex
        bcs  max1
        lda  numsec,x
        rts



; SIMPLIFIED setbam - from frets.src
; CHANGE: Uses bam_work directly instead of complex cache
; Sets bmpnt = bam_work + track*4, Y = 0
setbam:
        lda  track
        asl  a
        asl  a          ; A = track * 4
        clc
        adc  #<bam_work
        sta  bmpnt
        lda  #>bam_work
        adc  #0
        sta  bmpnt+1
        ldy  #0
        rts

; mark track,sector,(bmpnt) as used - from frets.src
; CHANGE: Simplified, no ndbl/ndbh tracking, no disk full check
usedts:
        jsr  freuse     ; calc index into bam
        beq  userts     ; used, no action
        lda  (bmpnt),y          ; get bits
        eor  bmask,x    ; mark sec used
        sta  (bmpnt),y
        ldy  temp
        lda  (bmpnt),y          ; get count
        sec
        sbc  #1         ;  dec one
        sta  (bmpnt),y          ; save it
userts:
        rts

; calculates index into bam - from frets.src
; for frets and usedts
freuse:
        jsr  setbam
        tya
freus2:
        sta  temp       ; save index
freus3:
        lda  sector     ; a=sector/8
        lsr  a
        lsr  a
        lsr  a          ; for which of three bytes
        sec
        adc  temp       ; calc index
        tay
        lda  sector     ; bit in that byte
        and  #7
        tax
        lda  (bmpnt),y          ; get the byte
        and  bmask,x    ; test it
        rts     ; z=1=used,z=0=free

; bmask table - from frets.src (verbatim)
bmask:
        .byte  1,2,4,8,16,32,64,128

; Get 4 hex digits into INH:INL
get_hex_addr:
        ldx  #4
gha_loop:
        jsr  GETCH
        pha               ; CHANGE: save char before OUTCH trashes A
        jsr  OUTCH
        pla               ; CHANGE: restore char for PACK
        jsr  PACK
        dex
        bne  gha_loop
        rts

; =============================================================================
; LOAD COMMAND - Load file from disk
; 
; GLUE CODE: This command is glue code that calls original DOS job queue
; operations. The original DOS LOAD uses the channel system (lindx, lintab,
; buf0/buf1, etc.) and command parser (cmdbuf, filtbl, f2cnt) which would
; require bringing in a ton of buffer management code.
; Instead, this simplified version:
; - Uses itrial pattern (SEEK then copy header) from tst2.src for disk ID
; - Reads directory sectors directly using job queue
; - Compares filename byte-by-byte
; - Reads file data using job queue, stores to memory at load address
; =============================================================================
CMD_LOAD:
    jsr  CRLF
    ; GLUE CODE: Prompt for filename (KIM-1 style, not original DOS)
    lda  #'F'
    jsr  OUTCH
    lda  #'I'
    jsr  OUTCH
    lda  #'L'
    jsr  OUTCH
    lda  #'E'
    jsr  OUTCH
    lda  #'?'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH

    ; Read filename (up to 16 chars) into savename buffer
    ldx  #0
load_name_loop:
    jsr  GETCH
    cmp  #$0D             ; RETURN?
    beq  load_name_done
    cpx  #16
    bcs  load_name_loop   ; ignore if too many
    sta  savename,x
    pha                   ; CHANGE: save char before OUTCH trashes A
    jsr  OUTCH
    pla                   ; CHANGE: restore char
    inx
    bne  load_name_loop

load_name_done:
    ; Pad rest with $A0 (same as directory format)
    lda  #$A0
load_name_pad:
    cpx  #16
    bcs  load_start
    sta  savename,x
    inx
    bne  load_name_pad

load_start:
    jsr  CRLF

    ; GLUE CODE: Initialize drive variables
    lda  #0
    sta  drvnum
    sta  cdrive
    sta  drive
    sta  jobnum           ; use job 0
    jsr  turnon           ; original DOS from lcc

    ; Pattern from itrial/initdr in tst2.src:
    ; 1. SEEK to directory track to read header (gets disk ID)
    ; 2. Copy disk ID from header to dskid  
    ; 3. Then READ operations will work
    
    ; Step 1: SEEK to track 18 sector 0 (from itrial in tst2.src)
    lda  dirtrk
    sta  track
    sta  hdrs
    lda  #0
    sta  sector
    sta  hdrs+1
    lda  #jseek           ; SEEK job ($B0) - reads header only
    sta  jobs
    jsr  simpwait
    ; Don't check error - SEEK fills header buffer regardless

    ; Step 2: Copy disk ID from header to dskid (from initdr in tst2.src)
    ; Original: lda header / sta dskid,x (x=drvnum*2)
    ; CHANGE: We only have one drive, so no indexing needed
    lda  header
    sta  dskid
    lda  header+1
    sta  dskid+1

    ; Step 3: Now READ the BAM with correct dskid (uses job queue)
    lda  dirtrk
    sta  hdrs
    lda  #0
    sta  hdrs+1
    lda  #jread
    sta  jobs
    jsr  simpwait
    beq  load_bam_ok
    jmp  loaderr

load_bam_ok:

    ; GLUE CODE: Start directory search at track 18 sector 1
    ; Original DOS uses srchst from lookup.src which requires channel system
    lda  dirtrk
    sta  track
    sta  hdrs
    lda  #1
    sta  sector
    sta  hdrs+1

load_dir_read:
    ; GLUE CODE: Read directory sector using job queue
    ; Original DOS uses opnird/nxtbuf which require channel system
    lda  track
    sta  hdrs
    lda  sector
    sta  hdrs+1
    lda  #jread
    sta  jobs
    jsr  simpwait
    beq  load_dir_ok
    jmp  loaderr
load_dir_ok:
    ; GLUE CODE: Search 8 entries in this sector
    ; Original DOS uses search/compar from lookup.src with dirbuf pointer
    ; Entry structure: byte 0=type, 1-2=T/S, 3-18=filename (at sector+2)
    lda  #0
    sta  index            ; entry offset (0, 32, 64, ...)

load_check_entry:
    ; GLUE CODE: Check file type at entry
    ; Original DOS: lda (dirbuf),y with y=0
    ldx  index
    lda  buff0+2,x        ; file type (entries start at byte 2 in sector)
    beq  load_next_entry  ; $00 = deleted/empty, skip
    and  #$80
    beq  load_next_entry  ; bit 7 clear = scratched, skip

    ; GLUE CODE: Compare filename (original DOS uses compar in lookup.src)
    ; Filename at entry+3 (sector byte = index+2+3 = index+5)
    ldy  #0
load_cmp_name:
    lda  savename,y
    cmp  buff0+5,x        ; compare with dir entry filename
    bne  load_next_entry  ; mismatch
    inx
    iny
    cpy  #16
    bcc  load_cmp_name

    ; GLUE CODE: Filename matches - get track/sector
    ; Original DOS stores in filtrk,x / filsec,x tables
    ldx  index
    lda  buff0+3,x        ; first track
    sta  filtrk
    lda  buff0+4,x        ; first sector
    sta  filsec
    jmp  load_found

load_next_entry:
    ; GLUE CODE: Move to next entry (+32 bytes)
    ; Original DOS uses incptr with #32
    lda  index
    clc
    adc  #32
    sta  index
    cmp  #0               ; wrapped = checked all 8 entries
    bne  load_check_entry

    ; GLUE CODE: Check link to next directory sector
    ; Original DOS uses nxtbuf to follow chain
    lda  buff0            ; next track
    beq  load_not_found   ; track=0 means end of directory
    sta  track
    lda  buff0+1
    sta  sector
    jmp  load_dir_read

load_not_found:
    ; GLUE CODE: Print error message
    lda  #'N'
    jsr  OUTCH
    lda  #'O'
    jsr  OUTCH
    lda  #'T'
    jsr  OUTCH
    lda  #' '
    jsr  OUTCH
    lda  #'F'
    jsr  OUTCH
    lda  #'N'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    jmp  loaddone

load_found:
    ; GLUE CODE: Print status
    lda  #'L'
    jsr  OUTCH
    lda  #'O'
    jsr  OUTCH
    lda  #'A'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    lda  #'I'
    jsr  OUTCH
    lda  #'N'
    jsr  OUTCH
    lda  #'G'
    jsr  OUTCH
    jsr  CRLF

    ; GLUE CODE: Read first sector of file using job queue
    lda  filtrk
    sta  track
    sta  hdrs
    lda  filsec
    sta  sector
    sta  hdrs+1
    lda  #jread
    sta  jobs
    jsr  simpwait
    beq  load_first_ok
    jmp  loaderr
load_first_ok:
    ; GLUE CODE: Get load address from bytes 2-3 of first sector
    ; Store in sal/sah and POINTL/POINTH for destination pointer
    lda  buff0+2          ; low byte of load address
    sta  sal
    sta  POINTL
    lda  buff0+3          ; high byte of load address
    sta  sah
    sta  POINTH

    ; GLUE CODE: Print load address
    lda  #'A'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    lda  #'R'
    jsr  OUTCH
    lda  #'='
    jsr  OUTCH
    lda  sah
    jsr  PRTBYT
    lda  sal
    jsr  PRTBYT
    jsr  CRLF

    ; GLUE CODE: Set up for reading file data
    ; Original DOS uses rdbyt with double buffering
    ; First sector: data starts at byte 4 (after T/S link + load addr)
    lda  #4
    sta  secptr

    ; Check if this is last sector (track link = 0)
    lda  buff0            ; next track
    bne  load_read_loop   ; not last sector
    ; Last sector - byte 1 has index of last valid byte
    lda  buff0+1
    sta  lstsec
    jmp  load_first_data

load_read_loop:
    ; Not last sector - read to byte 255
    lda  #$FF
    sta  lstsec

load_first_data:
    ; Fall through to read data

load_data_loop:
    ; GLUE CODE: Copy byte from buffer to user memory
    ; Original DOS uses rdbyt which handles double buffering
    ldx  secptr
    lda  buff0,x
    ldy  #0
    sta  (POINTL),y       ; store to destination

    ; Increment destination pointer
    inc  POINTL
    bne  load_no_carry
    inc  POINTH
load_no_carry:

    ; Check if done with this sector
    lda  secptr
    cmp  lstsec
    beq  load_next_sector
    inc  secptr
    jmp  load_data_loop

load_next_sector:
    ; GLUE CODE: Check if there's another sector (follow T/S chain)
    ; Original DOS uses nxtbuf/dblbuf for read-ahead
    lda  buff0            ; next track
    beq  load_done_ok     ; track=0 = end of file

    ; Read next sector
    sta  track
    sta  hdrs
    lda  buff0+1
    sta  sector
    sta  hdrs+1
    lda  #jread
    sta  jobs
    jsr  simpwait
    beq  load_next_ok
    jmp  loaderr
load_next_ok:
    ; For continuation sectors, data starts at byte 2
    lda  #2
    sta  secptr

    ; Check if this is last sector
    lda  buff0
    bne  load_read_loop   ; not last, read full sector
    ; Last sector
    lda  buff0+1
    sta  lstsec
    jmp  load_data_loop

load_done_ok:
    ; GLUE CODE: Print end address
    jsr  CRLF
    lda  #'E'
    jsr  OUTCH
    lda  #'N'
    jsr  OUTCH
    lda  #'D'
    jsr  OUTCH
    lda  #'='
    jsr  OUTCH
    lda  POINTH
    jsr  PRTBYT
    lda  POINTL
    jsr  PRTBYT
    jsr  CRLF
    lda  #'O'
    jsr  OUTCH
    lda  #'K'
    jsr  OUTCH
    jmp  loaddone

loaderr:
    ; GLUE CODE: Print error
    lda  #'E'
    jsr  OUTCH
    lda  #'R'
    jsr  OUTCH

loaddone:
    jsr  CRLF
    jmp  CLEAR

; =============================================================================
; ROM TABLES - from romtblsf.src
; =============================================================================

dirtrk:
        .byte  18      ; directory track #
bamsiz:
        .byte  4       ; # bytes/track in bam

numsec:         ; (4) sectors/track
        .byte    17,18,19,21
nzones:
        .byte  4       ; # of zones
maxtrk:         ; maximum track # +1
trknum:         ; zone boundaries track numbers
        .byte    36,31,25,18

; =============================================================================
; VECTORS
; =============================================================================
    * = $FFFA
    .word RESET           ; NMI vector (unused, points to reset)
    .word RESET           ; RESET vector
    .word sysirq          ; IRQ vector
