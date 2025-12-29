; KIM-1 Monitor modified to run on a Commodore 1541 Disk Drive
;
; 64tass syntax
;
; Serial I/O:
; KIM-1: SAD ($1740) Port A bit 7 for RX, SBD ($1742) Port B bit 0 for TX
; 1541: VIA1 Port B ($1800) bit 2 for RX, bit 1 for TX
;
; 2025-12-28, Dave McMurtrie

.cpu "6502"

; Timing variables (KIM-1 had these at $17F2-$17F4, but that's VIA space on 1541)
; We put them in low zero page instead
* = $00
CNTL30    .byte ?         ; $00 - Baud rate constant low
CNTH30    .byte ?         ; $01 - Baud rate constant high  
TIMH      .byte ?         ; $02 - Timer high byte

; KIM-1 standard zero page locations ($F8-$FF)
* = $F8
INL       .byte ?         ; $F8 - Input buffer low
INH       .byte ?         ; $F9 - Input buffer high
POINTL    .byte ?         ; $FA - Address pointer low
POINTH    .byte ?         ; $FB - Address pointer high
TEMP      .byte ?         ; $FC - Temporary storage
TMPX      .byte ?         ; $FD - Temporary X storage
CHAR      .byte ?         ; $FE - Character buffer
MODE      .byte ?         ; $FF - Mode flag

;
; === 6522 VIA Registers ===
;
VIA1      = $1800        ; VIA1 base address (UC3 on 1541)
PORTB     = VIA1         ; Port B Data ($1800)
PORTA     = VIA1+1       ; Port A Data ($1801) - not used
DDRB      = VIA1+2       ; Port B Direction ($1802)
DDRA      = VIA1+3       ; Port A Direction ($1803) - not used

; Map KIM-1 port names to VIA addresses
; KIM-1 SAD = Port A Data (for RX bit 7)
; KIM-1 SBD = Port B Data (for TX bit 0)
; 1541: Use Port B for both RX (bit 2) and TX (bit 1)
SAD       = PORTB        ; Map SAD to VIA Port B (for RX compatibility)
SBD       = PORTB        ; Map SBD to VIA Port B (for TX compatibility)

;
; === VIA2 (Motor Control) ===
;
VIA2      = $1C00        ; VIA2 base address (UC2 on 1541)
VIA2_PORTB = VIA2        ; Port B controls motor
VIA2_DDRB  = VIA2+2      ; Port B direction
MOTOR_BIT = $04          ; Bit 2 = motor control (0=on, 1=off)

;
; === ROM CODE ===
;
* = $E000

ROM_START = *
ROM_SIZE  = $2000        ; 8K ROM

;
; === RESET Vector Entry ===
;
RESET:
    ; Disable interrupts during initialization
    sei
    
    ; Initialize stack pointer
    ldx  #$FF
    txs
    
    ; Set outputs before DDRB 
    lda  #$08             ; 00001000: bit 3=1 (CLKOUT), bit 1=0 (TX idle LOW)
    sta  VIA1 

    ; Set Port B DDR: bit 1 = output (TX), bit 2 = input (RX), bit 3 = output (CLKOUT)
    lda  #$0A             ; 00001010: bits 1,3 = output, bit 2 = input
    sta  DDRB
    
    ; Set PB4 (ATNA) as output LOW to release DATA line.
    ; This was a major pain in my ass.
    ; ATNA HIGH would activate the inverter, pulling DATA low
    ; and was preventing OUTCH from sending any TTY data out.
    ; ATNA LOW releases the open-collector output
    lda  DDRB
    ora  #$10             ; Set bit 4 as output
    sta  DDRB
    lda  PORTB
    and  #$EF             ; Clear bit 4 (set LOW)
    sta  PORTB
    
    ; Write PORTB first, then DDRB. It boggles my mind why, but when
    ; I set the data direction register first, this didn't work.
    lda  #$00             ; All bits LOW (motor off)
    sta  VIA2_PORTB       ; Set port value FIRST
    lda  #$FF             ; All bits = output
    sta  VIA2_DDRB        ; THEN set direction
    
    ; Clear interrupts and enable them now that VIA is initialized
    cli
    
    jmp  START

;
; === Interrupt Handlers ===
;
NMI_HANDLER:
    ; NMI - just ignore and return
    rti

IRQ_HANDLER:
    ; IRQ - VIA interrupts are disabled, but clear flags just in case
    lda  VIA1+$0D         ; Read IFR (Interrupt Flag Register)
    sta  VIA1+$0D         ; Write back to clear flags
    rti

;
; === START - KIM-1 Startup (from source line 145) ===
;
START:
    ; Auto-detect baud rate
    jsr  DETCPS
    
    ; Print banner (from source line 152)
    ldx  #10              ; KIM-1 line 152
    jsr  PRTST            ; Print "KIM" + CR/LF
    jmp  SHOW1            ; Show address and value

;
; === CLEAR - Clear input buffer (KIM-1 line 156) ===
;
CLEAR:
    lda  #0
    sta  INL
    sta  INH

;
; === READ - Main input loop (KIM-1 line 163) ===
;
READ:
    jsr  GETCH
    pha
    ; KIM-1 did hardware echo. We have to do software echo 
    jsr  OUTCH        ; Echo it
    pla               ; Restore for PACK
    jsr  PACK
    jmp  SCAN

;
; === SCAN - Analyze character (KIM-1 line 170) ===
;
SCAN:
    cmp  #$20             ; SPACE
    beq  SPACE
    cmp  #$7F             ; RUBOUT
    beq  START
    cmp  #$0D             ; CR
    beq  RTRN
    cmp  #$0A             ; LF
    beq  FEED
    cmp  #'.'
    beq  MODIFY
    cmp  #'G'
    beq  GOEXEC
    jmp  READ             ; Ignore illegal character

;
; === SPACE - Open new cell (KIM-1 line 200) ===
;
SPACE:
    jsr  OPEN
SHOW:
    jsr  CRLF
SHOW1:
    jsr  PRTPNT
    jsr  OUTSP
    ldy  #0
    lda  (POINTL),Y
    jsr  PRTBYT
    jsr  OUTSP
    jmp  CLEAR

;
; === RTRN - Increment to next address (KIM-1 line 218) ===
;
RTRN:
    jsr  INCPT
    jmp  SHOW

;
; === FEED - Decrement to previous address (KIM-1 line 223) ===
;
FEED:
    jsr  DECPT
    jmp  SHOW

;
; === MODIFY - Modify cell (KIM-1 line 228) ===
;
MODIFY:
    ldy  #0
    lda  INL
    sta  (POINTL),Y
    jmp  RTRN             ; Increment address and show next cell

;
; === GOEXEC - Execute program (KIM-1 line 237) ===
; Execute from currently displayed address (POINTL/POINTH)
; NOT from input buffer - user views address with SPACE, then presses G
;
GOEXEC:
    jmp  (POINTL)

;
; === OPEN - Move INL/INH to POINTL/POINTH (KIM-1 line 243) ===
;
OPEN:
    lda  INH
    sta  POINTH
    lda  INL
    sta  POINTL
    rts

;
; === INCPT - Increment pointer (KIM-1 line 251) ===
;
INCPT:
    inc  POINTL
    bne  INC1
    inc  POINTH
INC1:
    rts

;
; === DECPT - Decrement pointer (KIM-1 line 259) ===
;
DECPT:
    lda  POINTL
    bne  DEC1
    dec  POINTH
DEC1:
    dec  POINTL
    rts

;
; === DETCPS - Detect baud rate (KIM-1 DETCPS, source line 753) ===
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
; Restructured to 13-cycle loop to match DELAY's 13-cycle loop
; lda(4) + and(2) + beq(2) + inx(2) + bne(3) = 13 cycles
;
DETCPS:
    lda  #$FF
    sta  CNTH30

    ; Wait for idle (LOW on RX input)
    ; After 74LS14 inversion: idle = LOW
DET_IDLE:
    lda  SAD              ; Read Port B
    and  #$04             ; Test bit 2
    bne  DET_IDLE         ; Loop while HIGH, wait for LOW (idle)

    ; Wait for start bit (HIGH on RX input)
    ; After 74LS14 inversion: start bit = HIGH
DET1:
    lda  SAD              ; Read Port B
    and  #$04             ; Test bit 2
    beq  DET1             ; Loop while LOW, wait for HIGH (start bit)

    ; Measure start bit duration - 13 cycle loop to match DELAY
    ; Loop: lda(4) + and(2) + beq(2) + inx(2) + bne(3) = 13 cycles
    ldx  #$FC
DET2:
    lda  SAD              ; 4 cycles - Read Port B
    and  #$04             ; 2 cycles - Test bit 2
    beq  DET_END          ; 2 cycles (not taken) - Exit when LOW (end of start bit)
    inx                   ; 2 cycles
    bne  DET2             ; 3 cycles (taken)
    inc  CNTH30           ; 5 cycles (only when X wraps)
    jmp  DET2             ; 3 cycles

DET_END:
    stx  CNTL30
    ldx  #8
    jsr  GET5             ; Read rest of character
    rts

;
; === GET5 - Read 8 data bits (KIM-1 GET5, source line 860) ===
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
; Use ROR with carry to shift bit into position 7
; Invert polarity because 74LS14 inverts the input
; VIA HIGH = RS-232 LOW = 0 bit
; VIA LOW = RS-232 HIGH = 1 bit
;
GET5:
    jsr  DEHALF           ; Delay to center of first bit

GET2:
    lda  SAD              ; Read Port B
    and  #$04             ; Test bit 2 - result is $00 or $04
    sec                   ; Default: carry set (1 bit)
    beq  GET2_SHIFT       ; If zero (VIA LOW = RS-232 HIGH), keep carry set
    clc                   ; If non-zero (VIA HIGH = RS-232 LOW), clear carry (0 bit)
GET2_SHIFT:
    ror  CHAR             ; Rotate carry into bit 7, shift right
    jsr  DELAY
    dex
    bne  GET2

    jsr  DEHALF
    rts

;
; === GETCH - Get character from serial (KIM-1 GETCH, source line 842) ===
; Use VIA Port B bit 2 instead of KIM-1 6530 Port A bit 7
;
GETCH:
    stx  TMPX

    ; Wait for idle (LOW on RX)
    ; After 74LS14 inversion: idle = LOW
GET1:
    lda  SAD              ; Read Port B
    and  #$04             ; Test bit 2
    bne  GET1             ; Loop while HIGH, wait for LOW (idle)

    ; Wait for start bit (HIGH on RX)
    ; After 74LS14 inversion: start bit = HIGH
    lda  SAD
    and  #$04
    beq  GET1+2           ; Keep checking if still LOW

    ; Read 8 data bits
    ldx  #8
    jsr  DELAY
    jsr  GET5

    ldx  TMPX
    lda  CHAR
    rol                   ; Shift off stop bit
    lsr
    rts

;
; === OUTCH - Output character (KIM-1 OUTCH, source line 895) ===
; Use VIA Port B bit 1 instead of KIM-1 6530 Port B bit 0
;
OUTSP:
    lda  #' '
OUTCH:
    sta  CHAR
    stx  TMPX
    jsr  DELAY

    ; Send start bit
    ; Idle is LOW, so start bit must be HIGH (opposite of idle)
    lda  SBD              ; Read Port B
    ora  #$02             ; Set bit 1 HIGH (start bit)
    sta  SBD
    jsr  DELAY

    ; Send 8 data bits
    ; Data polarity: VIA must output OPPOSITE of desired RS-232 level
    ; because 7406 inverts. So: 1 bit is VIA LOW, 0 bit is VIA HIGH
    ldx  #8
OUT1:
    lda  SBD              ; Read Port B
    ora  #$02             ; Default bit 1 HIGH (becomes LOW after 7406 = 0 bit)
    lsr  CHAR             ; Shift byte, bit 0 into carry
    bcc  OUT1_SEND        ; If carry clear (0 bit), keep HIGH
    and  #$FD             ; If carry set (1 bit), clear to LOW (becomes HIGH after 7406)
OUT1_SEND:
    sta  SBD              ; Output the bit
    jsr  DELAY
    dex
    bne  OUT1

    ; Send stop bit
    ; Stop bit must return to idle (LOW)
    lda  SBD              ; Read Port B
    and  #$FD             ; Clear bit 1 LOW (stop bit = return to idle)
    sta  SBD
    jsr  DELAY

    ldx  TMPX
    rts

;
; === DELAY - Delay one bit time (KIM-1 DELAY, source line 921) ===
; Loop: sec(2) + sbc(2) + bcs(3) + ldy(3) + bpl(3) = 13 cycles
; Matches DETCPS's 13-cycle measurement loop
;
DELAY:
    lda  CNTH30
    sta  TIMH
    lda  CNTL30
DE2:
    sec
DE4:
    sbc  #1
    bcs  DE3
    dec  TIMH
DE3:
    ldy  TIMH
    bpl  DE2
    rts

;
; === DEHALF - Delay half bit time (KIM-1 DEHALF, source line 935) ===
; Uses DELAY's loop (DE2/DE4) with halved count
;
DEHALF:
    lda  CNTH30
    sta  TIMH
    lda  CNTL30
    lsr
    lsr  TIMH
    bcc  DE2
    ora  #$80
    bcs  DE4              ; Always branches

;
; === CRLF - Print CR and LF (KIM-1 CRLF, source line 817) ===
;
CRLF:
    ldx  #7
PRTST:
    lda  TOP,X
    jsr  OUTCH
    dex
    bpl  PRTST
    rts

;
; === PRTPNT - Print address (KIM-1 PRTPNT, source line 800) ===
;
PRTPNT:
    lda  POINTH
    jsr  PRTBYT
    lda  POINTL
PRTBYT:
    pha
    lsr
    lsr
    lsr
    lsr
    jsr  HEXTA
    pla
    and  #$0F
HEXTA:
    and  #$0F             ; Mask to 4 bits (like original KIM-1)
    cmp  #$0A
    clc
    bmi  HEXTA1
    adc  #7               ; A..F
HEXTA1:
    adc  #$30
    jmp  OUTCH

;
; === PACK - Pack hex ASCII into binary (KIM-1 PACK, source line 828) ===
;
PACK:
    cmp  #'0'
    bmi  PACK_RTS
    cmp  #'G'
    bpl  PACK_RTS
    cmp  #'A'
    bmi  PACK_NUM
    clc
    adc  #9
PACK_NUM:
    rol
    rol
    rol
    rol
    ldy  #4
PACK1:
    rol
    rol  INL
    rol  INH
    dey
    bne  PACK1
    lda  #0
PACK_RTS:
    rts

;
; === TOP - Banner text (KIM-1 TOP, source line 1111) ===
;
TOP:
    .byte 0, 0, 0, 0, 0, 0, 10, 13
    .text "MIK"

;
; === PAD TO END OF ROM ===
;
    .fill (ROM_START + ROM_SIZE - 6) - *, $FF

;
; === VECTORS ===
;
* = ROM_START + ROM_SIZE - 6

VECTORS:
    .word NMI_HANDLER     ; $FFFA - NMI vector
    .word RESET           ; $FFFC - RESET vector  
    .word IRQ_HANDLER     ; $FFFE - IRQ vector
