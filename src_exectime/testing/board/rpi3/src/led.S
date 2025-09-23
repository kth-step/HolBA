/*

 -> taken fram the led01 example of https://github.com/adamransom/bare_metal
 -> ... and adapted

@;
@; This turns on the ACT LED for the Raspberry Pi 3 Model B v1.2
@;
@; The ACT LED is no longer wired directly to a GPIO pin and now belongs on
@; the GPIO expander, which is controlled by the GPU. In order to communicate
@; with the GPIO expander, we need to use the GPU's mailbox interface (in
@; particular, we need to send a message to the property tag channel).
@;
@; Mailbox base address: 0x3f00b880
@; Mailbox 1 write address: [0x3f00b880, #0x20]
@; Property tag channel: 8
@; Property tag ID: 0x00038041 (SET_GPIO_STATE)
@; Property tag message: 130 1 (ACT_LED pin number followed by state)
@;
*/

.globl _set_led// @; Make _set_led available to the outside world

.section .data
.align 4// @; This ensures lowest 4 bits are 0 for the following label
PropertyInfo:
//  @; = Message Header =
  .int PropertyInfoEnd - PropertyInfo// @; Calculate buffer size
  .int 0// @; Request code: Process Request
//  @; = Tag Header =
  .int 0x00038041// @; Tag ID (SET_GPIO_STATE)
  .int 8// @; Value buffer size
  .int 0// @; Request/response size
//  @; = Tag Value Buffer =
  .int 130// @; ACT_LED pin number
  .int 1// @; Turn it on
  .int 0// @; End tag
PropertyInfoEnd:

.section .text
_set_led:
// first: sanitize argument and write to message buffer in memory
  argument .req w0
  message .req x1
  ldr message, =PropertyInfo
  cbz argument, arg_ok
  mov argument, #1
arg_ok:
  str argument, [message, #24]
  .unreq argument
  .unreq message


// then: wait until the mailbox has space
  mailbox .req x0// @; Alias mailbox to r0
  ldr mailbox, =0x3f00b880// @; Load the mailbox's base address into r0

  wait1$:
    status .req x1// @; Alias status to r1
    ldr status, [mailbox, #0x18]// @; Load the Mailbox 0 status address
    tst status, #0x80000000// @; Check the status against the FULL bit
    .unreq status// @; Unset the alias
    bne wait1$// @; Keep checking the mailbox until it isn't full

// finally: send message and return
  message .req x1// @; Alias message to r1
  ldr message, =PropertyInfo// @; Load r1 with address of our message buffer
  add message, message, #8// @; Put the channel in the last 4 bits
  str message, [mailbox, #0x20]// @; Put the message in the mailbox
  .unreq message// @; Unset the alias
  .unreq mailbox

  ret // return from the led setting function

//  hang:
//    b hang// @; Give the CPU something to do ad infinitum
