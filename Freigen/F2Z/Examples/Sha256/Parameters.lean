namespace Freigen.F2Z.Examples

/-- A fixed-size SHA-256 circuit for 2 KiB (2048-byte) messages. -/
def sha2562KBMessageBytes : Nat := 2048

/-- The number of message bits processed by the 2 KiB SHA-256 circuit. -/
def sha2562KBMessageBits : Nat := sha2562KBMessageBytes * 8

end Freigen.F2Z.Examples
