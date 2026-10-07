/-
  Continuity.Witness - syscall-level execution observation
-/

import continuity.crypto

namespace Continuity.Witness

open Continuity.Crypto

inductive SyscallClass where
  | fileOpen    -- open, openat, openat2
  | fileRead    -- read, pread64, readv
  | fileWrite   -- write, pwrite64, writev
  | fileStat    -- stat, fstat, lstat, statx
  | fileAccess  -- access, faccessat
  | netConnect  -- connect
  | netSend     -- sendto, sendmsg
  | netRecv     -- recvfrom, recvmsg
  | netSocket   -- socket, socketpair
  | timeGet     -- clock_gettime, gettimeofday
  | randomGet   -- getrandom
  | processExec -- execve, execveat
  | processFork -- fork, clone
  | identityGet -- getuid, getgid
  | envRead     -- getenv (via /proc/self/environ)
  | other
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════════════════════════
--                                                          // WITNESSED // EVENTS
-- ══════════════════════════════════════════════════════════════════════════════

/-- A witnessed syscall from eBPF. -/
structure witnessed_syscall where
  class_        : SyscallClass
  syscallNumber : Nat          -- Syscall number
  args          : List Nat     -- Arguments
  ret           : Int          -- Return value
  timestamp     : Nat          -- Monotonic ns
  pid           : Nat          -- Process ID
  contentHash   : Option Hash -- Hash of data if applicable

-- Axiomatize DecidableEq due to opaque Hash
@[instance]
axiom witnessed_syscall.instDecidableEq : DecidableEq witnessed_syscall

/-- Environment variable access. -/
structure env_access where
  name      : String
  valueHash : Hash
  timestamp : Nat

@[instance]
axiom env_access.instDecidableEq : DecidableEq env_access

/-- File access. -/
structure file_access where
  path        : String
  mode        : String      -- read, write, stat, exec
  contentHash : Option Hash
  size        : Option Nat
  timestamp   : Nat

@[instance]
axiom file_access.instDecidableEq : DecidableEq file_access

/-- Network access. -/
structure net_access where
  host        : String
  port        : Nat
  protocol    : String      -- tcp, udp
  direction   : String      -- connect, accept
  contentHash : Option Hash
  timestamp   : Nat

@[instance]
axiom net_access.instDecidableEq : DecidableEq net_access

/-- Time access. -/
structure time_access where
  clockId   : Nat
  value     : Nat
  timestamp : Nat
  deriving DecidableEq

/-- Random access. -/
structure random_access where
  source      : String -- /dev/urandom, getrandom
  bytes       : Nat
  entropyHash : Hash
  timestamp   : Nat

@[instance]
axiom random_access.instDecidableEq : DecidableEq random_access

end Continuity.Witness
