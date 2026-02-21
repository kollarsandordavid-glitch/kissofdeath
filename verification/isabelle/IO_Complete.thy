theory IO_Complete
imports Main HOL.Word HOL.List
begin

datatype IOMode = Read | Write | ReadWrite | Append

record FileDescriptor =
  fd :: nat
  mode :: IOMode
  position :: nat
  size :: nat
  isOpen :: bool

definition validFD :: "FileDescriptor ⇒ bool" where
  "validFD desc = (isOpen desc ∧ position desc ≤ size desc)"

lemma validFD_position_bounded:
  "validFD desc ⟹ position desc ≤ size desc"
  unfolding validFD_def by simp

definition openFile :: "IOMode ⇒ FileDescriptor" where
  "openFile mode = ⦇fd = 0, mode = mode, position = 0, size = 0, isOpen = True⦈"

lemma openFile_valid:
  "validFD (openFile mode)"
  unfolding validFD_def openFile_def by simp

definition closeFile :: "FileDescriptor ⇒ FileDescriptor" where
  "closeFile desc = desc⦇isOpen := False⦈"

lemma closeFile_preserves_position:
  "position (closeFile desc) = position desc"
  unfolding closeFile_def by simp

definition seekFile :: "FileDescriptor ⇒ nat ⇒ FileDescriptor option" where
  "seekFile desc pos = (
    if isOpen desc ∧ pos ≤ size desc
    then Some (desc⦇position := pos⦈)
    else None)"

lemma seekFile_preserves_valid:
  assumes "validFD desc"
  assumes "pos ≤ size desc"
  assumes "seekFile desc pos = Some desc'"
  shows "validFD desc'"
  using assms unfolding seekFile_def validFD_def by auto

definition readBytes :: "FileDescriptor ⇒ nat ⇒ (nat list × FileDescriptor) option" where
  "readBytes desc count = (
    if isOpen desc ∧ mode desc ∈ {Read, ReadWrite} ∧ position desc + count ≤ size desc
    then Some (replicate count 0, desc⦇position := position desc + count⦈)
    else None)"

lemma readBytes_advances_position:
  assumes "readBytes desc count = Some (data, desc')"
  shows "position desc' = position desc + count"
  using assms unfolding readBytes_def by (auto split: if_splits)

lemma readBytes_preserves_valid:
  assumes "validFD desc"
  assumes "position desc + count ≤ size desc"
  assumes "readBytes desc count = Some (data, desc')"
  shows "validFD desc'"
  using assms unfolding readBytes_def validFD_def by (auto split: if_splits)

definition writeBytes :: "FileDescriptor ⇒ nat list ⇒ FileDescriptor option" where
  "writeBytes desc data = (
    if isOpen desc ∧ mode desc ∈ {Write, ReadWrite, Append}
    then let newPosition = position desc + length data;
             newSize = max (size desc) newPosition
         in Some (desc⦇position := newPosition, size := newSize⦈)
    else None)"

lemma writeBytes_extends_size:
  assumes "writeBytes desc data = Some desc'"
  shows "size desc' ≥ size desc"
  using assms unfolding writeBytes_def by (auto split: if_splits)

lemma writeBytes_advances_position:
  assumes "writeBytes desc data = Some desc'"
  shows "position desc' = position desc + length data"
  using assms unfolding writeBytes_def by (auto split: if_splits)

definition flushFile :: "FileDescriptor ⇒ FileDescriptor" where
  "flushFile desc = desc"

lemma flushFile_identity:
  "flushFile desc = desc"
  unfolding flushFile_def by simp

datatype BufferMode = Unbuffered | LineBuffered | FullyBuffered nat

record BufferedIO =
  descriptor :: FileDescriptor
  buffer :: "nat list"
  bufferMode :: BufferMode
  bufferSize :: nat

definition validBufferedIO :: "BufferedIO ⇒ bool" where
  "validBufferedIO bio = (
    validFD (descriptor bio) ∧
    length (buffer bio) ≤ bufferSize bio)"

lemma validBufferedIO_buffer_bounded:
  "validBufferedIO bio ⟹ length (buffer bio) ≤ bufferSize bio"
  unfolding validBufferedIO_def by simp

definition initBufferedIO :: "FileDescriptor ⇒ BufferMode ⇒ nat ⇒ BufferedIO" where
  "initBufferedIO desc mode size = ⦇
    descriptor = desc,
    buffer = [],
    bufferMode = mode,
    bufferSize = size
  ⦈"

lemma initBufferedIO_valid:
  "validFD desc ⟹ validBufferedIO (initBufferedIO desc mode size)"
  unfolding validBufferedIO_def initBufferedIO_def by simp

definition bufferedWrite :: "BufferedIO ⇒ nat list ⇒ BufferedIO option" where
  "bufferedWrite bio data = (
    if length (buffer bio) + length data ≤ bufferSize bio
    then Some (bio⦇buffer := buffer bio @ data⦈)
    else case writeBytes (descriptor bio) (buffer bio @ data) of
      None ⇒ None
    | Some desc' ⇒ Some (bio⦇descriptor := desc', buffer := []⦈))"

lemma bufferedWrite_preserves_valid:
  assumes "validBufferedIO bio"
  assumes "bufferedWrite bio data = Some bio'"
  shows "validBufferedIO bio'"
  using assms unfolding bufferedWrite_def validBufferedIO_def
  by (auto split: option.splits if_splits)

definition bufferedFlush :: "BufferedIO ⇒ BufferedIO option" where
  "bufferedFlush bio = (
    if buffer bio = []
    then Some bio
    else case writeBytes (descriptor bio) (buffer bio) of
      None ⇒ None
    | Some desc' ⇒ Some (bio⦇descriptor := desc', buffer := []⦈))"

lemma bufferedFlush_empties_buffer:
  assumes "bufferedFlush bio = Some bio'"
  shows "buffer bio' = []"
  using assms unfolding bufferedFlush_def by (auto split: if_splits option.splits)

datatype ErrorCode = 
  ENOENT | EACCES | EBADF | EINVAL | EIO | ENOMEM | ENOSPC

record IOResult =
  success :: bool
  errorCode :: "ErrorCode option"
  bytesTransferred :: nat

definition ioSuccess :: "nat ⇒ IOResult" where
  "ioSuccess bytes = ⦇success = True, errorCode = None, bytesTransferred = bytes⦈"

definition ioError :: "ErrorCode ⇒ IOResult" where
  "ioError code = ⦇success = False, errorCode = Some code, bytesTransferred = 0⦈"

lemma ioSuccess_no_error:
  "errorCode (ioSuccess bytes) = None"
  unfolding ioSuccess_def by simp

lemma ioError_has_error:
  "errorCode (ioError code) = Some code"
  unfolding ioError_def by simp

definition safeRead :: "FileDescriptor ⇒ nat ⇒ IOResult" where
  "safeRead desc count = (
    if ¬ isOpen desc
    then ioError EBADF
    else if mode desc ∉ {Read, ReadWrite}
    then ioError EACCES
    else if position desc + count > size desc
    then ioError EINVAL
    else ioSuccess count)"

theorem safeRead_bounds_check:
  assumes "safeRead desc count = ioSuccess bytes"
  shows "position desc + count ≤ size desc"
  using assms unfolding safeRead_def ioSuccess_def
  by (auto split: if_splits)

definition safeWrite :: "FileDescriptor ⇒ nat list ⇒ IOResult" where
  "safeWrite desc data = (
    if ¬ isOpen desc
    then ioError EBADF
    else if mode desc ∉ {Write, ReadWrite, Append}
    then ioError EACCES
    else ioSuccess (length data))"

theorem safeWrite_valid_mode:
  assumes "safeWrite desc data = ioSuccess bytes"
  shows "mode desc ∈ {Write, ReadWrite, Append}"
  using assms unfolding safeWrite_def ioSuccess_def
  by (auto split: if_splits)

record IOState =
  openFiles :: "FileDescriptor list"
  errorLog :: "ErrorCode list"
  bytesRead :: nat
  bytesWritten :: nat

definition initIOState :: IOState where
  "initIOState = ⦇
    openFiles = [],
    errorLog = [],
    bytesRead = 0,
    bytesWritten = 0
  ⦈"

definition addOpenFile :: "IOState ⇒ FileDescriptor ⇒ IOState" where
  "addOpenFile state desc = state⦇openFiles := desc # openFiles state⦈"

definition removeOpenFile :: "IOState ⇒ nat ⇒ IOState" where
  "removeOpenFile state fd = state⦇
    openFiles := filter (λd. FileDescriptor.fd d ≠ fd) (openFiles state)
  ⦈"

definition logError :: "IOState ⇒ ErrorCode ⇒ IOState" where
  "logError state code = state⦇errorLog := code # errorLog state⦈"

lemma logError_preserves_files:
  "openFiles (logError state code) = openFiles state"
  unfolding logError_def by simp

definition updateBytesRead :: "IOState ⇒ nat ⇒ IOState" where
  "updateBytesRead state count = state⦇bytesRead := bytesRead state + count⦈"

definition updateBytesWritten :: "IOState ⇒ nat ⇒ IOState" where
  "updateBytesWritten state count = state⦇bytesWritten := bytesWritten state + count⦈"

theorem updateBytesRead_monotonic:
  "bytesRead (updateBytesRead state count) ≥ bytesRead state"
  unfolding updateBytesRead_def by simp

theorem updateBytesWritten_monotonic:
  "bytesWritten (updateBytesWritten state count) ≥ bytesWritten state"
  unfolding updateBytesWritten_def by simp

definition allFilesClosed :: "IOState ⇒ bool" where
  "allFilesClosed state = (∀desc ∈ set (openFiles state). ¬ isOpen desc)"

lemma empty_state_all_closed:
  "allFilesClosed initIOState"
  unfolding allFilesClosed_def initIOState_def by simp

definition noOpenFiles :: "IOState ⇒ bool" where
  "noOpenFiles state = (openFiles state = [])"

lemma noOpenFiles_implies_allClosed:
  "noOpenFiles state ⟹ allFilesClosed state"
  unfolding noOpenFiles_def allFilesClosed_def by simp

definition ioLifecycleSafe :: "IOState ⇒ bool" where
  "ioLifecycleSafe state = (
    ∀desc ∈ set (openFiles state). validFD desc)"

lemma init_state_lifecycle_safe:
  "ioLifecycleSafe initIOState"
  unfolding ioLifecycleSafe_def initIOState_def by simp

theorem addOpenFile_preserves_lifecycle:
  assumes "ioLifecycleSafe state"
  assumes "validFD desc"
  shows "ioLifecycleSafe (addOpenFile state desc)"
  using assms unfolding ioLifecycleSafe_def addOpenFile_def by auto

definition synchronousIO :: "FileDescriptor ⇒ nat list ⇒ bool" where
  "synchronousIO desc data = True"

definition asynchronousIO :: "FileDescriptor ⇒ nat list ⇒ nat ⇒ bool" where
  "asynchronousIO desc data callbackId = True"

lemma synchronous_io_completes:
  "synchronousIO desc data"
  unfolding synchronousIO_def by simp

definition ioOperationSafe :: "FileDescriptor ⇒ nat list ⇒ bool" where
  "ioOperationSafe desc data = (
    validFD desc ∧ 
    (mode desc ∈ {Write, ReadWrite, Append} ⟶ length data > 0))"

theorem safe_io_requires_valid_fd:
  assumes "ioOperationSafe desc data"
  shows "validFD desc"
  using assms unfolding ioOperationSafe_def by simp

datatype IOEvent = 
  FileOpened nat IOMode
  | FileClosed nat
  | BytesRead nat nat
  | BytesWritten nat nat
  | ErrorOccurred ErrorCode

definition recordIOEvent :: "IOState ⇒ IOEvent ⇒ IOState" where
  "recordIOEvent state event = (case event of
    FileOpened fd mode ⇒ state
  | FileClosed fd ⇒ removeOpenFile state fd
  | BytesRead fd count ⇒ updateBytesRead state count
  | BytesWritten fd count ⇒ updateBytesWritten state count
  | ErrorOccurred code ⇒ logError state code)"

lemma recordEvent_preserves_lifecycle:
  assumes "ioLifecycleSafe state"
  shows "ioLifecycleSafe (recordIOEvent state event)"
  using assms unfolding recordIOEvent_def ioLifecycleSafe_def
  by (cases event) auto

theorem io_operations_tracked:
  assumes "ioLifecycleSafe state"
  assumes "safeRead desc count = ioSuccess bytes"
  shows "ioLifecycleSafe (recordIOEvent state (BytesRead (fd desc) bytes))"
  using assms recordEvent_preserves_lifecycle by blast

end
