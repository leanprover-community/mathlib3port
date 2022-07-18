import Lake
open Lake DSL System

-- Usually the `tag` will be of the form `nightly-2021-11-22`.
-- If you would like to use an artifact from a PR build,
-- it will be of the form `pr-branchname-sha`.
def tag : String := "nightly-2022-07-18"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "mathlib3-binport.tar.gz"

def download (url : String) (to : FilePath) : BuildM PUnit := Lake.proc
{ -- We use `curl -O` to ensure we clobber any existing file.
  cmd := "curl",
  args := #["-L", "-O", url]
  cwd := to }

def untar (file : FilePath) : BuildM PUnit := Lake.proc
{ cmd := "tar",
  args := #["-xzf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
  cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit :=
download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" to

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

def fetchOleans : OpaqueTarget := { info := (), task := fetch } where
  fetch := async (m := BuildM) do
    IO.FS.createDirAll libDir
    let oldTrace := Hash.ofString tag
    buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
      untarReleaseArtifact releaseRepo tag oleanTarName libDir

  libDir : FilePath := __dir__ / "build" / "lib"

package mathlib3port where
  extraDepTarget := Target.collectOpaqueList [fetchOleans]

require lean3port from git "https://github.com/leanprover-community/lean3port.git"@"c576264a78ae54feb56d3e782c192bc05e15c47f"

@[defaultTarget]
lean_lib Mathbin where
  roots := #[]
  globs := #[`Mathbin]
