import Lake
open Lake DSL System

-- Usually the `tag` will be of the form `nightly-2021-11-22`.
-- If you would like to use an artifact from a PR build,
-- it will be of the form `pr-branchname-sha`.
def tag : String := "nightly-2024-07-19-06"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "mathlib3-binport.tar.gz"

def untar (file : FilePath) : JobM PUnit := Lake.proc
  { cmd := "tar",
    args := #["-xzf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
    cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : JobM PUnit :=
  download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" (to / artifact)

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : JobM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

package mathlib3port where
  extraDepTargets := #[`fetchOleans]

target fetchOleans (_pkg) : Unit := Job.async do
  let libDir : FilePath := __dir__ / ".lake" / "build" / "lib"
  IO.FS.createDirAll libDir
  let oldTrace := Hash.ofString tag
  let _ ← buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
    logInfo "Fetching oleans for Mathbin"
    untarReleaseArtifact releaseRepo tag oleanTarName libDir
  return ((), .nil)

require lean3port from git "https://github.com/leanprover-community/lean3port.git"@"819fa0d4fe19a13ddb719b468cfaf06cfc064a8e"

@[default_target]
lean_lib Mathbin where
  roots := #[]
  globs := #[`Mathbin]
