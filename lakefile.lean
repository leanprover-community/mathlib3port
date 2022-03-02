import Lake
open Lake DSL System

-- Usually the `tag` will be of the form `nightly-2021-11-22`.
-- If you would like to use an artifact from a PR build,
-- it will be of the form `pr-branchname-sha`.
-- You can find the relevant SHA by inspecting the URL of the artifacts on the release page.
def tag : String := "nightly-2022-03-02"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "mathlib3-binport.tar.gz"
def leanTarName : String := "mathlib3-synport.tar.gz"

def download (url : String) (to : FilePath) : BuildM PUnit := Lake.proc
{ -- We use `curl -O` to ensure we clobber any existing file.
  cmd := "curl",
  args := #["-L", "-O", url]
  cwd := to }

def untar (file : FilePath) : BuildM PUnit := Lake.proc
{ cmd := "tar",
  args := #["-xzvf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
  cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit :=
download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" to

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

def fetchOleans (dir : FilePath) : OpaqueTarget := { info := (), task := fetch } where
  fetch := async (m := BuildM) do
    IO.FS.createDirAll libDir
    let oldTrace := Hash.ofString (← Git.headRevision dir)
    buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
      untarReleaseArtifact releaseRepo tag oleanTarName libDir

  libDir : FilePath := dir / "build" / "lib"

def fetchLeans (dir : FilePath) : OpaqueTarget := { info := (), task := fetch } where
  fetch := async (m := BuildM) do
    IO.FS.createDirAll srcDir
    let oldTrace := Hash.ofString (← Git.headRevision dir)
    buildFileUnlessUpToDate (srcDir / leanTarName) oldTrace do
      untarReleaseArtifact releaseRepo tag leanTarName srcDir

  srcDir : FilePath := dir

package mathlib3port (dir) {
  libRoots := #[]
  libGlobs := #[`Mathbin]
  extraDepTarget := Target.collectOpaqueList [fetchLeans dir, fetchOleans dir]
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "lean3port",
    src := Source.git "https://github.com/leanprover-community/lean3port.git" "a55fe81a3018ab10e3041c030ae1c81b6b243720"
  }]
}
