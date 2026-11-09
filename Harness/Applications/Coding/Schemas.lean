import Lean

/-! Provider schemas for the coding application's closed tool registry. -/
namespace Harness.Coding
open Lean

private def property (kind description : String) : Json :=
  Json.mkObj [("type", toJson kind), ("description", toJson description)]

private def tool (name description : String) (fields : List (String × Json))
    (required : List String) : Json :=
  Json.mkObj [("name", toJson name), ("description", toJson description),
    ("input_schema", Json.mkObj [("type", toJson "object"),
      ("properties", Json.mkObj fields), ("required", toJson required),
      ("additionalProperties", toJson false)])]

/-- The static coding registry. Schemas match the core decoder and IO adapters. -/
def toolSchemas : Array Json := #[
  tool "list"
    "List workspace files recursively in stable sorted traversal order. Paths are relative to the workspace; symlinks and parent traversal are rejected. Results are bounded by limit; ignored metadata directories are omitted. Inspect a subdirectory by calling list again with its path."
    [("path", property "string" "Workspace-relative directory, default '.'"),
     ("limit", property "integer" "Maximum entries, default 200")]
    [],
  tool "read"
    "Read a UTF-8 file with 1-based inclusive line bounds. The result includes the SHA256 identity of the full file; use it as expectedSha256 in a subsequent edit. Outputs are bounded and truncation is explicit. Read a later line range to retrieve omitted content."
    [("path", property "string" "Workspace-relative file path"),
     ("startLine", property "integer" "First line, default 1"),
     ("endLine", property "integer" "Last line, default 200")]
    ["path"],
  tool "search"
    "Search UTF-8 workspace files for a literal substring. Results contain paths and line numbers in stable order. Searches skip symlinks and ignored metadata directories, and stop at the configured match limit. Narrow the path or query if results are truncated."
    [("query", property "string" "Literal nonempty search string"),
     ("path", property "string" "Workspace-relative file or directory, default '.'"),
     ("limit", property "integer" "Maximum matches, default 100"),
     ("caseSensitive", property "boolean" "Case-sensitive matching, default true; false ignores ASCII letter case only")]
    ["query"],
  tool "edit"
    "Replace one exact occurrence of old with new in a workspace UTF-8 file. Read the file first and supply the returned full-file SHA256 as expectedSha256. An absent or ambiguous match or changed preimage fails without writing. Refresh the file after a stale-preimage error; edits use atomic replacement under a single-writer assumption."
    [("path", property "string" "Workspace-relative file path"),
     ("old", property "string" "Exact nonempty text to replace, must occur once"),
     ("new", property "string" "Replacement text, may be empty"),
     ("expectedSha256", property "string" "64-character SHA256 from a prior read")]
    ["path", "old", "new", "expectedSha256"],
  tool "create"
    "Create a UTF-8 file in the workspace. Existing files fail unless overwrite is explicitly true. Parent directories must already exist and may not be symlinks. Prefer edit with a preimage identity for changes to existing files."
    [("path", property "string" "Workspace-relative file path"),
     ("content", property "string" "Complete new file content"),
     ("overwrite", property "boolean" "Permit replacing an existing file, default false")]
    ["path", "content"],
  tool "artifact"
    "Retrieve a bounded byte range from a retained tool-output artifact. Use only the opaque artifact id returned by a previous tool result. Artifacts are immutable session data; this tool cannot read arbitrary paths. Continue at a later offset when content remains."
    [("id", property "string" "Opaque artifact id from a prior tool result"),
     ("offset", property "integer" "Zero-based byte offset, default 0"),
     ("length", property "integer" "Maximum bytes, default 4096, at most 65536")]
    ["id"],
  tool "process"
    "Run a program using an argument array without implicit shell expansion. Commands may require exact-action human approval. The current directory is workspace-relative; process access is governed by the session's frozen isolation profile and the operating system. Runtime deadlines and output limits apply; a nonzero exit is a completed command result, and timeout may leave side effects. Retained output artifacts can be retrieved with artifact."
    [("argv", Json.mkObj [("type", toJson "array"), ("items", property "string" "Argument"),
        ("minItems", toJson (1 : Nat)), ("description", toJson "Program followed by its arguments")]),
     ("cwd", property "string" "Workspace-relative working directory, default '.'")]
    ["argv"]]

end Harness.Coding

