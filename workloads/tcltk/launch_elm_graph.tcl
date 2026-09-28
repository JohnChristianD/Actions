#!/usr/bin/env tclsh
# Launch the dedicated Elm graph GUI from Tcl/Tk.
# Graph data is compiled from workloads/elm-graph/graph.dhall; no JSON
# interchange file is required.

set script_dir [file dirname [file normalize [info script]]]
set repo_root [file normalize [file join $script_dir .. ..]]
set elm_dir [file normalize [file join $script_dir .. elm-graph]]
set bundle [file join $elm_dir dist elm.js]
set html_path [file join $elm_dir index.html]

if {![file exists $bundle]} {
    set nix [auto_execok nix]
    if {$nix eq ""} {
        error "Elm graph bundle is missing and Nix is unavailable: $bundle"
    }
    set previous_dir [pwd]
    cd $repo_root
    set build_status [catch {exec {*}$nix run "${repo_root}#elm-graph-build"} build_error]
    cd $previous_dir
    if {$build_status} {
        error "Elm graph build failed: $build_error"
    }
}

if {![file exists $bundle]} {
    error "Elm graph bundle is missing after build: $bundle"
}

if {![file exists $html_path]} {
    error "Elm graph HTML shell is missing: $html_path"
}

set opener ""
foreach candidate {xdg-open gio open} {
    if {[auto_execok $candidate] ne ""} {
        set opener $candidate
        break
    }
}

if {$opener eq ""} {
    puts "Elm graph HTML: $html_path"
    exit 0
}

exec $opener $html_path &
