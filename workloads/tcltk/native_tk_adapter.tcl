#!/usr/bin/env wish
# Native presentation adapter only; semantic definitions remain in Agda.
# Contract: ACTIONS_WORKLOAD_LABEL is an externally supplied display string.

package require Tk

set workload_label "Actions native Tcl/Tk adapter"
if {[info exists ::env(ACTIONS_WORKLOAD_LABEL)] && $::env(ACTIONS_WORKLOAD_LABEL) ne ""} {
    set workload_label $::env(ACTIONS_WORKLOAD_LABEL)
}

wm title . "Actions"
ttk::label .status -text $workload_label
ttk::button .close -text "Close" -command {destroy .}
pack .status -padx 24 -pady 16
pack .close -padx 24 -pady {0 16}

proc launch_semantic_graph {launcher} {
    set tclsh [auto_execok tclsh]
    if {$tclsh eq ""} {
        tk_messageBox -icon error -title "Actions" -message "tclsh is unavailable for the Elm graph launcher."
        return
    }

    if {[catch {exec {*}$tclsh $launcher &} error_message]} {
        tk_messageBox -icon error -title "Actions" -message $error_message
    }
}

set graph_launcher [file join [file dirname [file normalize [info script]]] launch_elm_graph.tcl]

ttk::button .graph -text "Open semantic graph" -command [list launch_semantic_graph $graph_launcher]
pack .graph -padx 24 -pady {0 16}
