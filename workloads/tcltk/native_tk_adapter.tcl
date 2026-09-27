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
