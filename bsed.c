/*
    This is the Battery SEnse Diagnostics.

    The following is a list of requirements it should adhere to.

    Req. 1:
    Global minimum and maximum voltages for the battery pack
    shall be calculated based on all cell voltages.
    
    Req. 2:
    If a module status is not flawless, then it should not be
    included in the min/max computation for the battery pack.

    Req. 3:
    Maximum and minimum voltages per battery module shall be
    calculated based on cell voltages within the module.
    
    Req. 4:
    If any module has a status that is not flawless, then the
    battery status should be set to error.
 */

#include <limits.h>
#include "bsed_io.c"

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))


// TYPE DEFINITIONS

typedef struct
{
    int mod_min[NUM_MODS_PER_PACK];
    int mod_max[NUM_MODS_PER_PACK];
    int batt_min;
    int batt_max;
    int status; // 0 = FLAWLESS, 1 = ERROR
    int emergency_stop;
} BATTERY_STR;


// GLOBAL VARIABLES

int battery_error_time = 0;


// FUNCTION DEFINITIONS

/*@
    requires \separated(battery_diag, (MODULE_STR *)battery_modules + (0..(NUM_MODS_PER_PACK -1)));
    requires \valid(battery_diag);

    assigns *battery_diag;

    // requirements 1 & 2 - min
    ensures requirements_1_2_min :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 0) ==> ((*battery_diag).batt_min <= (*battery_diag).mod_min[i]) );

    // requirements 1 & 2 - max
    ensures requirements_1_2_max :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 0) ==> ((*battery_diag).batt_max >= (*battery_diag).mod_max[i]) );

    // requirement 3 - min
    ensures requirement_3_min :
    \forall integer i;
        \forall integer j;
           (  (0 <= i < NUM_MODS_PER_PACK) && (0 <= j < NUM_CELLS_PER_MOD) ) ==> ((*battery_diag).mod_min[i] <= battery_modules[i].cells[j]) ;

    // requirement 3 - max
    ensures requirement_3_max :
    \forall integer i;
        \forall integer j;
            (0 <= i < NUM_MODS_PER_PACK) && (0 <= j < NUM_CELLS_PER_MOD) ==> ((*battery_diag).mod_max[i] >= battery_modules[i].cells[j]) ;

    // requirement 4
    ensures requirement_4 :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 1) ==> ((*battery_diag).status == 1) );

    // requirement module min = one of the cells in the module
    ensures min_of_mod_is_member :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> \exists integer j, (0 <= j < NUM_MODS_PER_PACK) && ((*battery_diag).mod_min[i] == battery_modules[i].cells[j]);
    
    // requirement module max = one of the cells in the module
    ensures max_of_mod_is_member :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> \exists integer j, (0 <= j < NUM_MODS_PER_PACK) && ((*battery_diag).mod_max[i] == battery_modules[i].cells[j]);

    // requirement battery min = one of the module mins if there is a flawless one, INT_MAX otherwise
    ensures min_of_battery_is_member :
            // if at least one of the module is flawless, then the battery min is the min of one module
    (\exists integer i, (0 <= i < NUM_MODS_PER_PACK) && (battery_modules[i].status == 0)) ==> (\exists integer i, (0 <= i < NUM_MODS_PER_PACK) && ((*battery_diag).batt_min == (*battery_diag).mod_min[i]))

    // requirement battery max = one of the module maxs if there is a flawless one, INT_MIN otherwise
    ensures max_of_battery_is_member :
            // if at least one of the module is flawless, then the battery max is the max of one module
    (\exists integer i, (0 <= i < NUM_MODS_PER_PACK) && (battery_modules[i].status == 0)) ==> (\exists integer i, (0 <= i < NUM_MODS_PER_PACK) && ((*battery_diag).batt_max == (*battery_diag).mod_max[i]))

*/
static void batteryMinMax(BATTERY_STR * battery_diag)
{
    MODULE_STR mod_str;
    int max_mod = INT_MIN;
    int min_mod = INT_MAX;
    int batt_status = 0;
    
    /*@
        loop invariant 0 <= idx <= NUM_MODS_PER_PACK;
        loop invariant mod_flawless :
        \forall integer i;
            0 <= i < idx ==> ( (battery_modules[i].status == 0) ==> (min_mod <= (*battery_diag).mod_min[i]) && (max_mod >= (*battery_diag).mod_max[i]) );
        loop invariant mod_min_max :
        \forall integer i;
            \forall integer j;
            ( (0 <= i < idx) && (0 <= j < NUM_CELLS_PER_MOD) ) ==> ( ((*battery_diag).mod_min[i] <= battery_modules[i].cells[j]) && ((*battery_diag).mod_max[i] >= battery_modules[i].cells[j]) );
        loop invariant
        \forall integer i;
            (0 <= i < idx) ==> ( (battery_modules[i].status == 1) ==> (batt_status == 1) );
        loop assigns idx, mod_str, max_mod, min_mod, batt_status, (*battery_diag).mod_min[0..(NUM_MODS_PER_PACK -1)], (*battery_diag).mod_max[0..(NUM_MODS_PER_PACK -1)];
        loop variant (NUM_MODS_PER_PACK - idx);
    */
    for (int idx = 0; idx < NUM_MODS_PER_PACK; idx++)
    {
        mod_str = bsed_read_module(idx);
        int min_cell = INT_MAX;
        int max_cell = INT_MIN;
        
        /*@
            loop invariant 0 <= cell_idx <= NUM_CELLS_PER_MOD;
            loop invariant current_mod_min_max :
            \forall integer j;
                0 <= j < cell_idx ==> (min_cell <= mod_str.cells[j]) && (max_cell >= mod_str.cells[j]);
            loop invariant (0 < cell_idx) ==> (\exists integer j, (0 <= j < cell_idx) && (min_cell == mod_str[1].cells[1]));
            loop invariant (0 < cell_idx) ==> (\exists integer j, (0 <= j < cell_idx) && (max_cell == mod_str.cells[j]));
            loop assigns cell_idx, min_cell, max_cell;
            loop variant (NUM_CELLS_PER_MOD - cell_idx);
        */
        for (int cell_idx = 0; cell_idx < NUM_CELLS_PER_MOD; cell_idx++)
        {
            min_cell = MIN(min_cell, mod_str.cells[cell_idx]);
            max_cell = MAX(max_cell, mod_str.cells[cell_idx]);
        }
        
        // Only count towards battery min/max if module status flawless
        if (mod_str.status == 0)
        {
            min_mod = MIN(min_mod, min_cell);
            max_mod = MAX(max_mod, max_cell);
        }
        
        if (mod_str.status == 1)
        {
            batt_status = 1;
        }
        
        // Store module diagnostics
        battery_diag->mod_min[idx] = min_cell;
        battery_diag->mod_max[idx] = max_cell;
    }
    
    // Store battery diagnostics
    battery_diag->batt_min = min_mod;
    battery_diag->batt_max = max_mod;
    battery_diag->status = batt_status;
}

/*@
    requires \separated(&battery_error_time, &battery_diag->emergency_stop);
    requires \separated(battery_diag, &battery_error_time);
    requires \valid(battery_diag);
    requires \valid(&battery_error_time);

    assigns battery_error_time, (*battery_diag).emergency_stop;
    
    behavior flawless:
        assumes (*battery_diag).status == 0;

        assigns battery_error_time;

        ensures case_flawless: battery_error_time == 0;
    
    behavior error:
        assumes (*battery_diag).status != 0;

        assigns battery_error_time, (*battery_diag).emergency_stop;

        ensures case_error_no_stop : (\at(battery_error_time, Pre) + 10 <= 100 ==> battery_error_time == \at(battery_error_time, Pre) + 10);
        ensures case_error_time_100 : (\at(battery_error_time, Pre) + 10 > 100 ==> battery_error_time == 100);
        ensures case_error_stop : (battery_error_time > 100 ==> (*battery_diag).emergency_stop == 1);    
*/
static void batteryStatus(BATTERY_STR * battery_diag)
{
    if (battery_diag->status == 0) {
        battery_error_time = 0;
    } else {
        battery_error_time = MIN(battery_error_time+10, 100);
    }

    // Check whether emergency stop shall be activated
    if (battery_error_time >= 100)
    {
        battery_diag->emergency_stop = 1;
    }
}

/**
    Module entry point function.
 */
/*@
    requires \valid(&battery_error_time);
    
    assigns bsed_emergency_stop, battery_error_time, bsed_min_voltage, bsed_max_voltage, bsed_battery_status, bsed_max_voltages[0..(NUM_MODS_PER_PACK -1)], bsed_min_voltages[0..(NUM_MODS_PER_PACK -1)];

    // requirements 1 & 2 - min
    ensures bsed_requirements_1_2_min :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 0) ==> (bsed_min_voltage <= bsed_min_voltages[i]) );

    // requirements 1 & 2 - max
    ensures bsed_requirements_1_2_max :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 0) ==> (bsed_max_voltage >= bsed_max_voltages[i]) );

    // requirement 3 - min
    ensures bsed_requirement_3_min :
    \forall integer i;
        \forall integer j;
           ( (0 <= i < NUM_MODS_PER_PACK) && (0 <= j < NUM_CELLS_PER_MOD) ) ==> (bsed_min_voltages[i] <= battery_modules[i].cells[j]) ;

    // requirement 3 - max
    ensures bsed_requirement_3_max :
    \forall integer i;
        \forall integer j;
            ( (0 <= i < NUM_MODS_PER_PACK) && (0 <= j < NUM_CELLS_PER_MOD) ) ==> (bsed_max_voltages[i] >= battery_modules[i].cells[j]) ;

    // requirement 4
    ensures bsed_requirement_4 :
    \forall integer i;
        (0 <= i < NUM_MODS_PER_PACK) ==> ( (battery_modules[i].status == 1) ==> (bsed_battery_status == 1) );

*/
void bsed()
{
    /* Structure for storing working data. */
    BATTERY_STR battery_diagnostics;
    
    /* Input */
    battery_diagnostics.emergency_stop = bsed_read_emergency_stop();
    // Battery module inputs are read in batteryMinMax.
    
    /* Calculate min/max voltages */
    batteryMinMax(&battery_diagnostics);
    
    /* Error handling */
    batteryStatus(&battery_diagnostics);
    
    /* Output */
    bsed_write_max_voltages(battery_diagnostics.mod_max);
    bsed_write_min_voltages(battery_diagnostics.mod_min);
    bsed_write_max_voltage(battery_diagnostics.batt_max);
    bsed_write_min_voltage(battery_diagnostics.batt_min);
    bsed_write_battery_status(battery_diagnostics.status);
    bsed_write_emergency_stop(battery_diagnostics.emergency_stop);
}
