
/* BSED Input/Output Interface */

#define NUM_CELLS_PER_MOD 4
#define NUM_MODS_PER_PACK 4


// INPUT

typedef struct
{
    int cells[NUM_CELLS_PER_MOD];
    int status; // 0 = FLAWLESS, 1 = ERROR
} MODULE_STR;

MODULE_STR battery_modules[NUM_MODS_PER_PACK];
int bsed_emergency_stop;

/*@
    assigns \nothing;

    ensures \result == battery_modules[idx];
*/
MODULE_STR bsed_read_module(int idx)
{
    return battery_modules[idx];
}

/*@
    assigns \nothing;

    ensures \result == bsed_emergency_stop;
*/
int bsed_read_emergency_stop()
{
    return bsed_emergency_stop;
}


// OUTPUT

int bsed_max_voltages[NUM_MODS_PER_PACK];
int bsed_min_voltages[NUM_MODS_PER_PACK];
int bsed_max_voltage;
int bsed_min_voltage;
int bsed_battery_status;

/*@
    requires \separated(voltages + (0..(NUM_MODS_PER_PACK -1)), (int *)bsed_max_voltages + (0..(NUM_MODS_PER_PACK -1)));
    requires \valid(bsed_max_voltages+(0..(NUM_MODS_PER_PACK -1)));
    requires \valid(voltages+(0..(NUM_MODS_PER_PACK -1)));

    assigns bsed_max_voltages[0..(NUM_MODS_PER_PACK-1)];

    ensures bsed_max_voltages[0..(NUM_MODS_PER_PACK -1)] == voltages[0..(NUM_MODS_PER_PACK -1)];
*/
void bsed_write_max_voltages(int voltages[])
{
    /*@
        loop invariant 0 <= i <= NUM_MODS_PER_PACK;
        loop invariant 
        \forall integer j;
            0 <= j < i ==> bsed_max_voltages[j] == voltages[j];
        loop assigns i, bsed_max_voltages[0..(NUM_MODS_PER_PACK -1)];
        loop variant (NUM_MODS_PER_PACK - i);
    */    
    for(int i = 0; i < NUM_MODS_PER_PACK; i++)
    {
        bsed_max_voltages[i] = voltages[i];
    }
    return;
}

/*@
    requires \separated(voltages + (0..(NUM_MODS_PER_PACK -1)), (int *)bsed_min_voltages + (0..(NUM_MODS_PER_PACK -1)));
    requires \valid(bsed_min_voltages+(0..(NUM_MODS_PER_PACK -1)));
    requires \valid(voltages+(0..(NUM_MODS_PER_PACK -1)));

    assigns bsed_min_voltages[0..(NUM_MODS_PER_PACK -1)];

    ensures bsed_min_voltages[0..(NUM_MODS_PER_PACK -1)] == voltages[0..(NUM_MODS_PER_PACK -1)];
*/
void bsed_write_min_voltages(int voltages[])
{
    /*@
        loop invariant 0 <= i <= NUM_MODS_PER_PACK;
        loop invariant 
        \forall integer j;
            0 <= j < i ==> bsed_min_voltages[j] == voltages[j];
        loop assigns i, bsed_min_voltages[0..(NUM_MODS_PER_PACK -1)];
        loop variant (NUM_MODS_PER_PACK - i);
    */ 
    for(int i = 0; i < NUM_MODS_PER_PACK; i++)
    {
        bsed_min_voltages[i] = voltages[i];
    }
    return;
}

/*@
    assigns bsed_max_voltage;

    ensures bsed_max_voltage == voltage;
*/
void bsed_write_max_voltage(int voltage)
{
    bsed_max_voltage = voltage;
    return;
}

/*@
    assigns bsed_min_voltage;

    ensures bsed_min_voltage == voltage;
*/
void bsed_write_min_voltage(int voltage)
{
    bsed_min_voltage = voltage;
    return;
}

/*@
    assigns bsed_battery_status;

    ensures bsed_battery_status == status;
*/
void bsed_write_battery_status(int status)
{
    bsed_battery_status = status;
    return;
}

/*@
    assigns bsed_emergency_stop;

    ensures bsed_emergency_stop == status;
*/
void bsed_write_emergency_stop(int status)
{
    bsed_emergency_stop = status;
    return;
}
