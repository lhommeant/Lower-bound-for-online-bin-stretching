#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bin_stretching_v3.h"

#ifndef NDEBUG
#define DEBUG_PRINT(...) printf(__VA_ARGS__)
#else 
#define DEBUG_PRINT(...) do {} while(0)
#endif

/* PARAMETERS */

int PROBING_LENGTH = 4; // Number of tries to find an element in the hash table. Bigger = more compact hash table = more slowdowns
int HASH_TABLE_SIZE = 100000000; // Size of the has table containing configurations
unsigned long NODES_BETWEEN_PRINTS = 100000; // Frequency of the prints during the search

/* END OF PARAMETERS */

// Global Variables
int VISUALIZE_PROPAG = 0;
int DRAW_PROPAG_BEFORE = 1;
int WRITE_GRAPH = 0;
int DRAW_GRAPH = 0;
int PRINT_TREE_TERMINAL = 0;

int NB_BINS = 0;
int CAP;
int TARGET;
int BMIN;
int *CAPS;
int *HASHED_VALUE;
int *SOLVER_TMP_MEM;

int BEST_DEPTH_REACHED;
int BEST_NORM_REACHED;

long int NODES_VISITED;

unsigned long NUMBER_ELEMENTS_HASHED = 0;
unsigned long HASH_FAILS = 0;
unsigned long SUCCESSFUL_LOOKUPS = 0;
unsigned long TRIVIAL_ELIMINATIONS = 0;
unsigned long SUCCESSFUL_ELIMINATIONS = 0;
unsigned long TRIVIAL_ADV_WINS = 0;

unsigned long DELTA_HASHED = 0;
unsigned long DELTA_FAILS = 0;
unsigned long DELTA_SUCCESSES = 0;
unsigned long DELTA_SUCCESSFUL_ELIMINATIONS = 0;
unsigned long DELTA_TRIVIAL_ELIMINATIONS = 0;
unsigned long DELTA_TRIVIAL_ADV_WINS = 0;

uint64_t **ZOBRIST_LOADS;
uint64_t **ZOBRIST_INSTANCES;

int OPTIMAL_PACKING_ID;

int ***BOUNDED_PACKINGS_NUMBER; 

int **BOOL_REACHABLE_PACKINGS;
int ***REACHABLE_PACKINGS;


int *PACKINGS_LOWER_BOUNDS; // For each possible packing, this contains the smallest item that must be send to have a chance to prove the bound
// If it contains -1 then the packing is always winning for the algo

uint64_t **NTM; /* NTM[T][M] contains the number of different bin packings bounded (strictly) by T over M bins. 
 * T <= TARGET, M<=NB_BINS
 */









/*
 * Compute LB for the bin-stretching problem by solving a 2-players game tree
 * Author: Antoine Lhomme
 */


/* 
 * Free memory of a tree
 */
void free_tree(struct tree_node *tree) {
    if (tree) {
        for (int i=0; i<tree->nb_children; i++) {
            free_tree(tree->children[i]);
        }
    }
    free(tree->packings);
    if (tree->nb_children > 0) {
        free(tree->children);
    }
    free(tree);
}

/*
 * Debug function
 */
void print_table(int nb_elems, int *table) {
    for (int i=0; i<nb_elems; i++) {
        printf("%i ", table[i]);
    }
    printf("\n");
}


/* Compute a value bmin such that if a packing has all bins but at most one
 * filled with weight >= bmin, then there exists an algorithm such that
 * the value target is never reached
 */
int compute_forbidden_orthant(int m, int c, int t) {
    return (int) ((m*c-t)/(m-1))+1;
}

/* Prints a packing of the bins */
void print_packings(int *packings, int nb_obj){
    for (int b=0; b<NB_BINS; b++) {
        printf("%i ", packings[b]);
    }
    printf(" (%i obj)", nb_obj);
}

// SOLVER

void clean_bool_table(int nb_packings, int *bool_table, int **reached_packings) {
    for (int packing_id = 0; packing_id < nb_packings; packing_id++) {
        int id = reached_packings[packing_id][NB_BINS];
        bool_table[id] = 0;
    }
}


void compute_bounded_packings_number() {
    int max_norm = NB_BINS * CAP;
    BOUNDED_PACKINGS_NUMBER = malloc(sizeof(int**) * NB_BINS);
    for (int bin = 0; bin<NB_BINS; bin++) {
        BOUNDED_PACKINGS_NUMBER[bin] = malloc(sizeof(int*) * (max_norm+1));
        for (int norm = 0; norm<=max_norm; norm++) {
            BOUNDED_PACKINGS_NUMBER[bin][norm] = malloc(sizeof(int) * (CAP+1));
            for (int bound = 0; bound<=CAP; bound++) {
                if (bin == 0) {
                    if (bound>=norm) {
                        BOUNDED_PACKINGS_NUMBER[bin][norm][bound] = 1;
                    } else {
                        BOUNDED_PACKINGS_NUMBER[bin][norm][bound] = 0;
                    }
                } else {
                    int sum = 0;
                    for (int item = 1; item<=bound && item<norm; item++) {
                        sum = sum + BOUNDED_PACKINGS_NUMBER[bin-1][norm-item][item];
                    }
                    BOUNDED_PACKINGS_NUMBER[bin][norm][bound] = sum;  
                }
            }
        }
    }
}

int get_bounded_packing_number(int *packing, int norm) {
    int s = 0;
    int k = 0; // packing[0] ... [k-1] are not 0, and k = NB_BINS or packing[k] = 0
    while (k<NB_BINS && packing[k]!=0) {
        k++;
    }
    // f1 
    for (int bin = k; bin<NB_BINS; bin++) {
        s = s + BOUNDED_PACKINGS_NUMBER[bin][norm][CAP];
    }
    // f2
    int leftover_sum = norm;
    for (int i = 0; i<k-1 ; i++) {
        s = s + BOUNDED_PACKINGS_NUMBER[k-i-1][leftover_sum][packing[i]-1];
        leftover_sum = leftover_sum - packing[i];
    }
    return s;
}

/* Solver step, return maximum size that can be given*/
int compute_new_reachable_packings(int new_object,
                                    int nb_old_reachable_packings,
                                    int old_norm,
                                    int *nb_new_reachable_packings,
                                    int *bool_table_new_reachable_packings,
                                    int **old_reachable_packings,
                                    int **new_reachable_packings) {
    
    int new_norm = old_norm + new_object;
    int biggest_item = 0;
    for (int packing_number = 0; packing_number<nb_old_reachable_packings; packing_number++) {
        int *packing = old_reachable_packings[packing_number];
        for (int bin = 0; bin<NB_BINS; bin++) {
            SOLVER_TMP_MEM[bin] = packing[bin];
        }
        int last_bin_value = -1;
        int new_bin_value;
        int switch_bin;
        int space_left;
        for (int bin = 0; bin<NB_BINS; bin++) {
            if (SOLVER_TMP_MEM[bin] != last_bin_value && SOLVER_TMP_MEM[bin] + new_object <= CAP) {
                last_bin_value = SOLVER_TMP_MEM[bin];
                new_bin_value = SOLVER_TMP_MEM[bin]+new_object;

                // Add item to the bin
                switch_bin = bin-1;
                SOLVER_TMP_MEM[bin] = new_bin_value;
                while (switch_bin>=0 && SOLVER_TMP_MEM[switch_bin]<new_bin_value){
                    SOLVER_TMP_MEM[switch_bin+1] = SOLVER_TMP_MEM[switch_bin];
                    SOLVER_TMP_MEM[switch_bin] = new_bin_value;
                    switch_bin--;
                }
                switch_bin++;

                // Compute new obtained packing id
                int new_id = get_bounded_packing_number(SOLVER_TMP_MEM, new_norm);
                if (bool_table_new_reachable_packings[new_id] == 0) {
                    bool_table_new_reachable_packings[new_id] = 1;
                    int *new_packing_position = new_reachable_packings[*nb_new_reachable_packings];
                    for (int copy_bin = 0; copy_bin <NB_BINS; copy_bin++) {
                        new_packing_position[copy_bin] = SOLVER_TMP_MEM[copy_bin];
                    }
                    new_packing_position[NB_BINS] = new_id;
                    *nb_new_reachable_packings = *nb_new_reachable_packings + 1;
                    space_left = CAP - SOLVER_TMP_MEM[NB_BINS-1];
                    if (space_left > biggest_item) {
                        biggest_item = space_left;
                        OPTIMAL_PACKING_ID = *nb_new_reachable_packings - 1;
                    }
                    biggest_item = biggest_item > space_left ? biggest_item : space_left;
                }
                
                // We remove the item from the bin
                while(switch_bin<bin) {
                    SOLVER_TMP_MEM[switch_bin] = SOLVER_TMP_MEM[switch_bin+1];
                    switch_bin++;
                }
                SOLVER_TMP_MEM[bin] = last_bin_value;
            }
        }
    }
    clean_bool_table(*nb_new_reachable_packings, bool_table_new_reachable_packings, new_reachable_packings);

    return biggest_item;
}


void init_solver() {
    compute_bounded_packings_number();
    SOLVER_TMP_MEM = malloc(sizeof(int) * NB_BINS);; 
    int max_norm = (CAP * NB_BINS);
    BOOL_REACHABLE_PACKINGS = malloc(sizeof(int *) * (max_norm+1));
    BOOL_REACHABLE_PACKINGS[0] = malloc(sizeof(int) * 1); //Only 1 packing of norm 0;
    BOOL_REACHABLE_PACKINGS[0][0] = 1;

    for (int norm = 1; norm<=max_norm; norm++) {
        int nb_packings = 0;
        for (int bins = 0; bins<NB_BINS; bins++) {
            nb_packings = nb_packings + BOUNDED_PACKINGS_NUMBER[bins][norm][CAP];
        }
        BOOL_REACHABLE_PACKINGS[norm] = calloc(nb_packings, sizeof(int));
    }
    REACHABLE_PACKINGS = malloc(sizeof(int**) * (max_norm+1));
    REACHABLE_PACKINGS[0] = malloc(sizeof(int*) * 1); // Only 1 packing of norm 0;
    REACHABLE_PACKINGS[0][0] = malloc(sizeof(int) * (NB_BINS + 1));
    for (int b = 0; b<=NB_BINS; b++) {
        REACHABLE_PACKINGS[0][0][b] = 0;
    }
    for (int norm = 1; norm<=max_norm; norm++) {
        int nb_packings = 0;
        for (int bins = 0; bins<NB_BINS; bins++) {
            nb_packings = nb_packings + BOUNDED_PACKINGS_NUMBER[bins][norm][CAP];
        }
        REACHABLE_PACKINGS[norm] = malloc(sizeof(int*) * nb_packings);
        for (int packing_id = 0; packing_id<nb_packings; packing_id++) {
            REACHABLE_PACKINGS[norm][packing_id] = malloc(sizeof(int) * (NB_BINS+1));
        }
    }
}
// END SOLVER

/* Recursively prints a proof tree */
void print_tree_rec(struct tree_node *tree, int nb_obj) {
    printf("Node packings : ");
    print_packings(tree->packings, nb_obj);
    if (tree->nb_children == -1) {
        printf("\nNode result stored in hash table, next children unknown");
    }
    printf("\nNext object: %i\n", tree->next_item);

    for (int child=0; child<tree->nb_children; child++) {
        print_tree_rec(tree->children[child], nb_obj+1);
    }
}

/* Prints a proof tree */
void print_tree(struct tree_node *tree) {
    print_tree_rec(tree, 0);
}

/* Generate a random bitstring of 64 bits */
uint64_t rand_uint64(void) {
  uint64_t r = 0;
  for (int i=0; i<64; i += 15 /*30*/) {
    r = r*((uint64_t)RAND_MAX + 1) + rand();
  }
  return r;
}

/* Compute the has of a configuration for debugging purposes */
uint64_t compute_hash(int *packings, int *objects) {
    uint64_t h = 0;
    for (int b=0; b<NB_BINS; b++) {
        h ^= ZOBRIST_LOADS[b][packings[b]];
    }
    for (int i=0; i<CAP+1; i++) {
        h ^= ZOBRIST_INSTANCES[i][objects[i]];
    }
    return h;
}

/* 
 * Construct a table containing random bits for bin configurations
 */
uint64_t **zobrist_hash_init_loads() {
    uint64_t **hash_loads = malloc(sizeof(uint64_t*) * NB_BINS);
    for (int b=0; b<NB_BINS; b++) {
        hash_loads[b] = malloc(sizeof(uint64_t) * TARGET);
        for (int load = 0; load<TARGET; load++) {
            hash_loads[b][load] = rand_uint64();
        }
    }
    return hash_loads;
}

/* 
 * Construct a table containing random bits for b.s. instances
 */
uint64_t **zobrist_hash_init_instances() {
    uint64_t **hash_instance = malloc(sizeof(uint64_t*) * (CAP+1));
    for (int i=0; i<=CAP; i++) {
        hash_instance[i] = malloc(sizeof(uint64_t) * (NB_BINS * CAP + 1));
        for (int f = 0; f<=NB_BINS * CAP; f++) {
            hash_instance[i][f] = rand_uint64();
        }
    }
    return hash_instance;
}

/* Return 1 if the 2 configurations (packing, instance) are the same, 0 otherwise */
int same_config(int *bin_config1, int *instance1, int *bin_config2, int *instance2) {
    for (int b=0; b<NB_BINS; b++) {
        if (bin_config1[b] != bin_config2[b]) {
            return 0;
        }
    }
    for (int i=0; i<CAP; i++) {
        if (instance1[i] != instance2[i]) {
            return 0;
        }
    }
    return 1;
}


/*
 * Given a configuration (packing, instance) we check if we already computed if it's winning or not.
 * Return -1 if the configuration is not in the hash_table, 0 if algorithm wins, next item weight otherwise.
 */
int hash_table_check(uint64_t key, int *bin_config, int *instance, struct hash_table_element* hash_table) {
    uint64_t real_key = key%HASH_TABLE_SIZE;
    for (int i=0; i<PROBING_LENGTH; i++) {
        if (!hash_table[real_key+i].bin_config) {
            // Configuration is not in the hash_table
            return -1;
        }
        if (hash_table[real_key+i].key == key &&
         same_config(bin_config, instance, hash_table[real_key+i].bin_config, hash_table[real_key+i].instance)==1) {
            // We found the configuration in the hash_table
            SUCCESSFUL_LOOKUPS++;
            return hash_table[real_key+i].winning;
        }
    }
    // We couldn't find the configuration in the hast_table
    return -1;
}

/* Write a configuration in the hash table */
void write_hash_table(uint64_t key, int *bin_config, int *instance, int winning, uint64_t pos, struct hash_table_element *hash_table) {
    hash_table[pos].winning = winning;
    hash_table[pos].key = key;
    for (int b=0; b<NB_BINS; b++) {
        (hash_table[pos].bin_config)[b] = bin_config[b];
    }
    for (int i=0; i<=CAP; i++) {
        (hash_table[pos].instance)[i] = instance[i];
    }
}

/* Insert a configuration in the hash table */
void insert_hash_table(uint64_t key, int *bin_config, int *instance, struct hash_table_element* hash_table, int winning) {
    uint64_t real_key = key%HASH_TABLE_SIZE;
    for (int i=0; i<PROBING_LENGTH; i++) {
        DEBUG_PRINT("Insertion %i, key %lu\n", i, key);
        if (!hash_table[real_key+i].bin_config) {
            // free spot in the hash table
            hash_table[real_key+i].bin_config = malloc(sizeof(int)*NB_BINS);
            hash_table[real_key+i].instance = calloc(CAP+1, sizeof(int));
            write_hash_table(key, bin_config, instance, winning, real_key+i, hash_table);
            NUMBER_ELEMENTS_HASHED++;
            return;
        }
    }
    // No free spots in the hash table
    HASH_FAILS++;
}

void change_hash_table_value(uint64_t key, int *bin_config, int *instance, struct hash_table_element* hash_table, int new_value) {
    uint64_t real_key = key%HASH_TABLE_SIZE;
    for (int i=0; i<PROBING_LENGTH; i++) {
        if (!hash_table[real_key+i].bin_config) {
            // Configuration is not in the hash_table
            return;
        }
        if (hash_table[real_key+i].key == key &&
         same_config(bin_config, instance, hash_table[real_key+i].bin_config, hash_table[real_key+i].instance)==1) {
            // We found the configuration in the hash_table
            hash_table[real_key+i].winning = new_value;
            return;
        }
    }
    // We couldn't find the configuration in the hast_table
    return;
}

/* Removes an element from the hash table */
void remove_hashed_element(uint64_t key, int *bin_config, int *instance, struct hash_table_element* hash_table) {
    uint64_t real_key = key%HASH_TABLE_SIZE;
    for (int i=0; i<PROBING_LENGTH; i++) {
        if (hash_table[real_key+i].bin_config && hash_table[real_key+i].key == key &&
         same_config(bin_config, instance, hash_table[real_key+i].bin_config, hash_table[real_key+i].instance)==1) {
            // We found the configuration in the hash_table
            hash_table[real_key+i].key = 0;
            return; 
        }
    }
    // We couldn't find the configuration in the hash_table
    return;
}

/* Prints all elements from the hash_table */
void print_hash_table(struct hash_table_element *hash_table) {
    for (int i=0; i<HASH_TABLE_SIZE+PROBING_LENGTH; i++) {
        if (hash_table[i].bin_config) {
            DEBUG_PRINT("key %lu corresponds to config (value %i):\n", hash_table[i].key, hash_table[i].winning);
            DEBUG_PRINT("Bin config: ");
            print_table(NB_BINS, hash_table[i].bin_config);
            DEBUG_PRINT("Instance: ");
            print_table(CAP+1, hash_table[i].instance);
        }
    }
}

/* Get the index of a packing */
int packings_index(int *b) {
    int s = 0;
    for (int bin = 0; bin < NB_BINS; bin++) {
        s = s + NTM[b[bin]][NB_BINS-bin];
    }
    return s;
}


/*
 * Return NULL if the given configuration is winning for the algorithm, a tree otherwise
 */
struct tree_node *algorithm_to_play(int nb_objects_given,
                        int total_weight,
                        int new_object,
                        int previous_maximal_weight,
                        int nb_reachable_packings,
                        uint64_t previous_hash,
                        int *objects,
                        int *object_seq,
                        int *packings,
                        struct hash_table_element *hash_table) {

    // To break symmetries we want to have a packing in decreasing order,
    // and it's pointless to check the addition of the item to bins with similar
    // weight (one is enough).
#ifndef NDEBUG
    DEBUG_PRINT("--------------------\n");
    DEBUG_PRINT("ALGTP: nbo: %i tw: %i no: %i ph: %lu\n", nb_objects_given, total_weight, new_object, previous_hash);
    DEBUG_PRINT("Objects: ");
    print_table(CAP+1, objects);
    DEBUG_PRINT("Obj seq: ");
    print_table(nb_objects_given, object_seq);
    DEBUG_PRINT("packings: ");
    print_table(NB_BINS, packings);
    DEBUG_PRINT("Hash table:\n");
    //print_hash_table(hash_table);
#endif
    int last_bin_value = -1;
    int new_bin_value;
    int switch_bin;
    uint64_t new_hash;
    int hash_table_result;
    int min_send;
    struct tree_node *res;
    struct tree_node *tree = malloc(sizeof(struct tree_node));
    int hashed_value_offset = (total_weight + new_object) * NB_BINS;

    tree->children = malloc(sizeof(struct tree_node *) * NB_BINS);
    tree->hash = previous_hash;
    tree->nb_children = 0;
    

    
    previous_hash ^= ZOBRIST_INSTANCES[new_object][objects[new_object]];
    previous_hash ^= ZOBRIST_INSTANCES[new_object][objects[new_object] + 1];

    object_seq[nb_objects_given] = new_object;
    objects[new_object]++;

    // First, we test if there is a bin such that placing the new object there results in a trivial
    // algorithm win - if none exists, then we will have to explore recursively the tree
    for (int bin=0; bin<NB_BINS; bin++) {
        HASHED_VALUE[hashed_value_offset + bin] = -1;
        if (packings[bin]+new_object<TARGET) {
            // We can fit the object in this bin without reaching TARGET
            if (packings[bin] != last_bin_value) {
                // We avoided trivial symmetries
                // We add the item to the bin
                last_bin_value = packings[bin];
                new_bin_value = packings[bin]+new_object;
                // The new hash value is the previous one XOR some stuff
                new_hash = previous_hash;
                // We want to keep packings in decreasing order, so we have to switch the order of some bins
                switch_bin = bin-1;
                packings[bin] = new_bin_value;
                while (switch_bin>=0 && packings[switch_bin]<new_bin_value){
                    new_hash ^= ZOBRIST_LOADS[switch_bin][packings[switch_bin]];
                    packings[switch_bin+1] = packings[switch_bin];
                    packings[switch_bin] = new_bin_value;
                    new_hash ^= ZOBRIST_LOADS[switch_bin+1][packings[switch_bin+1]];
                    switch_bin--;
                }
                switch_bin++;
                new_hash ^= ZOBRIST_LOADS[switch_bin][new_bin_value];
                new_hash ^= ZOBRIST_LOADS[bin][last_bin_value];

                // We first check if we can eliminate this configuration with packings infos
                // This prevents filling the hash table with redundant info
                min_send = PACKINGS_LOWER_BOUNDS[packings_index(packings)];
                if (min_send > previous_maximal_weight) {
                    // Configuration is alg-winning, no need to add the result to the hash_table
                    SUCCESSFUL_ELIMINATIONS++;
                    TRIVIAL_ELIMINATIONS++;
                    objects[new_object]--;
                    while(switch_bin<bin) {
                        packings[switch_bin] = packings[switch_bin+1];
                        switch_bin++;
                    }
                    packings[bin] = last_bin_value;
                    // We need to free the tree
                    for (int child=0; child<tree->nb_children; child++) {
                        free_tree(tree->children[child]);
                    }
                    free(tree->children);
                    free(tree);
                    return NULL;
                }

                if (min_send == -1) { // Packing is green (adv-winning)
                    HASHED_VALUE[hashed_value_offset + bin] = -2; // HASHED_VALUE = -2 if the packing is green
                } else {
                    // We can now check if we stored this configuration in the hash table
                    DEBUG_PRINT("Checking hash table\n");
                    hash_table_result = hash_table_check(new_hash, packings, objects, hash_table);
                    HASHED_VALUE[hashed_value_offset + bin] = hash_table_result;
                    if (hash_table_result == 0) {
                        DEBUG_PRINT("Config is algo-winning according to hash table\n");
                        // There is an algorithm that wins according to the hash_table
                        // We need to free the tree
                        for (int child=0; child<tree->nb_children; child++) {
                            free_tree(tree->children[child]);
                        }
                        free(tree->children);
                        free(tree);
                        // We remove the item from the bin
                        objects[new_object]--;
                        while(switch_bin<bin) {
                            packings[switch_bin] = packings[switch_bin+1];
                            switch_bin++;
                        }
                        packings[bin] = last_bin_value;
                        return NULL;
                    }
                }
                // We remove the item from the bin
                while(switch_bin<bin) {
                    packings[switch_bin] = packings[switch_bin+1];
                    switch_bin++;
                }
                packings[bin] = last_bin_value;
            }
        }
    }
    DEBUG_PRINT("We need to explore the tree recursively\n");
    // Now we know that we can't avoid exploring the tree recursively
    last_bin_value = -1;
    for (int bin=0; bin<NB_BINS; bin++) {
        if (packings[bin]+new_object<TARGET) {
            // We can fit the object in this bin without reaching TARGET
            if (packings[bin] != last_bin_value) {
#ifndef NDEBUG
                DEBUG_PRINT("Trying to put object %i in bin %i from config ", new_object, bin);
                print_table(NB_BINS, packings);
                DEBUG_PRINT("of depth %i with objects ", nb_objects_given);
                print_table(CAP+1, objects);
#endif
                // We avoided trivial symmetries
                // We add the item to the bin
                last_bin_value = packings[bin];
                new_bin_value = packings[bin]+new_object;
                // The new hash value is the previous one XOR some stuff
                new_hash = previous_hash;
                // We want to keep packings in decreasing order, so we have to switch the order of some bins
                switch_bin = bin-1;
                packings[bin] = new_bin_value;
                while (switch_bin>=0 && packings[switch_bin]<new_bin_value){
                    new_hash ^= ZOBRIST_LOADS[switch_bin][packings[switch_bin]];
                    packings[switch_bin+1] = packings[switch_bin];
                    packings[switch_bin] = new_bin_value;
                    new_hash ^= ZOBRIST_LOADS[switch_bin+1][packings[switch_bin+1]];
                    switch_bin--;
                }
                switch_bin++;
                new_hash ^= ZOBRIST_LOADS[switch_bin][new_bin_value];
                new_hash ^= ZOBRIST_LOADS[bin][last_bin_value];

                DEBUG_PRINT("Checking hash table\n");
                hash_table_result = HASHED_VALUE[hashed_value_offset + bin];
                if (hash_table_result<=-1) {
                    DEBUG_PRINT("Config not in hashtable\n");
                    // We don't have this configuration in the hash table
                    // Maybe this configuration is winning in a trivial way for the adversary
                    if (hash_table_result == -2) { // Configuration is a green packing
                        TRIVIAL_ADV_WINS++;
                        SUCCESSFUL_ELIMINATIONS++;
                        // We add a special node
                        struct tree_node* child_tree = malloc(sizeof(struct tree_node));
                        child_tree->packings = malloc(sizeof(int) * NB_BINS);
                        for (int bb=0; bb<NB_BINS; bb++) {
                            child_tree->packings[bb] = packings[bb];
                        }
                        child_tree->next_item = 0; // Trees with 0 as next_item corresponds to green packings
                        child_tree->nb_children = 0;
                        child_tree->hash = new_hash;
                        tree->children[tree->nb_children] = child_tree;
                        tree->nb_children++;
                        // We remove the item from the bin
                        while(switch_bin<bin) {
                            packings[switch_bin] = packings[switch_bin+1];
                            switch_bin++;
                        }
                        packings[bin] = last_bin_value;
                    } else { // Configuration isn't a green packing and isn't in the hash table, so we need to explore the tree recursively
                        res = adversary_to_play(nb_objects_given+1, total_weight + new_object, previous_maximal_weight, nb_reachable_packings, new_hash, objects, object_seq, packings, hash_table);
                        if (res) {
                            // Algorithm loses
                            // We add the sub tree res to the current tree
                            tree->children[tree->nb_children] = res;
                            tree->nb_children++;
                            // We add the result of this configuration to the hash table
                            DEBUG_PRINT("Inserting config (algo loses) in hash_table\n");
                            insert_hash_table(new_hash, packings, objects, hash_table, res->next_item);
                            // We remove the item from the bin
                            while(switch_bin<bin) {
                                packings[switch_bin] = packings[switch_bin+1];
                                switch_bin++;
                            }
                            packings[bin] = last_bin_value;
                        } else {
                            // There is a an algorithm that wins
                            // We add the result of this configuration to the hash table
                            DEBUG_PRINT("Inserting config (algo wins) in ht\n");
                            insert_hash_table(new_hash, packings, objects, hash_table, 0);
                            // We remove the item from the bin
                            objects[new_object]--;
                            while(switch_bin<bin) {
                                packings[switch_bin] = packings[switch_bin+1];
                                switch_bin++;
                            }
                            packings[bin] = last_bin_value;
                            // We need to free the tree
                            for (int child=0; child<tree->nb_children; child++) {
                                free_tree(tree->children[child]);
                            }
                            free(tree->children);
                            free(tree);
                            return NULL;
                        }
                    }
                } else {
                    DEBUG_PRINT("Config is adversary-winning according to hash table");
                    // The adversary wins according to the hash_table
                    // We add a special node
                    struct tree_node* child_tree = malloc(sizeof(struct tree_node));
                    child_tree->packings = malloc(sizeof(int) * NB_BINS);
                    for (int bb=0; bb<NB_BINS; bb++) {
                        child_tree->packings[bb] = packings[bb];
                    }
                    child_tree->next_item = hash_table_result;
                    child_tree->nb_children = -1; // tree_nodes with -1 correspond to a node in the hash table
                    child_tree->hash = new_hash;
                    tree->children[tree->nb_children] = child_tree;
                    tree->nb_children++;
                    // We remove the item from the bin
                    while(switch_bin<bin) {
                        packings[switch_bin] = packings[switch_bin+1];
                        switch_bin++;
                    }
                    packings[bin] = last_bin_value;
                }
            }
        }
    }

    // We couldn't find a bin to fit the item without reaching target, we return the tree
    tree->next_item = new_object;
    tree->packings = malloc(sizeof(int) * NB_BINS);
    for (int b=0; b<NB_BINS; b++) {
        tree->packings[b] = packings[b];
    }
    objects[new_object]--;
    return tree;
}

/*
 * Return a tree if the given configuration is winning for the adversary, NULL otherwise.
 * Parameters:
 * - nb_objects_given: numbers of objects already placed in the current configuration
 * - total_weight: total weight of the objects
 * - hash: hash value of the current configuration (we know it's also not in the hash table)
 * - *objects: number of objects for each size that were given
 * - *object_seq: list of objects, used by MULKNAP
 * - *packings: current weight of each bin, size m
 * - *hash_table: hash table containing known configurations
 */
struct tree_node *adversary_to_play(int nb_objects_given,
                        int total_weight,
                        int previous_maximal_weight,
                        int prev_nb_reachable_packings,
                        uint64_t hash,
                        int *objects,
                        int *object_seq,
                        int *packings,
                        struct hash_table_element *hash_table) {
    /* It is here the adversary turn to play. We need to propose an object
    that could fit in the bins with a proper placement - to know the maximum
    size of such an object, we use Pisinger's Mulknap algorithm. We return 1
    if there is an object that is winning for the adversary (i.e. we managed
    to prove the bound target/cap). */
#ifndef NDEBUG
    DEBUG_PRINT("--------------------\n");
    DEBUG_PRINT("ADVTP: nbo: %i tw: %i ph: %lu\n",nb_objects_given, total_weight, hash);
    DEBUG_PRINT("Objects: ");
    print_table(CAP+1, objects);
    DEBUG_PRINT("Obj seq: ");
    print_table(nb_objects_given, object_seq);
    DEBUG_PRINT("packings: ");
    print_table(NB_BINS, packings);
    DEBUG_PRINT("Hash table:\n");
    //print_hash_table(hash_table);
#endif
    int max_value;
    int res;
    NODES_VISITED++;
    if (NODES_VISITED%NODES_BETWEEN_PRINTS == 0) {
        printf("----------------------------------------------------------------------------------\n");
        printf("Nodes visited: %li\n", NODES_VISITED);
        printf("Eliminated: %-10lu (reds %-10lu | greens %-10lu | purples %-10lu)\n",
        SUCCESSFUL_ELIMINATIONS,
        TRIVIAL_ELIMINATIONS,
        TRIVIAL_ADV_WINS,
        SUCCESSFUL_ELIMINATIONS - TRIVIAL_ADV_WINS - TRIVIAL_ELIMINATIONS);
        printf("           +%-10lu (    +%-10lu |       +%-10lu |        +%-10lu)\n",
        SUCCESSFUL_ELIMINATIONS - DELTA_SUCCESSFUL_ELIMINATIONS,
        TRIVIAL_ELIMINATIONS - DELTA_TRIVIAL_ELIMINATIONS,
        TRIVIAL_ADV_WINS - DELTA_TRIVIAL_ADV_WINS,
        SUCCESSFUL_ELIMINATIONS - DELTA_SUCCESSFUL_ELIMINATIONS - TRIVIAL_ELIMINATIONS + DELTA_TRIVIAL_ELIMINATIONS -TRIVIAL_ADV_WINS + DELTA_TRIVIAL_ADV_WINS);
        printf("\n");
        printf("Hash table elements: %-10lu | insertion fails: %-10lu | successful queries: %-10lu\n",
        NUMBER_ELEMENTS_HASHED,
        HASH_FAILS,
        SUCCESSFUL_LOOKUPS);
        printf("                    +%-10lu |                 +%-10lu |                    +%-10lu\n",
        NUMBER_ELEMENTS_HASHED - DELTA_HASHED,
        HASH_FAILS - DELTA_FAILS,
        SUCCESSFUL_LOOKUPS - DELTA_SUCCESSES);
        


        /*printf("Nodes visited: %li, eliminated  %lu (+%lu): %lu (+%lu) reds, %lu (+%lu) greens, %lu (+%lu) purples | hash table has %lu elements (+%lu) (had %lu failed insertions (+%lu), %lu queries (+%lu))\n",
        NODES_VISITED,
        SUCCESSFUL_ELIMINATIONS,
        SUCCESSFUL_ELIMINATIONS - DELTA_SUCCESSFUL_ELIMINATIONS,
        TRIVIAL_ELIMINATIONS,
        TRIVIAL_ELIMINATIONS - DELTA_TRIVIAL_ELIMINATIONS,
        NUMBER_ELEMENTS_HASHED,
        NUMBER_ELEMENTS_HASHED - DELTA_HASHED,
        HASH_FAILS,
        HASH_FAILS - DELTA_FAILS,
        SUCCESSFUL_LOOKUPS,
        SUCCESSFUL_LOOKUPS - DELTA_SUCCESSES); */
        DELTA_FAILS = HASH_FAILS;
        DELTA_HASHED = NUMBER_ELEMENTS_HASHED;
        DELTA_SUCCESSES = SUCCESSFUL_LOOKUPS;
        DELTA_SUCCESSFUL_ELIMINATIONS = SUCCESSFUL_ELIMINATIONS;
        DELTA_TRIVIAL_ELIMINATIONS = TRIVIAL_ELIMINATIONS;
        DELTA_TRIVIAL_ADV_WINS = TRIVIAL_ADV_WINS;
    }
    
    // Now we need to compute the max size of an object we can send, using
    // Pisinger's Mulknap algorithm
    DEBUG_PRINT("SOLVER...");
    // int mknap_res = mulknap(nb_objects_given, NB_BINS-1, object_seq, object_seq, MKNAPSOL, CAPS);
    int last_object;
    int new_nb_reachable_packings=0;

    if (nb_objects_given != 0) {
        last_object = object_seq[nb_objects_given-1];
        int prev_norm = total_weight-last_object;
        res = compute_new_reachable_packings(last_object,
                                                prev_nb_reachable_packings,
                                                prev_norm,
                                                &new_nb_reachable_packings,
                                                BOOL_REACHABLE_PACKINGS[total_weight],
                                                REACHABLE_PACKINGS[prev_norm],
                                                REACHABLE_PACKINGS[total_weight]);
    } else {
        new_nb_reachable_packings = 1;
        res = CAP;
    }
    
    
    DEBUG_PRINT("SOLVER OK\n");
    max_value = res; //CAP - (total_weight - mknap_res);
    /*if (res != max_value) {
        printf("ERROR SOLVER: GOT %i, EXPECTED %i\n", res, max_value);
    }*/

    uint64_t p_index = packings_index(packings);
    int min_send = PACKINGS_LOWER_BOUNDS[p_index];

    if (min_send > max_value) {
        SUCCESSFUL_ELIMINATIONS++;
        return NULL;
    }
    // We can now propose any item with weight less than max_value
    // We iterate over all possibilities
    if (packings[0]>=TARGET - CAP) {
        for (int item = max_value; item>=1; item--) {
        //for (int item = 1; item<=max_value; item++) {
    #ifndef NDEBUG
            DEBUG_PRINT("Proposing object %i from packing:", item);
            print_table(NB_BINS, packings);
            DEBUG_PRINT("of depth %i with items:", nb_objects_given);
            print_table(CAP+1, object_seq);
    #endif
            struct tree_node * res = algorithm_to_play(nb_objects_given, total_weight, item, max_value, new_nb_reachable_packings, hash, objects, object_seq, packings, hash_table);
            if (res) {
                return res;
            }
        }
    } else {
        //for (int item = max_value; item>=1; item--) {
        for (int item = 1; item<=max_value; item++) {
    #ifndef NDEBUG
            DEBUG_PRINT("Proposing object %i from packing:", item);
            print_table(NB_BINS, packings);
            DEBUG_PRINT("of depth %i with items:", nb_objects_given);
            print_table(CAP+1, object_seq);
    #endif
            struct tree_node * res = algorithm_to_play(nb_objects_given, total_weight, item, max_value, new_nb_reachable_packings, hash, objects, object_seq, packings, hash_table);
            if (res) {
                return res;
            }
        }
    }
    return NULL; // there is an algorithm that can fit items under TARGET
}






void iterate_hyperplane(int sum, int index, int prev, int *current_packing, int *nb_points, int **hyperplane_points) {
    if (index == NB_BINS - 1) {
        hyperplane_points[*nb_points] = malloc(sizeof(int) * NB_BINS);
        current_packing[index] = sum;
        for (int bin = 0; bin < NB_BINS; bin++) {
            hyperplane_points[*nb_points][bin] = current_packing[bin];
        }
        *nb_points = *nb_points+1;
    } else {
        int bins_left = NB_BINS - index;
        int i_min = sum / bins_left;
        int max = sum > prev ? prev : sum;
        if (sum % bins_left != 0) {
            i_min++;
        }
        for (int item = i_min; item <= max; item++) {
            current_packing[index] = item;
            iterate_hyperplane(sum - item, index+1, item, current_packing, nb_points, hyperplane_points);
        }
    }
}

void visualize_f_states(int b3, int size, FILE *f, int **f_states) {
    int picture_size = 400;
    float square_size = (float) (picture_size) / size;
    int i_square_size = (int) square_size + 1; 
    int x, y;
    fprintf(f, "<svg width=\"%i\" height=\"%i\"  xmlns=\"http://www.w3.org/2000/svg\">\n", picture_size, picture_size+100);
    for (int b1 = 0; b1<size; b1++) {
        for (int b2 = 0; b2<size; b2++) {
            x = (int) ( b1 * square_size);
            y = (int) (b2 * square_size); 
            fprintf(f, "<rect x=\"%i\" y=\"%i\" width=\"%i\" height=\"%i\" style=\"fill:", x, y, i_square_size, i_square_size);
            if (b1+b2+b3 > CAP * NB_BINS) {
                fprintf(f, "black\"/>\n");
            } else {
                if (f_states[b1][b2]==CAP+1) {
                    // Losing state
                    fprintf(f, "red\"/>\n");
                } else {
                    if (f_states[b1][b2] == -1) {
                        fprintf(f, "rgb(0,155,0)\"/>\n"); // Winning state (not visited)
                    } else {
                        if (f_states[b1][b2] == -2) {
                            fprintf(f, "rgb(0,0,255)\"/>\n"); // Visited state
                        } else {
                            if (f_states[b1][b2] == -3) { // Winning state (visited)
                                fprintf(f, "rgb(255,255,0)\"/>\n");
                            } else {
                                //fprintf(f, "rgb(%i,0,255)\"/>\n", (f_states[b1][b2] * 255) / CAP); // Unvisited state
                                fprintf(f, "white\"/>\n");
                            }
                        }
                    }

                }
            }
        }
    }
    fprintf(f, "<text x=\"0\" y=\"%i\" fill=\"black\">Bins: %i; Bound: %i/%i, b3: %i</text>\n", picture_size+25, NB_BINS, TARGET, CAP, b3);
    fprintf(f, "</svg>");
    fclose(f);
}


void propagate_states() {
    uint64_t nb_states_alg_winning = 0;
    uint64_t nb_feasible_states = 0;
    uint64_t nb_states_adv_winning = 0;
    uint64_t max_nb_packings = NTM[TARGET][NB_BINS];
    DEBUG_PRINT("Max number of packings: %lu\n", max_nb_packings);
    PACKINGS_LOWER_BOUNDS = malloc(sizeof(int) * NTM[TARGET][NB_BINS]);
    int *cp = calloc(NB_BINS, sizeof(int));
    int **hyperplane_points = calloc(max_nb_packings, sizeof(int*));
    int nb_points, big_item, max_item, switch_bin;
    int last_bin_value = -1;
    int smallest_item_needed, biggest_item_needed, propagated_value, res, trivial_winning, nb_zeros;
    uint64_t p_index;
    for (int norm = NB_BINS * CAP; norm>=0; norm--) {
        nb_points = 0;
        iterate_hyperplane(norm, 0, TARGET-1, cp, &nb_points, hyperplane_points);
        nb_feasible_states = nb_feasible_states + nb_points;
        DEBUG_PRINT("Found %i points for hyperplane of norm %i\n", nb_points, norm);
        for (int p = 0; p<nb_points; p++) {
            p_index = packings_index(hyperplane_points[p]);
            if (hyperplane_points[p][NB_BINS-2] >= BMIN) {
                // Geometric elimination, this is not feasible
                PACKINGS_LOWER_BOUNDS[p_index] = CAP + 1;
            } else {
                nb_zeros = 0;
                for (int target_bin = 0; target_bin < NB_BINS; target_bin++) {
                    cp[target_bin] = hyperplane_points[p][target_bin];
                    if (cp[target_bin] == 0) {
                        nb_zeros++;
                    }
                }

                /* Compute the highest weight that can be send in the worst case wether this is trivially adv winning */
                if (cp[NB_BINS-2] + cp[NB_BINS-1] <= CAP) {
                    res = CAP;
                } else {
                    res = CAP - cp[NB_BINS-1];
                }

                big_item = NB_BINS * CAP - norm;
                max_item = big_item > CAP ? CAP : big_item;
                smallest_item_needed = CAP + 1;
                for (int item=1; item<=max_item; item++) {
                    //trivial_winning = (item<=res && cp[0]<=CAP);
                    trivial_winning = 0;
                    last_bin_value = -1;
                    biggest_item_needed = 1;
                    for (int target_bin = 0; target_bin < NB_BINS; target_bin++) {
                        if (cp[target_bin] != last_bin_value) {
                            last_bin_value = cp[target_bin];
                            switch_bin = target_bin - 1;
                            cp[target_bin] = last_bin_value + item;

                            while (switch_bin >= 0 && cp[switch_bin+1]>cp[switch_bin]) {
                                cp[switch_bin+1] = cp[switch_bin];
                                cp[switch_bin] = last_bin_value + item;
                                switch_bin--;
                            }
                            if (last_bin_value + item >= TARGET) {
                                propagated_value = item;
                            } else {
                                if (norm + item > CAP * NB_BINS) {
                                    propagated_value = CAP+1;
                                } else {
                                    propagated_value = PACKINGS_LOWER_BOUNDS[packings_index(cp)];
                                    if (propagated_value != -1) {
                                        trivial_winning = 0;
                                    }
                                    propagated_value = propagated_value > item ? propagated_value : item;
                                }
                            }
                            biggest_item_needed = biggest_item_needed > propagated_value ? biggest_item_needed : propagated_value;
                            
                            switch_bin = switch_bin+2;
                            cp[switch_bin-1] = last_bin_value;
                            while (switch_bin < NB_BINS && cp[switch_bin-1]<cp[switch_bin]) {
                                cp[switch_bin-1] = cp[switch_bin];
                                cp[switch_bin] = last_bin_value;
                                switch_bin++;
                            }
                        }
                    }
                    if (trivial_winning) {
                        smallest_item_needed = -1;
                    }
                    smallest_item_needed = smallest_item_needed < biggest_item_needed ? smallest_item_needed : biggest_item_needed;
                }
                PACKINGS_LOWER_BOUNDS[p_index] = smallest_item_needed;
            }
            if (PACKINGS_LOWER_BOUNDS[p_index] == CAP + 1) {
                nb_states_alg_winning++;
            } else {
                if (PACKINGS_LOWER_BOUNDS[p_index] == -1) {
                    nb_states_adv_winning++;
                }
            }
        }
    }
    printf("---\nPackings statistics: reds: %lu, greens: %lu, covered: %lu out of %lu states (bounded by %lu)\n", nb_states_alg_winning, nb_states_adv_winning, nb_states_alg_winning+nb_states_adv_winning, nb_feasible_states, max_nb_packings);
}

void draw_vis_propag() {
    if (NB_BINS == 3 && VISUALIZE_PROPAG == 1) {
        int ***f_states = malloc(sizeof(int**)*TARGET);
        int *test_packing = malloc(sizeof(int) * NB_BINS);
        for (int b1 = 0; b1<TARGET; b1++) {
            f_states[b1] = malloc(sizeof(int*)*TARGET);
            for (int b2 = 0; b2<TARGET; b2++) {
                f_states[b1][b2] = malloc(sizeof(int)*TARGET);
            }
        }
        for (int b1 = 0; b1<TARGET; b1++) {
            for (int b2 = 0; b2<=b1; b2++) {
                for (int b3 = 0; b3<=b2; b3++) {
                    if (b1+b2+b3 <= NB_BINS*CAP) {
                        test_packing[0] = b1;
                        test_packing[1] = b2;
                        test_packing[2] = b3;
                        f_states[b1][b2][b3] = PACKINGS_LOWER_BOUNDS[packings_index(test_packing)];
                        f_states[b1][b3][b2] = f_states[b1][b2][b3];
                        f_states[b2][b1][b3] = f_states[b1][b2][b3];
                        f_states[b2][b3][b1] = f_states[b1][b2][b3];
                        f_states[b3][b1][b2] = f_states[b1][b2][b3];
                        f_states[b3][b2][b1] = f_states[b1][b2][b3];
                    } else {
                        f_states[b1][b2][b3] = CAP+1;
                        f_states[b1][b3][b2] = f_states[b1][b2][b3];
                        f_states[b2][b1][b3] = f_states[b1][b2][b3];
                        f_states[b2][b3][b1] = f_states[b1][b2][b3];
                        f_states[b3][b1][b2] = f_states[b1][b2][b3];
                        f_states[b3][b2][b1] = f_states[b1][b2][b3];
                    }
                }
            }
        }
        for (int b1 = 0; b1 < TARGET; b1++) {
            char filename[25];
            sprintf(filename, "Propag_Cut%03i.svg", b1);
            FILE *file_test = fopen(filename, "w+");
            visualize_f_states(b1, TARGET, file_test, f_states[b1]);
        }
    } else {
        if (NB_BINS == 2 && VISUALIZE_PROPAG == 1){
            int **f_states = malloc(sizeof(int*)*TARGET);
            int *test_packing = malloc(sizeof(int) * NB_BINS);
            for (int b1 = 0; b1<TARGET; b1++) {
                f_states[b1] = malloc(sizeof(int)*TARGET);
            }
            for (int b1 = 0; b1<TARGET; b1++) {
                for (int b2 = 0; b2<=b1; b2++) {
                    if (b1+b2 <= NB_BINS*CAP) {
                        test_packing[0] = b1;
                        test_packing[1] = b2;
                        f_states[b1][b2] = PACKINGS_LOWER_BOUNDS[packings_index(test_packing)];
                        f_states[b2][b1] = f_states[b1][b2];
                    } else {
                        f_states[b1][b2] = CAP + 1;
                        f_states[b2][b1] = f_states[b1][b2];
                    }
                }
            }
            char filename[25];
            sprintf(filename, "2DPROPAG.svg");
            FILE *file_test = fopen(filename, "w+");
            visualize_f_states(0, TARGET, file_test, f_states);
        }
    }
}

void init_NTM() {
    NTM = malloc(sizeof(uint64_t *) * (TARGET+1));

    NTM[0] = malloc(sizeof(uint64_t) * (NB_BINS+1));
    for (int bin = 0; bin <= NB_BINS; bin++) {
        NTM[0][bin] = 0;
    }

    for (int tar = 1; tar <= TARGET; tar++) {
        NTM[tar] = malloc(sizeof(uint64_t) * (NB_BINS+1));
        NTM[tar][0] = 0;
        NTM[tar][1] = (uint64_t) tar;
        for (int bin = 2; bin <= NB_BINS; bin++) {
            NTM[tar][bin] = NTM[tar-1][bin] + NTM[tar][bin-1];
        }
    }
}

void init_algo(int m, int c, int t) {
    NB_BINS = m;
    CAP = c;
    TARGET = t;
    BMIN = compute_forbidden_orthant(m, c, t);
    CAPS = malloc(sizeof(int) * m);
    for (int b = 0; b<m; b++) {
        CAPS[b] = c;
    }
    int max_objects = c*m;
    BEST_DEPTH_REACHED = max_objects + 1;
    BEST_NORM_REACHED = max_objects + 1;
    HASHED_VALUE = malloc(sizeof(int) * NB_BINS * (CAP * NB_BINS + 1));
    NODES_VISITED = 0;
    DEBUG_PRINT("Computing NTM table\n");
    init_NTM();
    DEBUG_PRINT("Propagating packings minimum weight\n");
    propagate_states();
    init_solver();
}



int print_proof_tree_rec(
                        int *cpt, 
                        int *instance, 
                        FILE *f,
                        struct tree_node *tree,
                        struct hash_table_element *hash_table) {
    int node_index = *cpt;
    int child_name;
    uint64_t p_indx = packings_index(tree->packings);
    int colr = PACKINGS_LOWER_BOUNDS[p_indx];
    fprintf(f, "n%09i [label=\"bins: [%i", node_index, tree->packings[0]);
    for (int i=1; i<NB_BINS; i++) {
        fprintf(f, ", %i", tree->packings[i]);
    }

    if (colr == -1 || colr == -3) { // Packing is green (ADV-WINNING)
        fprintf(f, "]\\nADV-WINNING PACKING\"];\n");
    } else {
        if (tree->next_item == -2) { // Configuration was already seen in the DAG
            fprintf(f, "]\\nMemoized value\"];\n");
        } else { // New configuration
            fprintf(f, "]\\nNext weight: %i\"];\n", tree->next_item);
        }
    }
    *cpt = *cpt + 1;
    if (VISUALIZE_PROPAG==1 && DRAW_PROPAG_BEFORE==0) {
        
        if (colr == -1 || colr == -3) { // Packing is adv-winning and we visited it -> Special color
            PACKINGS_LOWER_BOUNDS[p_indx] = -3;
        } else {
            PACKINGS_LOWER_BOUNDS[p_indx] = -2;
        }
    }
    if (tree->nb_children == -1) {
        // The current tree has no children because it is in the hash_table.
        // We simply follow the hash table (since we didnt delete anything from it)
        int next_item = tree->next_item;
        int last_bin_value = -1;
        int new_bin_value;
        int hash_table_result;
        int switch_bin;
        int *packings = malloc(sizeof(int) * NB_BINS);
        for (int b = 0; b<NB_BINS; b++) {
            packings[b] = tree->packings[b];
        }
        uint64_t previous_hash = tree->hash;
        uint64_t new_hash;
        int h_table_res = hash_table_check(previous_hash, packings, instance, hash_table);
        if (h_table_res == -1) {
            printf("ERROR: COULDN'T FIND NODE IN HASH TABLE\n");
            uint64_t real_key = previous_hash%HASH_TABLE_SIZE;
            for (int i=0; i<PROBING_LENGTH; i++) {
                if (!hash_table[real_key+i].bin_config) {
                    printf("EMPTY CELL N%i\n", i);
                }
                if (hash_table[real_key+i].key == previous_hash) {
                    printf("MATCHING KEY CELL N%i\n", i);
                    if (same_config(packings, instance, hash_table[real_key+i].bin_config, hash_table[real_key+i].instance)==1) {
                        printf("MATCHING CONFIG ???\n");
                    } else {
                        printf("NOT MATCHING CONFIG\n");
                        printf("CONFIG FOUND:\nPACKING: ");
                        print_table(NB_BINS, hash_table[real_key+i].bin_config);
                        printf("OBJECTS: ");
                        print_table((CAP+1), hash_table[real_key+i].instance);
                    }
                }
            }
            // We couldn't find the configuration in the hash_table
            return -1;
        }
        if (h_table_res == -2) { // We have already visited this configuration in the proof_tree, no need to explore further
            return node_index;
        }
        change_hash_table_value(previous_hash, packings, instance, hash_table, -2);
        previous_hash ^= ZOBRIST_INSTANCES[next_item][instance[next_item]];
        previous_hash ^= ZOBRIST_INSTANCES[next_item][instance[next_item] + 1];
        instance[next_item] = instance[next_item] + 1;
        for (int bin=0; bin<NB_BINS; bin++) {
            if (packings[bin]+next_item<TARGET) {
                // We can fit the object in this bin without reaching TARGET
                if (packings[bin] != last_bin_value) {
                    // We avoided trivial symmetries
                    // We add the item to the bin
                    last_bin_value = packings[bin];
                    new_bin_value = packings[bin]+next_item;
                    // The new hash value is the previous one XOR some stuff
                    new_hash = previous_hash;
                    // We want to keep packings in decreasing order, so we have to switch the order of some bins
                    switch_bin = bin-1;
                    packings[bin] = new_bin_value;
                    while (switch_bin>=0 && packings[switch_bin]<new_bin_value){
                        new_hash ^= ZOBRIST_LOADS[switch_bin][packings[switch_bin]];
                        packings[switch_bin+1] = packings[switch_bin];
                        packings[switch_bin] = new_bin_value;
                        new_hash ^= ZOBRIST_LOADS[switch_bin+1][packings[switch_bin+1]];
                        switch_bin--;
                    }
                    switch_bin++;
                    new_hash ^= ZOBRIST_LOADS[switch_bin][new_bin_value];
                    new_hash ^= ZOBRIST_LOADS[bin][last_bin_value];

                    // We can now check if we stored this configuration in the hash table
                    hash_table_result = hash_table_check(new_hash, packings, instance, hash_table);
                    if (hash_table_result==-1) {
                        // This is not always an error as you may end up on a green packing
                        // We verify that this is the case
                        int new_p_id = packings_index(packings);
                        if (PACKINGS_LOWER_BOUNDS[new_p_id] != -1 && PACKINGS_LOWER_BOUNDS[new_p_id] != -3) {
                            printf("Error: Couldn't follow tree in hash table\n");
                        } else {
                            fprintf(f, "n%09i [label=\"bins: [%i", *cpt, packings[0]);
                            for (int i=1; i<NB_BINS; i++) {
                                fprintf(f, ", %i", packings[i]);
                            }
                            fprintf(f, "]\\nADV-WINNING PACKING\"];\n");
                            fprintf(f, "n%09i -> n%09i;\n", node_index, *cpt);
                            *cpt = *cpt + 1;
                        }
                        
                    }
                    else {
                        struct tree_node *child_tree = malloc(sizeof(struct tree_node));
                        child_tree->nb_children = -1;
                        child_tree -> packings = packings;
                        child_tree->next_item = hash_table_result;
                        child_tree->hash = new_hash;
                        child_name = print_proof_tree_rec(cpt, instance, f, child_tree, hash_table);
                        fprintf(f, "n%09i -> n%09i;\n", node_index, child_name);
                        //free_tree(child_tree);
                    }
                    // We remove the item from the bin
                    while(switch_bin<bin) {
                        packings[switch_bin] = packings[switch_bin+1];
                        switch_bin++;
                    }
                    packings[bin] = last_bin_value;
                }
            }
        }
        instance[next_item] = instance[next_item] - 1;
        return node_index;
    } else {
        instance[tree->next_item] = instance[tree->next_item] + 1;
        for (int child_index = 0; child_index<tree->nb_children; child_index++) {
            child_name = print_proof_tree_rec(cpt, instance, f, tree->children[child_index], hash_table);
            fprintf(f, "n%09i -> n%09i;\n", node_index, child_name);
        }
        instance[tree->next_item] = instance[tree->next_item] - 1;
        return node_index;
    }
}


void write_proof_tree_graph(struct tree_node *tree, struct hash_table_element *hash_table) {
    char filename[35];
    char command[120];
    int *instance = calloc(CAP+1, sizeof(int));
    printf("---\nRecovering full tree proof from hash table...\n");
    sprintf(filename, "Proof_%i_%i_%i.dot", NB_BINS, CAP, TARGET);
    FILE *f = fopen(filename, "w+");
    fprintf(f, "digraph {\n");
    int cpt = 0;
    print_proof_tree_rec(&cpt, instance, f, tree, hash_table);
    fprintf(f, "}");
    fclose(f);
    printf("Tree proof recovered !\n");
    printf("---\nNumber of nodes in the tree proof: %i\n", cpt);
    if (DRAW_GRAPH) {
        printf("Converting the proof into PDF...\n");
        sprintf(command, "dot -Tpdf Proof_%i_%i_%i.dot > Proof_%i_%i_%i.pdf", NB_BINS, CAP, TARGET, NB_BINS, CAP, TARGET);
        system(command);
        printf("PDF written!\n");
    }
    
}


void compute_bound_feasibility() {
    int m, c, t;
    int *objects;
    int *object_sequence;
    int *packings;
    if (NB_BINS == 0) {
        printf("Number of bins:\\");
        scanf("%d", &m);
        printf("Capacity of each bin:\\");
        scanf("%d", &c); 
        printf("Target:\\");
        scanf("%d", &t);
    } else {
        m = NB_BINS;
        c = CAP;
        t = TARGET;
    }
    DEBUG_PRINT("Initializing algorithm\n");
    init_algo(m, c, t);
    DEBUG_PRINT("Initialized!\n");
    if (DRAW_PROPAG_BEFORE == 1) {
        draw_vis_propag();
    }
    struct hash_table_element* hash_table = calloc(HASH_TABLE_SIZE+PROBING_LENGTH, sizeof(struct hash_table_element));
    ZOBRIST_LOADS = zobrist_hash_init_loads();
    ZOBRIST_INSTANCES = zobrist_hash_init_instances();
    int max_objects = c*m;
    objects = calloc(CAP+1, sizeof(int));
    packings = malloc(sizeof(int) * m);
    object_sequence = malloc(sizeof(int) * max_objects);
    for (int i=0; i<m; i++) {
        packings[i] = 0;
    }
    uint64_t starting_hash = 0;
    for (int b=0; b<NB_BINS; b++) {
        starting_hash^= ZOBRIST_LOADS[b][0];
    }
    for (int i=0; i<=CAP; i++) {
        starting_hash^= ZOBRIST_INSTANCES[i][0];
    }
    struct tree_node * tree = adversary_to_play(0, 0, CAP, 0, starting_hash, objects, object_sequence, packings, hash_table);
    if (tree) {
        printf("\n   --------------------------------------\n");
        printf("~~~| Bound %3i/%3i with %2i bins found ! |~~~\n", TARGET, CAP, NB_BINS);
        printf("   --------------------------------------\n\n");
        if (PRINT_TREE_TERMINAL == 1) {
            print_tree(tree);
        } else {
            printf("Option to print the tree in terminal disabled.\n");
        }
        if (WRITE_GRAPH) {
            write_proof_tree_graph(tree, hash_table);
        }
        free_tree(tree);
    } else {
        printf("Can't prove the bound %i/%i with %i bins\n", TARGET, CAP, NB_BINS);
    }
    if (DRAW_PROPAG_BEFORE == 0) {
        draw_vis_propag();
    }
    printf("\n---------- Final statistics ----------\n\n");
        printf("Nodes visited: %li\n", NODES_VISITED);
        printf("Eliminated: %-10lu (reds %-10lu | greens %-10lu | purples %-10lu)\n",
        SUCCESSFUL_ELIMINATIONS,
        TRIVIAL_ELIMINATIONS,
        TRIVIAL_ADV_WINS,
        SUCCESSFUL_ELIMINATIONS - TRIVIAL_ADV_WINS - TRIVIAL_ELIMINATIONS);
        printf("\n");
        printf("Hash table elements: %-10lu | insertion fails: %-10lu | successful queries: %-10lu\n",
        NUMBER_ELEMENTS_HASHED,
        HASH_FAILS,
        SUCCESSFUL_LOOKUPS);
    printf("\n--------------------------------------\n");
    free(CAPS);
    free(objects);
    free(packings);
}

int main(int argc, char *argv[]) 
{   
    if (argc <= 1) {
        printf("Try -h to see possible options\n");
    }
    for (int arg = 1; arg<argc; arg++) {
        if (strcmp(argv[arg], "-h") == 0) {
            printf("--- Bound finder for online bin stretching ---\n");
            printf("Options:\n");
            printf("-h to see options\n");
            printf("-w to write the proof as a .dot file\n");
            printf("-g to write the proof as a .dot file and to convert it into a pdf file (may take a while on large graphs)\n");
            printf("-p m g t to set problems parameters, such as '-p 3 14 19' where:\n -- m corresponds to the number of bins\n -- g corresponds to the capacity of each bin\n -- t corresponds to the targeted value\n");
            printf("-draw to draw the .svg files representing packings for 2 or 3 bins\n");
            printf("-t to draw the packings that were visited on the visualisations (2 or 3 bins only)\n");
            
            return 1;
        }
        if (strcmp(argv[arg], "-g") == 0) {
            DRAW_GRAPH = 1;
            WRITE_GRAPH = 1;
            printf("- Option draw graph enabled (.dot and .pdf)\n");
        }
        if (strcmp(argv[arg], "-w") == 0) {
            WRITE_GRAPH = 1;
            printf("- Option print graph enabled (.dot file)\n");
        }
        if (strcmp(argv[arg], "-t") == 0) {
            DRAW_PROPAG_BEFORE = 0;
            printf("- Option see visited packings enabled\n");
        }
        if (strcmp(argv[arg], "-draw") == 0) {
            VISUALIZE_PROPAG = 1;
            printf("- Option draw .svg visualisation enabled\n");
        }
        if (strcmp(argv[arg], "-p") == 0) {
            if (arg+3<argc) {
                char *endPtr;
                NB_BINS = strtol(argv[arg+1], &endPtr, 10);
                CAP = strtol(argv[arg+2], &endPtr, 10);
                TARGET = strtol(argv[arg+3], &endPtr, 10);
                if (NB_BINS <=2) {
                    printf("Number of bins should be bigger than 2!\n");
                }
                if (CAP <= 0) {
                    printf("Capacity should be at least 1!\n");
                    return 1;
                }
                if (TARGET <= CAP) {
                    printf("Targeted value should be bigger than the capacity!\n");
                    return 1;
                }
                arg = arg + 3;
            } else {
                printf("Option -p requires 3 numbers!\n");
            }
        }

    }
    compute_bound_feasibility();
    return 1;
    
}
