/* 
 * We use the following data structure to represent the tree giving a bound
 */
struct tree_node {
    int nb_children; /* Number of children */
    int *packings; /* Current packing of bins */
    int next_item; /* Next item proposed */
    uint64_t hash; /* Hash of this node */
    struct tree_node **children;
};

/*
 * We keep track of what configurations we explored in a hash table containing the
 * following structure
 */
struct hash_table_element {
    uint64_t key; // Key of the element in the hash table (to deal with collisions)
    int *bin_config; // Bin configuration
    int *instance; // Items given
    int winning; // 0 if the config is winning for the algorithm, next item otherwise
};


struct tree_node *algorithm_to_play(int nb_objects_given,
                        int total_weight,
                        int new_object,
                        int previous_maximal_weight,
                        int nb_reachable_packings,
                        uint64_t previous_hash,
                        int *objects,
                        int *object_seq,
                        int *packings,
                        struct hash_table_element *hash_table);


struct tree_node *adversary_to_play(int nb_objects_given,
                        int total_weight,
                        int previous_maximal_weight,
                        int prev_nb_reachable_packings,
                        uint64_t hash,
                        int *objects,
                        int *object_seq,
                        int *packings,
                        struct hash_table_element *hash_table);
