mtype = { IDLE, COMPUTING, SYNCING, WAITING, DONE };

#define NUM_GPUS 4
#define GRADIENT_SIZE 10
#define MAX_ITERATIONS 5

typedef GPUState {
    mtype state;
    int weights[GRADIENT_SIZE];
    int gradients[GRADIENT_SIZE];
    int buffer[GRADIENT_SIZE];
    int syncCounter;
}

GPUState gpus[NUM_GPUS];

chan gradientChannels[NUM_GPUS] = [NUM_GPUS] of { int, int, int };
chan weightChannels[NUM_GPUS] = [NUM_GPUS] of { int };
chan ackChannels[NUM_GPUS] = [NUM_GPUS] of { int };

int globalSyncStep = 0;
int completedGPUs = 0;
int iteration = 0;

init {
    int i, j;
    for (i : 0 .. NUM_GPUS-1) {
        gpus[i].state = IDLE;
        gpus[i].syncCounter = 0;
        for (j : 0 .. GRADIENT_SIZE-1) {
            gpus[i].weights[j] = 10;
            gpus[i].gradients[j] = 0;
            gpus[i].buffer[j] = 0;
        }
    }
    
    run GPU(0);
    run GPU(1);
    run GPU(2);
    run GPU(3);
}

proctype GPU(int id) {
    int other, i, gradVal, ackVal, recvGrad;
    int acksReceived = 0;
    
gpu_loop:
    do
    :: (iteration >= MAX_ITERATIONS) -> 
        gpus[id].state = DONE;
        goto done_state
    :: (gpus[id].state == IDLE && iteration < MAX_ITERATIONS) ->
        gpus[id].state = COMPUTING;
        
        for (i : 0 .. GRADIENT_SIZE-1) {
            if
            :: (gpus[id].weights[i] > 0) ->
                gpus[id].gradients[i] = gpus[id].weights[i] - 1
            :: else ->
                gpus[id].gradients[i] = 0
            fi
        }
        
        gpus[id].state = SYNCING;
        acksReceived = 0;
        
        for (other : 0 .. NUM_GPUS-1) {
            if
            :: (other != id) ->
                for (i : 0 .. GRADIENT_SIZE-1) {
                    gradVal = gpus[id].gradients[i];
                    assert(gradVal >= 0);
                    gradientChannels[other]!id,i,gradVal
                }
                ackChannels[id]?ackVal;
                assert(ackVal == other);
                acksReceived = acksReceived + 1
            :: else ->
                skip
            fi
        }
        
        assert(acksReceived == NUM_GPUS - 1);
        
        for (i : 0 .. GRADIENT_SIZE-1) {
            if
            :: (gpus[id].buffer[i] > 0) ->
                gpus[id].weights[i] = gpus[id].weights[i] - (gpus[id].buffer[i] / NUM_GPUS);
                if
                :: (gpus[id].weights[i] < 0) ->
                    gpus[id].weights[i] = 0
                :: else ->
                    skip
                fi
            :: else ->
                skip
            fi;
            gpus[id].buffer[i] = 0
        }
        
        gpus[id].state = WAITING;
        
        atomic {
            completedGPUs = completedGPUs + 1;
            if
            :: (completedGPUs == NUM_GPUS) ->
                globalSyncStep = globalSyncStep + 1;
                iteration = iteration + 1;
                completedGPUs = 0;
                
                for (other : 0 .. NUM_GPUS-1) {
                    gpus[other].state = IDLE;
                    gpus[other].syncCounter = 0
                }
            :: else ->
                skip
            fi
        }
    
    :: (gpus[id].state == SYNCING) ->
        if
        :: nempty(gradientChannels[id]) ->
            gradientChannels[id]?other,i,recvGrad;
            assert(other >= 0 && other < NUM_GPUS);
            assert(i >= 0 && i < GRADIENT_SIZE);
            assert(recvGrad >= 0);
            
            gpus[id].buffer[i] = gpus[id].buffer[i] + recvGrad;
            ackChannels[other]!id
        :: else ->
            skip
        fi
    
    :: (gpus[id].state == WAITING) ->
        skip
    od;

done_state:
    skip
}

ltl no_message_loss {
    [](
        (len(gradientChannels[0]) > 0 || 
         len(gradientChannels[1]) > 0 ||
         len(gradientChannels[2]) > 0 ||
         len(gradientChannels[3]) > 0)
        -> <>(
            len(gradientChannels[0]) == 0 && 
            len(gradientChannels[1]) == 0 &&
            len(gradientChannels[2]) == 0 &&
            len(gradientChannels[3]) == 0
        )
    )
}

ltl eventual_sync {
    <>(iteration == MAX_ITERATIONS)
}

ltl mutual_consistency {
    [](
        (gpus[0].syncCounter == gpus[1].syncCounter) &&
        (gpus[1].syncCounter == gpus[2].syncCounter) &&
        (gpus[2].syncCounter == gpus[3].syncCounter)
    )
}

ltl no_deadlock {
    [](
        (gpus[0].state != DONE || 
         gpus[1].state != DONE ||
         gpus[2].state != DONE ||
         gpus[3].state != DONE)
        -> <>(
            gpus[0].state == COMPUTING ||
            gpus[1].state == COMPUTING ||
            gpus[2].state == COMPUTING ||
            gpus[3].state == COMPUTING
        )
    )
}

ltl fifo_ordering {
    []<>(
        (len(gradientChannels[0]) == 0) &&
        (len(gradientChannels[1]) == 0) &&
        (len(gradientChannels[2]) == 0) &&
        (len(gradientChannels[3]) == 0)
    )
}
