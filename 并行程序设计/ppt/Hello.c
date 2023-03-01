#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

/*全局变量*/
int thread_count;

/*线程运行的函数*/
void* Hello(void* rank);

int main(int argc, char* argv[]){
    long thread; /*为了适应64位系统*/
    pthread_t* thread_handles;

    /*从命令行获得线程数量*/
    thread_count = strtol(argv[1],NULL,10);

    thread_handles = malloc(thread_count*sizeof(pthread_t));

    for(thread = 0; thread < thread_count; thread++)
        pthread_create(&thread_handles[thread],NULL,Hello, (void*) thread);

    printf("Hello from the main thread\n");

    for(thread = 0; thread < thread_count; thread++)
        pthread_join(thread_handles[thread], NULL);

    free(thread_handles);
    return 0;
}
void* Hello(void* rank) {
    long my_rank = (long) rank
    printf("Hello from thread %ld of %d\n", my_rank, thread_count);
    return NULL;
}
