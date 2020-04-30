#include <stdio.h>
#include <stdlib.h>

#define N 5

struct node {
  int data;
  struct node *next;
};

int main() {

  struct node *list, *current;
  int i;
  int r;

  // list initialization
  list = (struct node *)malloc(sizeof(struct node));
  current = list;
  for(i = 0; i < N - 1; i++) {
    current->next = (struct node *)malloc(sizeof(struct node));
    current = current->next;
  }
  current->next = NULL;

  // map
  current = list;
  while(current != NULL) {
    current->data = current->data * current->data;
    current = current->next;
  }

  current = list;
  while(current != NULL) {
    printf("%d\n", current->data);
    current = current->next;
  }

}
