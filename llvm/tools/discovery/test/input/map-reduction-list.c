#include <stdio.h>
#include <stdlib.h>

#define N 5

struct node {
  int data;
  struct node *next;
};

void initialize_list(struct node **list, int size) {
  int i;
  struct node * current;
  current = (struct node *) malloc(sizeof(struct node));
  *list = current;
  for (i = 0; i < size - 1; i++) {
    current->next = (struct node *) malloc(sizeof(struct node));
    current = current->next;
  }
  current->next = NULL;
}

int main(int argc, char *argv[]) {
  struct node *in_list, *out_list, *in_current, *out_current;
  int r;
  initialize_list(&in_list, N);
  initialize_list(&out_list, N);
  in_current = in_list;
  out_current = out_list;
  while(in_current != NULL) {
    out_current->data = in_current->data * in_current->data;
    in_current = in_current->next;
    out_current = out_current->next;
  }
  out_current = out_list;
  r = 0;
  while(out_current != NULL) {
    r = r + out_current->data;
    out_current = out_current->next;
  }
  return r;
}
