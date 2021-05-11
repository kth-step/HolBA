
int addOne(int x) {
  return x + 1;
}

int addTwo(int x) {
  return x + 2;
}

int comp(int (*f)(int), int (*g)(int), int x) {
  return (*f) ((*g) (x));
}

int addThree(int x) {
  return comp(&addOne, &addTwo, x);
}
