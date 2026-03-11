int main(int n) {
  if (n < 0) n = 0;
  int i = 0, j;
  int budget = n * (n + 1);
  
  while (i < n) {
    
    for (j = 0; j < i; ++j) {
      budget -= 2;
    }
    budget -= 2;
    i++;
  }
  /*@ assert budget == 0 && budget % 2 == 0; */
  return budget;
}
