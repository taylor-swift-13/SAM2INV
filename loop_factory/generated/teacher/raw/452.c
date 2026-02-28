int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=-2;

  while (1) {
      if (n<c+4) {
          c = c+c;
      }
      c = c-c;
      c = c+1;
      v = v+1;
  }

}
