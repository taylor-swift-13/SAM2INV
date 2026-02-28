int main1(int b,int p){
  int f, n, v, c;

  f=p;
  n=3;
  v=b;
  c=-1;

  while (1) {
      if (n>=f) {
          break;
      }
      v = v+2;
      n = n+1;
      v = v+2;
      c = c+3;
      v = v+n;
  }

}
