int main1(int p,int q){
  int i, f, n;

  i=(q%7)+14;
  f=0;
  n=p;

  while (f<i) {
      n = n*2;
      n = n*n;
      f = f+1;
  }

}
