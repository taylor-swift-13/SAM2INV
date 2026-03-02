int main1(int n,int p){
  int e, k, a;

  e=(p%28)+12;
  k=1;
  a=k;

  while (1) {
      a = a+4;
      if (a+5<e) {
          a = a-a;
      }
  }

}
