int main1(int m,int n){
  int j, k, t, c;

  j=n;
  k=0;
  t=2;
  c=-2;

  while (t!=0&&c!=0) {
      if (t>c) {
          t = t-c;
      }
      else {
          c = c-t;
      }
      t = t*2;
  }

}
