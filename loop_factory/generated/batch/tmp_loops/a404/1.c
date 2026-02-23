int main1(int m,int n){
  int l, t, x;

  l=m;
  t=0;
  x=n;

  while (t<=l-1) {
      if (x+3<l) {
          x = x%4;
      }
      t = t+1;
  }

}
