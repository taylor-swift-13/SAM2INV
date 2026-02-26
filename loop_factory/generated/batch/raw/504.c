int main1(int a,int q){
  int c, j, t, e;

  c=20;
  j=0;
  t=3;
  e=q;

  while (1) {
      if (j>=c) {
          break;
      }
      t = t+3;
      j = j+1;
      t = t+1;
      e = e-1;
      if ((j%5)==0) {
          e = e+1;
      }
  }

}
