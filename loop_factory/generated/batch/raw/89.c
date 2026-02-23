int main1(int k,int q){
  int h, j, t;

  h=64;
  j=h;
  t=-5;

  while (j>0) {
      if ((j%4)==0) {
          t = t+t;
      }
      j = j-1;
  }

}
