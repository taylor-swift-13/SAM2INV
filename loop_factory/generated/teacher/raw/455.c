int main1(int k,int q){
  int h, j, t;

  h=64;
  j=0;
  t=h;

  while (1) {
      t = t+2;
      if ((j%8)==0) {
          t = t+j;
      }
      t = t+1;
  }

}
