int main1(int b,int p){
  int c, v, m;

  c=(p%6)+10;
  v=1;
  m=v;

  while (v<=c/3) {
      if (v+6<=p+c) {
          m = m*2;
      }
      v = v*3;
  }

}
