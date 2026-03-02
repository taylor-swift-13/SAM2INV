int main1(int b,int p){
  int f, q, r;

  f=b;
  q=3;
  r=-4;

  while (1) {
      r = r+2;
      if ((q%4)==0) {
          r = r+r;
      }
      r = r+r;
  }

}
