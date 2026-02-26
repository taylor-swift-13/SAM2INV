int main1(int b,int m){
  int z, t, v;

  z=(b%20)+10;
  t=z+6;
  v=4;

  while (t-z>0) {
      v = v*v;
      v = v%5;
      if ((t%4)==0) {
          v = v*2;
      }
      t = t-3;
  }

}
