int main1(int p,int r){
  int i, ikm, xb, u;

  i=32;
  ikm=i;
  xb=0;
  u=1;

  while (xb>0&&u<=i) {
      if (xb>u) {
          xb = xb - u;
      }
      else {
          xb = 0;
      }
      xb += 1;
      u = u + 1;
      ikm = ikm + 1;
  }

}
