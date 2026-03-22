int main1(int x,int r){
  int fs, rpq, iwdt, eas, eoba, fv, a234, q, rlk;

  fs=77;
  rpq=0;
  iwdt=2;
  eas=2;
  eoba=0;
  fv=4;
  a234=0;
  q=rpq;
  rlk=-5;

  while (1) {
      if (!(rpq<fs)) {
          break;
      }
      if (!(!(rpq%3==0))) {
          if (iwdt>0) {
              iwdt = iwdt - 1;
              eoba += 1;
          }
      }
      else {
          if (iwdt<fv) {
              iwdt += 1;
              eas++;
          }
      }
      fv = fv + eoba;
      rpq = rpq + 1;
      a234++;
      fv += 4;
      rlk = rlk + 3;
      q = q+(rpq%2);
      x = x+(rpq%2);
  }

}
