int main1(int j){
  int kjv, f, k5m, iq;

  kjv=0;
  f=0;
  k5m=0;
  iq=(j%18)+5;

  while (iq>0) {
      iq = iq - 1;
      kjv = kjv+j*j;
      f = f+j*j;
      k5m = k5m+j*j;
      j = j+(k5m%9);
  }

}
