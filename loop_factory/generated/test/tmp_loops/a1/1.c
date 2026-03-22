int main1(int j,int y){
  int vr, u, jkc, hu, ap, rr, i, d;

  vr=j-7;
  u=0;
  jkc=1;
  hu=1;
  ap=1;
  rr=1;
  i=vr;
  d=u;

  while (ap<=vr) {
      jkc = jkc*(j/ap);
      if ((ap/2)%2==0) {
          rr = 1;
      }
      else {
          rr = -1;
      }
      hu = hu+rr*jkc;
      ap += 1;
      jkc = jkc*(j/ap);
      if (hu*hu<=vr+4) {
          j = j*2;
      }
      y = y + 3;
      d = d+jkc+ap;
      i += d;
      d += j;
  }

}
