int main1(int k){
  int p, b2, z, q, xfz;

  p=40;
  b2=p;
  z=0;
  q=2;
  xfz=0;

  while (1) {
      if (!(b2<p)) {
          break;
      }
      q += 1;
      xfz += 1;
      if (q>=9) {
          q = q - 9;
          z += 1;
      }
      b2++;
  }

}
