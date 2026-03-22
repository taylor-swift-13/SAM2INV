int main1(int r){
  int dw5u, cn, y0z, hs, r3, j3;

  dw5u=r;
  cn=-3;
  y0z=0;
  hs=0;
  r3=r;
  j3=dw5u;

  while (1) {
      if (r3>dw5u) {
          break;
      }
      cn = cn + y0z;
      y0z = (hs)+(y0z);
      r3 = r3 + 1;
      hs += 4;
      j3 = j3+(hs%4);
  }

}
