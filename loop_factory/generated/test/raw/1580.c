int main1(){
  int u0f, ah, c4q, lfd0, hivv, z, lzf, sq, yk, hz;

  u0f=1*3;
  ah=0;
  c4q=u0f;
  lfd0=0;
  hivv=ah;
  z=1;
  lzf=ah;
  sq=ah;
  yk=0;
  hz=0;

  while (ah+1<=u0f) {
      lfd0 -= 4;
      c4q += 4;
      if (c4q<yk+4) {
          z += 4;
      }
      if (lzf<hivv+3) {
          lzf += 1;
      }
      hz += lfd0;
      hivv += 4;
      z = z + hivv;
      lzf = (z)+(lzf);
      if (z+4<u0f) {
          sq = sq + hivv;
      }
      else {
          yk = yk + ah;
      }
      u0f = (ah+1)-1;
  }

}
