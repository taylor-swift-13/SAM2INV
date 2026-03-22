int main1(int a){
  int an, zl, o3, zx, wk, oe, o3v, jk, h, xl, dr;

  an=59;
  zl=2;
  o3=0;
  zx=a*4;
  wk=zl;
  oe=an;
  o3v=13;
  jk=1;
  h=0;
  xl=an;
  dr=zl;

  while (o3<=an-1) {
      o3 += 2;
      if (wk<=zx) {
          zx = wk;
      }
      if (o3v+3<an) {
          o3v++;
      }
      jk = jk + 3;
      oe += o3v;
      dr += o3;
      jk = jk + a;
      o3v += wk;
      h = h + a;
      jk += zl;
      if (an<xl+2) {
          o3v = o3v + jk;
      }
  }

}
