int main1(int b,int g){
  int hx, z, e, u, mzj, eum, pnp;

  hx=b;
  z=hx;
  e=-1;
  u=6;
  mzj=z;
  eum=(b%6)+2;
  pnp=z;

  while (1) {
      if (!(mzj<hx)) {
          break;
      }
      e = e*eum+b;
      mzj++;
      u = u*eum;
      eum = eum + 3;
      g = g*3+(mzj%6)+2;
      pnp += 2;
      b = b*4+(u%6)+3;
  }

}
