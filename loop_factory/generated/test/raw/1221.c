int main1(){
  int zn, hp8, e3q, ns7u, zz92, z;

  zn=(1%16)+12;
  hp8=0;
  e3q=0;
  ns7u=1;
  zz92=6;
  z=0;

  while (z<=zn) {
      z += 1;
      e3q = e3q + ns7u;
      ns7u = ns7u + zz92;
      zz92 += 6;
      ns7u = ns7u*ns7u;
      e3q += hp8;
  }

}
