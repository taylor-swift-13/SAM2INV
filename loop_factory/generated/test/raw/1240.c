int main1(int g){
  int fa, q, kgx6, eu6, z, bw;

  fa=g+9;
  q=g;
  kgx6=16;
  eu6=g;
  z=(g%6)+2;
  bw=fa;

  while (eu6<fa) {
      eu6 += 1;
      kgx6 = kgx6*z;
      q = q*z+1;
      bw = bw+(q%8);
      z += 2;
      z = z*z+z;
  }

}
