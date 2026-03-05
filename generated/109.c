int main109(int y,int b,int l){
  int shk, kj, z4nq, u, o5p, oq;

  shk=l+22;
  kj=2;
  z4nq=-5;
  u=3;
  o5p=(l%6)+2;
  oq=-3;

  while (u<=shk-1) {
      z4nq = z4nq*o5p;
      u = u + 1;
      kj = kj*o5p+4;
      y++;
      o5p = o5p*4+(z4nq%6)+2;
      oq = oq*4+(z4nq%3)+3;
  }

}
