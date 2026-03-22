int main1(int v,int f){
  int rb, o0c, un, pfw, yq, r1, cn, jfj;

  rb=f;
  o0c=0;
  un=25;
  pfw=12;
  yq=0;
  r1=o0c;
  cn=12;
  jfj=3;

  while (o0c < rb) {
      o0c = o0c + 1;
      un = (v + f + o0c) % rb;
      if ((un == 0)) {
          pfw = pfw + 1;
      }
      if ((un % 2 == 0)) {
          r1++;
      }
      else {
          jfj += 1;
      }
      v += jfj;
      yq += jfj;
      cn = cn + 3;
      cn += v;
  }

}
