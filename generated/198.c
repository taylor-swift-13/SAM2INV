int main198(int w,int o){
  int mj2, yz, jc, nq, mnj, cn, g9z4;

  mj2=o;
  yz=0;
  jc=0;
  nq=0;
  mnj=7;
  cn=16;
  g9z4=yz;

  while (1) {
      if (!(jc<mj2&&mnj>0)) {
          break;
      }
      jc++;
      nq = nq + mnj;
      g9z4 += 2;
      cn = cn+(nq%8);
      mnj -= 1;
      w = w+(nq%7);
  }

}
