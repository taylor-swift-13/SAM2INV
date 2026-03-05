int main167(int a,int j){
  int dfsj, mi1, ni, xv9u, eg, qc8, tg0;

  dfsj=j-2;
  mi1=dfsj;
  ni=j;
  xv9u=mi1;
  eg=j;
  qc8=mi1;
  tg0=-4;

  while (1) {
      if (!(mi1>=5)) {
          break;
      }
      ni = ni + mi1;
      xv9u = xv9u*xv9u;
      eg = eg+ni*xv9u;
      tg0 = tg0%8;
      tg0 = qc8*qc8;
      mi1 = mi1 - 5;
  }

}
