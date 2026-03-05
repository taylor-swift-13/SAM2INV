int main131(int o,int n,int c){
  int u77, fo, mxd, ckf, rdq, i;

  u77=(n%23)+9;
  fo=u77;
  mxd=(n%40)+2;
  ckf=0;
  rdq=fo;
  i=-4;

  while (1) {
      if (!(mxd!=ckf)) {
          break;
      }
      ckf = mxd;
      mxd = (mxd+u77/mxd)/2;
      o = o+ckf-ckf;
      rdq = rdq+(ckf%4);
      i = i/3;
      rdq = rdq*3;
  }

}
