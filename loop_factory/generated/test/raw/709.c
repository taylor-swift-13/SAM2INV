int main1(){
  int bsf, vv, de1, lw, cj, bu, vx;

  bsf=1+21;
  vv=0;
  de1=6;
  lw=0;
  cj=bsf;
  bu=(1%35)+8;
  vx=vv;

  while (bu>0) {
      de1 = de1+lw*lw;
      cj = cj+bu*bu;
      lw = lw+bu*bu;
      bu = bu - 1;
      vx = vx + cj;
  }

}
