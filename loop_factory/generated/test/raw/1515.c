int main1(int n,int i){
  int blj, exb, vd8, k, q7w, vf8, u, zf;

  blj=i;
  exb=0;
  vd8=blj;
  k=blj;
  q7w=exb;
  vf8=i;
  u=n;
  zf=exb;

  while (1) {
      if (!(exb<=blj-1)) {
          break;
      }
      if (!(!(exb<blj/2))) {
          vd8++;
      }
      else {
          vd8 = vd8 + k;
      }
      if (q7w+4<blj) {
          q7w = q7w + u;
      }
      i += vd8;
      vf8 += vd8;
      zf += vd8;
      n += 1;
      q7w += vf8;
      u = u + exb;
      exb = blj;
      if ((exb%8)==0) {
          zf += vf8;
      }
  }

}
