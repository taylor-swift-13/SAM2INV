int main1(int d,int f){
  int xq, ckf, qv7c, ov9;

  xq=f+11;
  ckf=0;
  qv7c=3;
  ov9=0;

  while (ckf<xq) {
      ov9 = ckf%5;
      if (ckf>=qv7c) {
          qv7c = (ckf-qv7c)%5;
          qv7c = qv7c+ov9-qv7c;
      }
      else {
          qv7c += ov9;
      }
      d = d + xq;
      ckf += 1;
  }

}
