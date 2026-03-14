int main1(int k,int p){
  int xw, s4, qo3d, m;

  xw=p-7;
  s4=xw;
  qo3d=xw;
  m=0;

  while (s4-3>=0) {
      m = m+qo3d*s4;
      s4 += 1;
  }

  while (xw<s4) {
      qo3d = qo3d + k;
      xw += 1;
  }

}
