int main1(int d){
  int ua, cj, lf, ogh, f6qk, k4;

  ua=d;
  cj=ua;
  lf=ua;
  ogh=cj;
  f6qk=-3;
  k4=(d%35)+8;

  while (k4>0) {
      f6qk = f6qk+k4*k4;
      lf = (ogh*ogh)+(lf);
      ogh = ogh+k4*k4;
      k4--;
      d = d+(k4%6);
  }

}
