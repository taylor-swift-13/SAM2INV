int main1(int d){
  int r13k, km, tn1l, xfcm, f, s7s;

  r13k=d-2;
  km=0;
  tn1l=8;
  xfcm=0;
  f=r13k;
  s7s=km;

  while (km<r13k) {
      xfcm = xfcm + tn1l;
      s7s += xfcm;
      km = r13k;
  }

  while (f<=s7s-1) {
      tn1l += xfcm;
      xfcm = xfcm + tn1l;
      f = s7s;
  }

}
