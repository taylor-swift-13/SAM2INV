int main1(int m){
  int d, jn, nu, ar, dd;

  d=m;
  jn=0;
  nu=0;
  ar=0;
  dd=1;

  while (jn < d) {
      ar += dd;
      dd += 2;
      jn = jn + 1;
      nu = nu+(dd%3);
  }

}
