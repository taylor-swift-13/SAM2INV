int main1(){
  int l7k, fy, qcp, u, zl;

  l7k=(1%9)+19;
  fy=0;
  qcp=1;
  u=l7k;
  zl=7;

  while (1) {
      if (!(fy < l7k)) {
          break;
      }
      fy++;
      qcp = qcp * u;
      u += qcp;
      zl = zl + 3;
  }

}
