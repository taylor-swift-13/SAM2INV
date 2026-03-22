int main1(){
  int gz, bw, yl, nu, g, d, s2;

  gz=1-7;
  bw=gz+7;
  yl=0;
  nu=1;
  g=6;
  d=0;
  s2=gz;

  while (d<=gz) {
      d++;
      yl = yl + nu;
      nu = nu + g;
      s2 = s2 + bw;
      g += 6;
  }

}
