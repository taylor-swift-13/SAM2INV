int main1(){
  int q, gg, qxmf, d, t;

  q=(1%6)+4;
  gg=1;
  qxmf=0;
  d=0;
  t=0;

  while (1) {
      if (!(gg<q)) {
          break;
      }
      d++;
      t += 1;
      if (d>=8) {
          d -= 8;
          qxmf = qxmf + 1;
      }
      gg += 1;
  }

}
