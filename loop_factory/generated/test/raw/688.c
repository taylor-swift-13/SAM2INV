int main1(){
  int ua3, l3f, ukf, e4dn;

  ua3=1*3;
  l3f=(1%40)+2;
  ukf=0;
  e4dn=-6;

  while (1) {
      if (!(l3f!=ukf)) {
          break;
      }
      ukf = l3f;
      l3f = (l3f+ua3/l3f)/2;
      e4dn = e4dn + l3f;
  }

}
