int main1(int a){
  int jbcs, gtwt, m4v9, ov, as, hfi, lxt;

  jbcs=a+7;
  gtwt=0;
  m4v9=(a%20)+10;
  ov=(a%15)+8;
  as=a;
  hfi=6;
  lxt=gtwt;

  while (1) {
      if (!(m4v9>0&&ov>0)) {
          break;
      }
      if (gtwt%2==0) {
          m4v9--;
      }
      else {
          ov -= 1;
      }
      gtwt++;
      if (!(!(hfi+6<jbcs))) {
          hfi += gtwt;
      }
      a++;
      as += 2;
      lxt = lxt+(gtwt%2);
      as += 1;
      hfi += as;
  }

}
