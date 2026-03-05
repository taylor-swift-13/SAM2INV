int main1(){
  int wjs, cy, uu, tm7q;

  wjs=11;
  cy=0;
  uu=0;
  tm7q=1;

  while (uu>0&&tm7q<=wjs) {
      if (uu>tm7q) {
          uu = uu - tm7q;
      }
      else {
          uu = 0;
      }
      uu = uu + 1;
      tm7q = tm7q + 1;
      cy++;
  }

}
