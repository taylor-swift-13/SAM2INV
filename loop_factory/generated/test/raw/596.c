int main1(int u,int q){
  int vots, w, ooe;

  vots=1;
  w=(q%20)+10;
  ooe=(q%15)+8;

  while (1) {
      if (!(w>0&&ooe>0)) {
          break;
      }
      if (!(!(vots%2==0))) {
          w = w - 1;
      }
      else {
          ooe = ooe - 1;
      }
      vots++;
  }

}
