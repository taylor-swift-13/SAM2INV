int main1(int u){
  int md, z2, nb, dcq1, dxx;

  md=u*2;
  z2=0;
  nb=1;
  dcq1=1;
  dxx=md;

  while (1) {
      if (!(nb<=md)) {
          break;
      }
      z2++;
      dcq1 += 2;
      nb = nb + dcq1;
      dxx = dxx+z2+z2;
  }

}
