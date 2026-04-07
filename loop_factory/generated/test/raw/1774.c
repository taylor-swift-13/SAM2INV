int main1(int m){
  int ug, ie, igd, g7;

  ug=(m%15)+20;
  ie=0;
  igd=-4;
  g7=0;

  while (ie < ug) {
      g7 = g7 * (ie + 1) + m;
      igd += 1;
      ie = ug;
  }

}
