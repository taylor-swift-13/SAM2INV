int main1(){
  int cnx, v, w6ad, o8v, rhcd;

  cnx=1;
  v=cnx+5;
  w6ad=(1%40)+2;
  o8v=0;
  rhcd=v;

  while (w6ad!=o8v) {
      o8v = w6ad;
      w6ad = (w6ad+cnx/w6ad)/2;
      rhcd += w6ad;
      rhcd += v;
  }

}
