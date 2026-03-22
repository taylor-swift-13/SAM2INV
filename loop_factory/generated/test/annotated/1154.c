int main1(){
  int cnx, v, w6ad, o8v, rhcd;
  cnx=1;
  v=cnx+5;
  w6ad=(1%40)+2;
  o8v=0;
  rhcd=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rhcd >= o8v + v;
  loop invariant w6ad >= 1;
  loop invariant cnx == 1;
  loop invariant v == 6;
  loop invariant w6ad <= 3;
  loop invariant 0 <= o8v <= 3;
  loop assigns o8v, w6ad, rhcd;
*/
while (w6ad!=o8v) {
      o8v = w6ad;
      w6ad = (w6ad+cnx/w6ad)/2;
      rhcd += w6ad;
      rhcd += v;
  }
}