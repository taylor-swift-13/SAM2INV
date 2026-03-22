int main1(int o,int p){
  int mhr, ssqh, sc3, bey;
  mhr=o;
  ssqh=0;
  sc3=1;
  bey=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ssqh >= 0;
  loop invariant sc3 == (ssqh + 1) * (ssqh + 1);
  loop invariant bey == 2*ssqh + 1;
  loop invariant o >= \at(o, Pre);
  loop invariant o <= \at(o, Pre) + 5 * ssqh;
  loop invariant mhr == \at(o,Pre);
  loop assigns ssqh, bey, sc3, o;
*/
while (1) {
      if (!(sc3<=mhr)) {
          break;
      }
      ssqh = ssqh + 1;
      bey += 2;
      sc3 += bey;
      o = o+(sc3%6);
  }
}