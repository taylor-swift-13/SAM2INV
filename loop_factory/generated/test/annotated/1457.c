int main1(){
  int zh7, duv, odn7, w;
  zh7=1;
  duv=0;
  odn7=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant odn7 == duv;
  loop invariant duv <= zh7;
  loop invariant 0 <= odn7;
  loop invariant w == 0;
  loop assigns duv, odn7, w;
*/
while (1) {
      if (!(duv < zh7)) {
          break;
      }
      duv += 1;
      odn7 = odn7+(duv>=zh7-1);
      w = (w+(duv>=zh7)+(-(1)));
  }
}