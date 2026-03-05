int main1(){
  int j6ro, hh, e, gb;
  j6ro=(1%23)+13;
  hh=0;
  e=0;
  gb=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= e;
  loop invariant e <= 1;
  loop invariant gb == hh + 1;
  loop invariant hh >= 0;
  loop invariant hh <= j6ro;
  loop assigns e, gb, hh;
*/
for (; e>0&&gb<=j6ro; hh++) {
      if (e>gb) {
          e = e - gb;
      }
      else {
          e = 0;
      }
      e += 1;
      gb = gb + 1;
  }
}