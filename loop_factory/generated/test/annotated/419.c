int main1(){
  int wu, y, oy, y1m, il, meo;
  wu=1;
  y=wu;
  oy=9;
  y1m=0;
  il=1;
  meo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == il;
  loop invariant oy + y1m == 9;
  loop invariant 0 <= oy;
  loop invariant 0 <= y1m;
  loop invariant 1 <= il <= 10;
  loop invariant meo <= oy;
  loop invariant meo <= il;
  loop invariant y <= wu;
  loop assigns il, meo, oy, y, y1m;
*/
while (oy>0&&y<wu) {
      if (oy<=il) {
          meo = oy;
      }
      else {
          meo = il;
      }
      il = il + 1;
      oy = oy - meo;
      y++;
      y1m = y1m + meo;
  }
}