int main1(int c,int u){
  int db2, j, aoej, r, h8, y;
  db2=28;
  j=db2;
  aoej=1;
  r=0;
  h8=3;
  y=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (aoej - 1) * (aoej - 1);
  loop invariant j == 28;
  loop invariant db2 == 28;
  loop invariant h8 == 3;
  loop invariant aoej <= db2 + 1;
  loop assigns r, aoej, h8;
*/
while (aoej<=db2) {
      r = r+2*aoej-1;
      h8 = h8+db2-j;
      aoej++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 28;
  loop invariant j % 4 == 0;
  loop invariant db2 == 28;
  loop assigns h8, j, c;
*/
while (1) {
      if (!(j<y)) {
          break;
      }
      h8 = (y)+(-(j));
      j += 4;
      c += j;
  }
}