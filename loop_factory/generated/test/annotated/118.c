int main1(int x,int u){
  int dw, mo, aw, j7;
  dw=u+14;
  mo=0;
  aw=2;
  j7=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j7 - aw == 4;
  loop invariant dw == \at(u,Pre) + 14;
  loop invariant j7 == 6 + 4*mo;
  loop invariant u == \at(u, Pre);
  loop invariant x == \at(x, Pre);
  loop invariant 0 <= mo;
  loop assigns aw, j7, mo;
*/
while (mo<dw) {
      j7 += 4;
      mo++;
      aw += 4;
  }
}