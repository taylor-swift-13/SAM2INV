int main1(){
  int y, i, l, mo, e8, dnba;
  y=1+9;
  i=y+5;
  l=0;
  mo=0;
  e8=7;
  dnba=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dnba == i*(mo+1);
  loop invariant l == mo;
  loop invariant e8 >= 7;
  loop invariant 0 <= mo;
  loop invariant mo <= y;
  loop invariant i >= y;
  loop assigns e8, dnba, mo, l;
*/
while (mo<=y-1) {
      e8 = e8*4;
      dnba = dnba + i;
      mo++;
      l = l + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= y;
  loop invariant e8 >= 7;
  loop invariant l >= 0;
  loop assigns e8, i;
*/
while (1) {
      if (!(y+1<=i)) {
          break;
      }
      if (y%2==0) {
          e8 += l;
      }
      else {
          e8 = e8+l+1;
      }
      i = (y+1)-1;
  }
}