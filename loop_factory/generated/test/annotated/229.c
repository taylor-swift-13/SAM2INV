int main1(){
  int mb1, me1r, b4y, ty, nj7, kw72;
  mb1=1+3;
  me1r=0;
  b4y=0;
  ty=0;
  nj7=mb1;
  kw72=mb1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ty == b4y;
  loop invariant nj7 >= mb1;
  loop invariant (ty == 0) || (nj7 % 3 == 0);
  loop invariant nj7 >= 0;
  loop invariant 0 <= ty <= mb1;
  loop assigns ty, b4y, nj7;
*/
while (ty<=mb1-1) {
      ty = ty + 1;
      b4y++;
      nj7 = nj7 + b4y;
      nj7 = nj7*3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kw72 == mb1;
  loop invariant nj7 >= kw72;
  loop invariant b4y >= mb1;
  loop invariant me1r >= 0;
  loop invariant b4y >= 0;
  loop assigns b4y, me1r, nj7;
*/
while (nj7>kw72) {
      if (nj7%2==0) {
          b4y += mb1;
      }
      else {
          b4y = b4y+mb1+1;
      }
      me1r = me1r + b4y;
      nj7 = kw72;
  }
}