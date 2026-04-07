int main1(){
  int yuf, y, f;
  yuf=1;
  y=(1%20)+10;
  f=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y + f + yuf == 21;
  loop invariant y >= 0;
  loop invariant f >= 0;
  loop invariant yuf >= 1;
  loop assigns y, f, yuf;
*/
for (; y>0&&f>0; yuf++) {
      if (!(!(yuf%2==0))) {
          y -= 1;
      }
      else {
          f--;
      }
  }
}