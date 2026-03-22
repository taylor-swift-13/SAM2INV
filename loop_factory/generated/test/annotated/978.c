int main1(){
  int s, y, gc, lr;
  s=(1%20)+20;
  y=s;
  gc=5;
  lr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (lr == 0) ==> (gc == 5);
  loop invariant y == s;
  loop invariant s == 21;
  loop invariant (gc + 2) % 7 == 0;
  loop invariant gc >= 2*lr + 5;
  loop invariant lr >= 0;
  loop invariant lr <= s;
  loop invariant (gc % 2) == 1;
  loop assigns lr, gc;
*/
while (lr<=s-1) {
      gc++;
      lr = lr + 1;
      gc += gc;
      if (lr<s+3) {
          gc = gc + y;
      }
      else {
          gc = gc + 3;
      }
      if ((y%5)==0) {
          gc = gc + y;
      }
  }
}