int main1(){
  int c, re8s, dy;
  c=(1%20)+5;
  re8s=(1%20)+5;
  dy=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == dy;
  loop invariant 0 <= c;
  loop invariant c <= 6;
  loop invariant re8s >= 6;
  loop assigns c, dy, re8s;
*/
while (c>=1) {
      if (re8s>0) {
          if (dy>0) {
              c--;
              re8s = re8s - 1;
              dy = dy - 1;
          }
      }
      re8s += 1;
  }
/*@
  assert !(c>=1) &&
         (c == dy);
*/

}