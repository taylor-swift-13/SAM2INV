int main1(){
  int v, fu, b;
  v=30;
  fu=0;
  b=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 20 * fu;
  loop invariant fu <= v;
  loop invariant 0 <= fu;
  loop invariant v == 30;
  loop assigns fu, b;
*/
while (fu<v) {
      fu = fu + 1;
      b = b + 16;
      b += 4;
  }
}