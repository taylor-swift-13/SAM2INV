int main1(){
  int t7, x, o8, r1o;
  t7=1-8;
  x=0;
  o8=0;
  r1o=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r1o == 0;
  loop invariant o8 == 0;
  loop invariant x >= 0;
  loop invariant (t7 == x - 1) || ((t7 == 1 - 8) && (x == 0));
  loop assigns x, t7, o8;
*/
while (x++ < t7) {
      o8 += r1o;
      t7 = x++;
  }
}