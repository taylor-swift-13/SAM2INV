int main1(){
  int aky, bn, a, d2, w;
  aky=1+3;
  bn=0;
  a=aky;
  d2=-8;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (bn == 0) || (bn == 5);
  loop invariant aky == 1 + 3;
  loop assigns bn;
*/
for (; bn<aky; bn = bn + 5) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn % 5 == 0;
  loop invariant w == 0;
  loop invariant aky == 1 + 3;
  loop invariant d2 <= w - a;
  loop invariant a >= 0;
  loop assigns a, bn, d2;
*/
while (a<w) {
      a++;
      bn = bn + a;
      d2 = w-a;
  }
}