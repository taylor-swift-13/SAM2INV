int main1(){
  int b, i, x, oy1, jg, p;
  b=15;
  i=0;
  x=i;
  oy1=0;
  jg=0;
  p=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i;
  loop invariant i <= b;
  loop invariant jg == i;
  loop invariant (i == 0) ==> (p == 1 && oy1 == 0 && jg == 0);
  loop invariant x == 0;
  loop invariant oy1 == 0;
  loop invariant (i == 0 && p == 1) || (i > 0 && p == 0);
  loop assigns i, jg, oy1, p;
*/
while (1) {
      if (!(i < b)) {
          break;
      }
      p = p * x;
      jg = (1)+(i);
      i = i + 1;
      oy1 = oy1 + jg * p;
  }
}