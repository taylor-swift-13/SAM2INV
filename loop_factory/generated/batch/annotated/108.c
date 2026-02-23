int main1(int q){
  int b, i, r;

  b=54;
  i=0;
  r=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant i <= b;
  loop invariant b == 54;
  loop invariant q == \at(q, Pre);
  loop invariant i % 5 == 0;
  loop invariant 0 <= i;
  loop assigns i;
*/
while (i+5<=b) {
      i = i+5;
  }

}
