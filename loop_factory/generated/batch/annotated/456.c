int main1(int a,int q){
  int e, t, v;

  e=a;
  t=3;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == a;
  loop invariant q == \at(q, Pre);
  loop invariant v == 0 || v >= 2;
  loop invariant v == 0 || v == 3;
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= v <= 3;
  loop invariant v >= 0;

  loop assigns v;
*/
while (1) {
      v = v+2;
      if (e<a+3) {
          v = v-v;
      }
  }

}
