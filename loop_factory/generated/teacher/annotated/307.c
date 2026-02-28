int main1(int p,int q){
  int t, g, v;

  t=q;
  g=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(q, Pre);
  loop invariant g == 0;
  loop invariant v % 2 == 0;
  loop invariant p == \at(p, Pre);
  loop invariant v >= 0;
  loop invariant t == q;
  loop invariant q == \at(q,Pre);
  loop invariant 0 <= v <= 2;
  loop invariant (v == 2) || (v == 0);
  loop invariant g % 3 != 0 ==> (v % 4 == 2);

  loop invariant v == 2 || v == 0;
  loop assigns v;
*/
while (g+5<=t) {
      v = v+4;
      if ((g%3)==0) {
          v = v-v;
      }
  }

}
