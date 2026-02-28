int main1(int q){
  int p, e, t, v;

  p=q;
  e=0;
  t=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == q;
  loop invariant ((p >= 0) ==> (t <= p)) && ((p < 0) ==> (t <= 0));
  loop invariant t == p || t % 5 == 0;

  loop invariant q == \at(q, Pre);

  loop invariant ((t == p) || (t % 5 == 0)) && (q == \at(q, Pre));
  loop invariant p == \at(q, Pre);
  loop invariant (t == p) || (t == 0) || (0 <= t && t % 5 == 0 && t <= p);
  loop assigns t;
*/
while (1) {
      if (t+5<=p) {
          t = t+5;
      }
      else {
          t = p;
      }
  }

}
